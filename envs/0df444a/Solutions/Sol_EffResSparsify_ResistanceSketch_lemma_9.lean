-- Prove2me | solution 1 for EffResSparsify.ResistanceSketch.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T07:35:19.950328+00:00
-- url     : https://prove2.me/submissions/b0e5210e-0653-48db-9084-513e7200db33

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P813d17a4

open HarmonicGames.Decomposition
open EffResSparsify.ResistanceSketch
open Matrix
open scoped InnerProductSpace

section Pinv
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

lemma sub_proj_mem_ker (L : V →ₗ[ℝ] W) (x : V) :
    x - (LinearMap.ker L)ᗮ.starProjection x ∈ LinearMap.ker L := by
  have := (LinearMap.ker L)ᗮ.sub_starProjection_mem_orthogonal x
  rwa [Submodule.orthogonal_orthogonal] at this

lemma map_proj (L : V →ₗ[ℝ] W) (x : V) :
    L ((LinearMap.ker L)ᗮ.starProjection x) = L x := by
  have h1 := sub_proj_mem_ker L x
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1.symm

lemma pinv_apply_self (L : V →ₗ[ℝ] W) (x : V) :
    pinv L (L x) = (LinearMap.ker L)ᗮ.starProjection x := by
  set K := (LinearMap.ker L)ᗮ with hK
  set f := L ∘ₗ K.subtype with hf
  set y : K := K.orthogonalProjectionOnto x with hy
  have hk : L x = f y := by
    rw [← map_proj L x, Submodule.starProjection_apply]; rfl
  have hr : (LinearMap.range f).orthogonalProjectionOnto (f y) =
      ⟨f y, LinearMap.mem_range_self f y⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨f y, LinearMap.mem_range_self f y⟩
  have he : (LinearEquiv.ofInjective f (pinv_restrict_injective L)).symm
      ⟨f y, LinearMap.mem_range_self f y⟩ = y := by
    rw [LinearEquiv.symm_apply_eq]; ext; simp
  unfold pinv
  rw [hk]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [hr]
  have := congrArg K.subtype he
  exact this.trans (by rw [Submodule.starProjection_apply]; rfl)

lemma map_pinv (L : V →ₗ[ℝ] W) (x : V) : L (pinv L (L x)) = L x := by
  rw [pinv_apply_self, map_proj]

lemma map_pinv_of_mem (L : V →ₗ[ℝ] W) (y : W) (hy : y ∈ LinearMap.range L) :
    L (pinv L y) = y := by
  obtain ⟨x, rfl⟩ := hy
  exact map_pinv L x

end Pinv

section Graph
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma incidence_mulVec (G : WGraph V E) (x : V → ℝ) (e : E) :
    (G.incidence *ᵥ x) e = x (G.head e) - x (G.tail e) := by
  simp only [WGraph.incidence, mulVec, dotProduct]
  rw [Fintype.sum_eq_add (G.head e) (G.tail e) (G.head_ne_tail e)]
  · simp [(G.head_ne_tail e).symm]
    ring
  · intro c hc
    simp [hc.1, hc.2]

lemma dot_lap (G : WGraph V E) (y x : V → ℝ) :
    y ⬝ᵥ (G.laplacian *ᵥ x) =
      ∑ e, G.w e * ((y (G.head e) - y (G.tail e)) * (x (G.head e) - x (G.tail e))) := by
  unfold WGraph.laplacian WGraph.weightMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal, incidence_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma quad_nonneg (G : WGraph V E) (x : V → ℝ) : 0 ≤ x ⬝ᵥ (G.laplacian *ᵥ x) := by
  rw [dot_lap]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (G.w_pos e).le (mul_self_nonneg _)

lemma edge_eq_of_ker (G : WGraph V E) (x : V → ℝ) (hx : G.laplacian *ᵥ x = 0) (e : E) :
    x (G.head e) = x (G.tail e) := by
  have h0 : ∑ e, G.w e * ((x (G.head e) - x (G.tail e)) * (x (G.head e) - x (G.tail e))) = 0 := by
    rw [← dot_lap, hx, dotProduct_zero]
  have hnn : ∀ e ∈ (Finset.univ : Finset E),
      0 ≤ G.w e * ((x (G.head e) - x (G.tail e)) * (x (G.head e) - x (G.tail e))) :=
    fun e _ => mul_nonneg (G.w_pos e).le (mul_self_nonneg _)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 e (Finset.mem_univ e)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (G.w_pos e).ne'
  · have := mul_self_eq_zero.1 h; linarith

lemma const_of_ker (G : WGraph V E) (hconn : G.IsConnected) (x : V → ℝ)
    (hx : G.laplacian *ᵥ x = 0) (u v : V) : x u = x v := by
  obtain ⟨p⟩ := hconn.preconnected u v
  induction p with
  | nil => rfl
  | cons hadj p ih =>
    simp only [WGraph.toSimpleGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨_, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩ := hadj
    · exact (edge_eq_of_ker G x hx e).trans ih
    · exact (edge_eq_of_ker G x hx e).symm.trans ih

lemma lap_herm (G : WGraph V E) : G.laplacian.IsHermitian := by
  unfold Matrix.IsHermitian WGraph.laplacian WGraph.weightMatrix
  rw [conjTranspose_eq_transpose_of_trivial]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma dot_chi (z : V → ℝ) (u v : V) :
    z ⬝ᵥ (WGraph.chi u - WGraph.chi v) = z u - z v := by
  simp [WGraph.chi, dotProduct_sub, dotProduct_single]

lemma lap_pinv_spec (G : WGraph V E) (hconn : G.IsConnected) (u v : V) :
    G.laplacian *ᵥ (G.lapPinv *ᵥ (WGraph.chi u - WGraph.chi v)) =
      WGraph.chi u - WGraph.chi v := by
  set b : V → ℝ := WGraph.chi u - WGraph.chi v with hb
  set f := Matrix.toEuclideanLin G.laplacian with hf
  have hsym : f.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 (lap_herm G)
  have hrange : (LinearMap.ker f)ᗮ = LinearMap.range f := by
    rw [← hsym.orthogonal_range, Submodule.orthogonal_orthogonal]
  have hmem : (WithLp.toLp 2 b : EuclideanSpace ℝ V) ∈ LinearMap.range f := by
    rw [← hrange, Submodule.mem_orthogonal]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    have hz' : G.laplacian *ᵥ (WithLp.ofLp z) = 0 := by
      have := congrArg WithLp.ofLp hz
      exact this
    have hc := const_of_ker G hconn (WithLp.ofLp z) hz' u v
    rw [PiLp.inner_apply]
    have : ∑ i, ⟪(z i : ℝ), (WithLp.toLp 2 b : EuclideanSpace ℝ V) i⟫_ℝ =
        (WithLp.ofLp z) ⬝ᵥ b := by
      simp only [dotProduct, Real.inner_apply]
    rw [this, hb, dot_chi, hc, sub_self]
  have h1 : Matrix.toEuclideanLin G.lapPinv = pinv f := by
    unfold WGraph.lapPinv
    exact LinearEquiv.apply_symm_apply _ _
  have h2 : G.laplacian *ᵥ (G.lapPinv *ᵥ b) =
      WithLp.ofLp (f (pinv f (WithLp.toLp 2 b))) := by
    rw [← h1]; rfl
  rw [h2, map_pinv_of_mem f _ hmem]

lemma cs_lap (G : WGraph V E) (y x : V → ℝ) :
    (y ⬝ᵥ (G.laplacian *ᵥ x)) ^ 2 ≤
      (y ⬝ᵥ (G.laplacian *ᵥ y)) * (x ⬝ᵥ (G.laplacian *ᵥ x)) := by
  rw [dot_lap, dot_lap, dot_lap]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun e => Real.sqrt (G.w e) * (y (G.head e) - y (G.tail e)))
    (fun e => Real.sqrt (G.w e) * (x (G.head e) - x (G.tail e)))
  have hw : ∀ e, Real.sqrt (G.w e) * Real.sqrt (G.w e) = G.w e :=
    fun e => Real.mul_self_sqrt (G.w_pos e).le
  have e1 : ∀ e, Real.sqrt (G.w e) * (y (G.head e) - y (G.tail e)) *
      (Real.sqrt (G.w e) * (x (G.head e) - x (G.tail e))) =
      G.w e * ((y (G.head e) - y (G.tail e)) * (x (G.head e) - x (G.tail e))) := fun e => by
    linear_combination ((y (G.head e) - y (G.tail e)) * (x (G.head e) - x (G.tail e))) * hw e
  have e2 : ∀ e, (Real.sqrt (G.w e) * (y (G.head e) - y (G.tail e))) ^ 2 =
      G.w e * ((y (G.head e) - y (G.tail e)) * (y (G.head e) - y (G.tail e))) := fun e => by
    linear_combination ((y (G.head e) - y (G.tail e)) * (y (G.head e) - y (G.tail e))) * hw e
  have e3 : ∀ e, (Real.sqrt (G.w e) * (x (G.head e) - x (G.tail e))) ^ 2 =
      G.w e * ((x (G.head e) - x (G.tail e)) * (x (G.head e) - x (G.tail e))) := fun e => by
    linear_combination ((x (G.head e) - x (G.tail e)) * (x (G.head e) - x (G.tail e))) * hw e
  simp only [e1, e2, e3] at h
  exact h

/-- `R = xᵀ L x` for `x = L⁺ b`. -/
lemma R_eq_quad (G : WGraph V E) (hconn : G.IsConnected) (u v : V) :
    G.R u v = (G.lapPinv *ᵥ (WGraph.chi u - WGraph.chi v)) ⬝ᵥ
      (G.laplacian *ᵥ (G.lapPinv *ᵥ (WGraph.chi u - WGraph.chi v))) := by
  rw [lap_pinv_spec G hconn u v, dotProduct_comm]
  rfl

lemma R_nonneg (G : WGraph V E) (hconn : G.IsConnected) (u v : V) : 0 ≤ G.R u v := by
  rw [R_eq_quad G hconn]; exact quad_nonneg G _

/-- `w_e R_e ≤ 1`. -/
lemma w_mul_R_le (G : WGraph V E) (hconn : G.IsConnected) (e : E) :
    G.w e * G.R (G.head e) (G.tail e) ≤ 1 := by
  set x := G.lapPinv *ᵥ (WGraph.chi (G.head e) - WGraph.chi (G.tail e)) with hx
  have hR : G.R (G.head e) (G.tail e) = x (G.head e) - x (G.tail e) := by
    show (WGraph.chi (G.head e) - WGraph.chi (G.tail e)) ⬝ᵥ x = _
    rw [dotProduct_comm, dot_chi]
  have hQ := R_eq_quad G hconn (G.head e) (G.tail e)
  rw [← hx, dot_lap] at hQ
  have hle : G.w e * ((x (G.head e) - x (G.tail e)) * (x (G.head e) - x (G.tail e))) ≤
      ∑ f, G.w f * ((x (G.head f) - x (G.tail f)) * (x (G.head f) - x (G.tail f))) :=
    Finset.single_le_sum (f := fun f => G.w f * ((x (G.head f) - x (G.tail f)) *
      (x (G.head f) - x (G.tail f))))
      (fun f _ => mul_nonneg (G.w_pos f).le (mul_self_nonneg _)) (Finset.mem_univ e)
  rw [← hQ, ← hR] at hle
  have hR0 := R_nonneg G hconn (G.head e) (G.tail e)
  have hw := G.w_pos e
  nlinarith

lemma card_E_le (G : WGraph V E) (hsimple : G.IsSimple) :
    (Fintype.card E : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have hinj : Function.Injective (fun e => (G.head e, G.tail e)) := by
    intro e e' h
    simp only [Prod.mk.injEq] at h
    apply hsimple
    rw [h.1, h.2]
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_prod] at this
  have : ((Fintype.card E : ℕ) : ℝ) ≤ ((Fintype.card V * Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at this
  nlinarith

lemma mulVec_chi {k : ℕ} (Z : Matrix (Fin k) V ℝ) (u v : V) (i : Fin k) :
    (Z *ᵥ (WGraph.chi u - WGraph.chi v)) i = Z i u - Z i v := by
  show Z i ⬝ᵥ (WGraph.chi u - WGraph.chi v) = _
  exact dot_chi _ u v

end Graph

lemma norm_sq_toLp {k : ℕ} (a : Fin k → ℝ) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin k))‖ ^ 2 = sqNorm a := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [sqNorm, Real.norm_eq_abs, sq_abs]

/-- The final real-number step. -/
lemma final_ineq (R ε nA nT nD : ℝ) (hR : 0 ≤ R) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hA : 0 ≤ nA) (hT : 0 ≤ nT) (hD : 0 ≤ nD)
    (h1 : (1 - ε) * R ≤ nA ^ 2) (h2 : nA ^ 2 ≤ (1 + ε) * R)
    (h3 : nD ^ 2 ≤ 2 * ε ^ 2 * (1 - ε) / 9 * R)
    (h4 : nT ≤ nA + nD) (h5 : nA ≤ nT + nD) :
    (1 - ε) ^ 2 * R ≤ nT ^ 2 ∧ nT ^ 2 ≤ (1 + ε) ^ 2 * R := by
  set s := Real.sqrt R with hs
  set q := Real.sqrt (1 - ε) with hq
  set p := Real.sqrt (1 + ε) with hp
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hss : s ^ 2 = R := Real.sq_sqrt hR
  have hqq : q ^ 2 = 1 - ε := Real.sq_sqrt (by linarith)
  have hpp : p ^ 2 = 1 + ε := Real.sq_sqrt (by linarith)
  -- nA ≥ q s
  have hAlo : q * s ≤ nA := by
    have : (q * s) ^ 2 ≤ nA ^ 2 := by rw [mul_pow, hqq, hss]; exact h1
    exact (pow_le_pow_iff_left₀ (mul_nonneg hq0 hs0) hA (by norm_num)).1 this
  have hAhi : nA ≤ p * s := by
    have : nA ^ 2 ≤ (p * s) ^ 2 := by rw [mul_pow, hpp, hss]; exact h2
    exact (pow_le_pow_iff_left₀ hA (mul_nonneg hp0 hs0) (by norm_num)).1 this
  have hDhi : nD ≤ ε * q / 2 * s := by
    have hc : 0 ≤ ε * q / 2 * s := by positivity
    have : nD ^ 2 ≤ (ε * q / 2 * s) ^ 2 := by
      have e : (ε * q / 2 * s) ^ 2 = ε ^ 2 * (1 - ε) / 4 * R := by
        rw [mul_pow, div_pow, mul_pow, hqq, hss]; ring
      rw [e]
      have : 2 * ε ^ 2 * (1 - ε) / 9 * R ≤ ε ^ 2 * (1 - ε) / 4 * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        have : 0 ≤ ε ^ 2 * (1 - ε) := mul_nonneg (sq_nonneg _) (by linarith)
        linarith
      linarith
    exact (pow_le_pow_iff_left₀ hD hc (by norm_num)).1 this
  have hq1 : q ≤ 1 - ε / 2 := by
    have : q ^ 2 ≤ (1 - ε / 2) ^ 2 := by rw [hqq]; nlinarith
    exact (pow_le_pow_iff_left₀ hq0 (by linarith) (by norm_num)).1 this
  have hp1 : p ≤ 1 + ε / 2 := by
    have : p ^ 2 ≤ (1 + ε / 2) ^ 2 := by rw [hpp]; nlinarith
    exact (pow_le_pow_iff_left₀ hp0 (by linarith) (by norm_num)).1 this
  have hqle1 : q ≤ 1 := by linarith
  constructor
  · -- nT ≥ (1 - ε) s
    have hlow : (1 - ε) * s ≤ nT := by
      have k1 : (1 - ε) ≤ q * (1 - ε / 2) := by nlinarith
      have k2 : q * (1 - ε / 2) * s ≤ nT := by nlinarith
      nlinarith
    have h0 : 0 ≤ (1 - ε) * s := mul_nonneg (by linarith) hs0
    have := pow_le_pow_left₀ h0 hlow 2
    rw [mul_pow, hss] at this
    exact this
  · have hhigh : nT ≤ (1 + ε) * s := by
      have k2 : nT ≤ p * s + ε * q / 2 * s := by linarith
      have k3 : ε * q / 2 * s ≤ ε / 2 * s := by
        have : ε * q / 2 ≤ ε / 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hs0
      have k4 : p * s ≤ (1 + ε / 2) * s := mul_le_mul_of_nonneg_right hp1 hs0
      nlinarith
    have := pow_le_pow_left₀ hT hhigh 2
    rw [mul_pow, hss] at this
    exact this

/-- The δ-bound gives `B² (1+ε) |E| ≤ 2ε²(1-ε)/9`. -/
lemma delta_bound (ε wmin wmax n m : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hwmin : 0 < wmin)
    (hn : 1 ≤ n) (hm0 : 0 ≤ m) (hmn : m ≤ n ^ 2) (hwle : 0 < m → wmin ≤ wmax) :
    (ε / 3 * Real.sqrt (2 * (1 - ε) * wmin / ((1 + ε) * n ^ 3 * wmax))) ^ 2 * ((1 + ε) * m)
      ≤ 2 * ε ^ 2 * (1 - ε) / 9 := by
  have hR : 0 ≤ 2 * ε ^ 2 * (1 - ε) / 9 := by
    have : 0 ≤ ε ^ 2 * (1 - ε) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  rcases hm0.eq_or_lt with hm | hm
  · rw [← hm]; simp; exact hR
  have hw := hwle hm
  have hwmax : 0 < wmax := lt_of_lt_of_le hwmin hw
  have hn3 : 0 < n ^ 3 := by positivity
  set X := 2 * (1 - ε) * wmin / ((1 + ε) * n ^ 3 * wmax) with hX
  have hX0 : 0 ≤ X := by
    apply div_nonneg
    · have : 0 ≤ 1 - ε := by linarith
      positivity
    · positivity
  have hB : (ε / 3 * Real.sqrt X) ^ 2 = ε ^ 2 / 9 * X := by
    rw [mul_pow, Real.sq_sqrt hX0]; ring
  rw [hB]
  have hkey : X * ((1 + ε) * m) ≤ 2 * (1 - ε) := by
    rw [hX, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hn23 : n ^ 2 ≤ n ^ 3 := by nlinarith
    have hm' : wmin * m ≤ wmax * n ^ 3 :=
      mul_le_mul hw (hmn.trans hn23) hm.le hwmax.le
    have h0 : 0 ≤ 2 * (1 - ε) * (1 + ε) := by
      have : 0 ≤ 1 - ε := by linarith
      positivity
    have := mul_le_mul_of_nonneg_left hm' h0
    nlinarith
  have : ε ^ 2 / 9 * X * ((1 + ε) * m) = ε ^ 2 / 9 * (X * ((1 + ε) * m)) := by ring
  rw [this]
  have hε2 : 0 ≤ ε ^ 2 / 9 := by positivity
  have := mul_le_mul_of_nonneg_left hkey hε2
  linarith

end P813d17a4

open EffResSparsify.ResistanceSketch Matrix in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : WGraph V E) (hconn : G.IsConnected) (hsimple : G.IsSimple)
    (wmin wmax : ℝ) (hwmin : 0 < wmin) (hw : ∀ e, wmin ≤ G.w e ∧ G.w e ≤ wmax)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (k : ℕ) (Z Zt : Matrix (Fin k) V ℝ) (δ : ℝ)
    (hZ : ∀ u v : V,
      (1 - ε) * G.R u v ≤ sqNorm (Z *ᵥ (WGraph.chi u - WGraph.chi v)) ∧
        sqNorm (Z *ᵥ (WGraph.chi u - WGraph.chi v)) ≤ (1 + ε) * G.R u v)
    (h4 : ∀ i : Fin k, G.lNorm (Z i - Zt i) ≤ δ * G.lNorm (Z i))
    (h5 : δ ≤ ε / 3 * Real.sqrt (2 * (1 - ε) * wmin /
      ((1 + ε) * (Fintype.card V : ℝ) ^ 3 * wmax))) :
    ∀ u v : V,
      (1 - ε) ^ 2 * G.R u v ≤ sqNorm (Zt *ᵥ (WGraph.chi u - WGraph.chi v)) ∧
        sqNorm (Zt *ᵥ (WGraph.chi u - WGraph.chi v)) ≤ (1 + ε) ^ 2 * G.R u v := by
  intro u v
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set m : ℝ := (Fintype.card E : ℝ) with hm
  set B : ℝ := ε / 3 * Real.sqrt (2 * (1 - ε) * wmin / ((1 + ε) * n ^ 3 * wmax)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ε / 3 := by positivity
    exact mul_nonneg this (Real.sqrt_nonneg _)
  -- quadratic form shorthand
  have hQ : ∀ y : V → ℝ, G.lNorm y ^ 2 = y ⬝ᵥ (G.laplacian *ᵥ y) := fun y =>
    Real.sq_sqrt (P813d17a4.quad_nonneg G y)
  -- row bound
  have hrow : ∀ i : Fin k, (Z i - Zt i) ⬝ᵥ (G.laplacian *ᵥ (Z i - Zt i)) ≤
      B ^ 2 * (Z i ⬝ᵥ (G.laplacian *ᵥ Z i)) := by
    intro i
    have h1 : G.lNorm (Z i - Zt i) ≤ B * G.lNorm (Z i) :=
      (h4 i).trans (mul_le_mul_of_nonneg_right h5 (Real.sqrt_nonneg _))
    have h0 : 0 ≤ G.lNorm (Z i - Zt i) := Real.sqrt_nonneg _
    have h2 := pow_le_pow_left₀ h0 h1 2
    rw [mul_pow, hQ, hQ] at h2
    exact h2
  -- S bound
  have hS : ∑ i : Fin k, Z i ⬝ᵥ (G.laplacian *ᵥ Z i) ≤ (1 + ε) * m := by
    have hS1 : ∑ i : Fin k, Z i ⬝ᵥ (G.laplacian *ᵥ Z i) =
        ∑ e, G.w e * sqNorm (Z *ᵥ (WGraph.chi (G.head e) - WGraph.chi (G.tail e))) := by
      simp only [P813d17a4.dot_lap, sqNorm, P813d17a4.mulVec_chi]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hS1, hm, Finset.card_univ.symm, Finset.cast_card, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have := (hZ (G.head e) (G.tail e)).2
    have hwe := P813d17a4.w_mul_R_le G hconn e
    have hwp := G.w_pos e
    calc G.w e * sqNorm (Z *ᵥ (WGraph.chi (G.head e) - WGraph.chi (G.tail e)))
        ≤ G.w e * ((1 + ε) * G.R (G.head e) (G.tail e)) :=
          mul_le_mul_of_nonneg_left this hwp.le
      _ = (1 + ε) * (G.w e * G.R (G.head e) (G.tail e)) := by ring
      _ ≤ (1 + ε) * 1 := mul_le_mul_of_nonneg_left hwe (by linarith)
  -- c bound
  have hn1 : 1 ≤ n := by
    have := hconn.nonempty
    have : 0 < Fintype.card V := Fintype.card_pos
    rw [hn]; exact_mod_cast this
  have hc : B ^ 2 * ((1 + ε) * m) ≤ 2 * ε ^ 2 * (1 - ε) / 9 := by
    apply P813d17a4.delta_bound ε wmin wmax n m hε0 hε1 hwmin hn1 (by positivity)
      (P813d17a4.card_E_le G hsimple)
    intro hmpos
    rw [hm] at hmpos
    have : 0 < Fintype.card E := by exact_mod_cast hmpos
    obtain ⟨e⟩ := Fintype.card_pos_iff.1 this
    exact (hw e).1.trans (hw e).2
  -- the vectors
  set b : V → ℝ := WGraph.chi u - WGraph.chi v with hb
  set x : V → ℝ := G.lapPinv *ᵥ b with hx
  have hLx : G.laplacian *ᵥ x = b := P813d17a4.lap_pinv_spec G hconn u v
  have hRx : G.R u v = x ⬝ᵥ (G.laplacian *ᵥ x) := P813d17a4.R_eq_quad G hconn u v
  have hR0 : 0 ≤ G.R u v := P813d17a4.R_nonneg G hconn u v
  set a : Fin k → ℝ := Z *ᵥ b with ha
  set t : Fin k → ℝ := Zt *ᵥ b with ht
  set d : Fin k → ℝ := a - t with hd
  have hdi : ∀ i, d i = (Z i - Zt i) ⬝ᵥ (G.laplacian *ᵥ x) := by
    intro i
    rw [hLx, sub_dotProduct]
    rfl
  have hdsq : sqNorm d ≤ 2 * ε ^ 2 * (1 - ε) / 9 * G.R u v := by
    have hsum : sqNorm d ≤ ∑ i : Fin k, B ^ 2 * (Z i ⬝ᵥ (G.laplacian *ᵥ Z i)) * G.R u v := by
      unfold sqNorm
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hdi i]
      refine (P813d17a4.cs_lap G _ _).trans ?_
      rw [← hRx]
      exact mul_le_mul_of_nonneg_right (hrow i) hR0
    refine hsum.trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have h1 : B ^ 2 * ∑ i : Fin k, Z i ⬝ᵥ (G.laplacian *ᵥ Z i) ≤ B ^ 2 * ((1 + ε) * m) :=
      mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (h1.trans hc) hR0
  -- norms
  set A : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 a with hA
  set T : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 t with hT
  set D : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 d with hD
  have hTAD : T = A - D := by
    rw [hT, hA, hD, ← WithLp.toLp_sub, hd]; congr 1; abel
  have hATD : A = T + D := by rw [hTAD]; abel
  have k1 : ‖T‖ ≤ ‖A‖ + ‖D‖ := by rw [hTAD]; exact norm_sub_le _ _
  have k2 : ‖A‖ ≤ ‖T‖ + ‖D‖ := by
    conv_lhs => rw [hATD]
    exact norm_add_le _ _
  have hAsq : ‖A‖ ^ 2 = sqNorm a := P813d17a4.norm_sq_toLp a
  have hTsq : ‖T‖ ^ 2 = sqNorm t := P813d17a4.norm_sq_toLp t
  have hDsq : ‖D‖ ^ 2 = sqNorm d := P813d17a4.norm_sq_toLp d
  have := P813d17a4.final_ineq (G.R u v) ε ‖A‖ ‖T‖ ‖D‖ hR0 hε0 hε1 (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (by rw [hAsq]; exact (hZ u v).1)
    (by rw [hAsq]; exact (hZ u v).2) (by rw [hDsq]; exact hdsq) k1 k2
  rw [hTsq] at this
  exact this
