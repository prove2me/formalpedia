-- Prove2me | solution 1 for GaussianMatrix.spectral_second_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:01:08.801022+00:00
-- url     : https://prove2.me/submissions/239c2a1c-73e0-4964-97da-98b364a3a752

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_slepian_tail_comparison
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-! ### Gaussian coordinates and linear forms (adapted from the `gordon_upper` reduction) -/

lemma ssb_hasGaussianLaw_pi (κ : Type*) [Fintype κ] :
    HasGaussianLaw (fun x : κ → ℝ => x) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have h := iIndepFun.hasGaussianLaw (P := Measure.pi fun _ : κ => gaussianReal 0 1)
    (X := fun k (x : κ → ℝ) => x k) (fun k => ⟨by
      have := (measurePreserving_eval (fun _ : κ => gaussianReal (0 : ℝ) 1) k).map_eq
      rw [this]; infer_instance⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

lemma ssb_hasGaussianLaw_id (p m : ℕ) :
    HasGaussianLaw (fun G : Fin p → Fin m → ℝ => G) (gaussianMatrix p m) := by
  have h := iIndepFun.hasGaussianLaw (P := gaussianMatrix p m)
    (X := fun i (G : Fin p → Fin m → ℝ) => G i) (fun i => ⟨by
      have := (measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) i).map_eq
      unfold gaussianMatrix
      rw [this]
      have := (ssb_hasGaussianLaw_pi (Fin m)).isGaussian_map
      rwa [Measure.map_id'] at this⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

lemma ssb_measurePreserving_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

lemma ssb_memLp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (q : ENNReal) (hq : q ≠ ⊤) :
    MemLp (fun G : Fin p → Fin m → ℝ => G a b) q (gaussianMatrix p m) :=
  (memLp_id_gaussianReal' q hq).comp_measurePreserving (ssb_measurePreserving_coord a b)

lemma ssb_integral_comp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (f : ℝ → ℝ)
    (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix p m) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (ssb_measurePreserving_coord a b).map_eq, integral_map]
  · exact (ssb_measurePreserving_coord a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

lemma ssb_integral_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ∂(gaussianMatrix p m) = 0 := by
  have := ssb_integral_comp_coord a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

lemma ssb_integral_coord_sq {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix p m) = 1 := by
  rw [ssb_integral_comp_coord a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

lemma ssb_integral_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) :
    ∫ G, G a b * G c d ∂(gaussianMatrix p m) = if a = c ∧ b = d then 1 else 0 := by
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simpa [← pow_two] using ssb_integral_coord_sq a b
    · simp only [hbd, and_false, if_false]
      have hrow := measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) a
      have h1 : ∫ G, G a b * G a d ∂(gaussianMatrix p m)
          = ∫ x, x b * x d ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) := by
        have := integral_map (μ := gaussianMatrix p m) hrow.measurable.aemeasurable
          (f := fun x : Fin m → ℝ => x b * x d) (by fun_prop)
        unfold gaussianMatrix at this ⊢
        rw [hrow.map_eq] at this
        exact this.symm
      rw [h1]
      have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → ℝ) => ω i)
          (Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) :=
        iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
      rw [(hind.indepFun hbd).integral_fun_mul_eq_mul_integral
        (measurable_pi_apply b).aestronglyMeasurable (measurable_pi_apply d).aestronglyMeasurable]
      have h0 : ∫ x, x b ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) = 0 := by
        have hb := measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) b
        have := integral_map (μ := Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1)
          hb.measurable.aemeasurable (f := fun x : ℝ => x) (by fun_prop)
        rw [hb.map_eq, integral_id_gaussianReal] at this
        exact this.symm
      simp [h0]
  · simp only [hac, false_and, if_false]
    have hind : iIndepFun (fun (i : Fin p) (ω : Fin p → Fin m → ℝ) => ω i)
        (gaussianMatrix p m) :=
      iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
    have h2 := (hind.indepFun hac).comp (measurable_pi_apply b) (measurable_pi_apply d)
    have := h2.integral_fun_mul_eq_mul_integral
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω a b) := by fun_prop
        exact this.aestronglyMeasurable)
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω c d) := by fun_prop
        exact this.aestronglyMeasurable)
    simp only [Function.comp_def] at this
    rw [this, ssb_integral_coord]
    simp

lemma ssb_integrable_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) (k : ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => k * (G a b * G c d)) (gaussianMatrix p m) :=
  ((ssb_memLp_coord a b 2 (by simp)).integrable_mul (ssb_memLp_coord c d 2 (by simp))).const_mul k


noncomputable def ssbLin {p m : ℕ} (c : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * G i j

/-- The coefficient-to-form map as a continuous linear map into `ι → ℝ`. -/
noncomputable def ssbLinCLM {ι : Type*} {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    (Fin p → Fin m → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun t => ∑ i, ∑ j,
    a t i j • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => Fin m → ℝ) i))

lemma ssb_hasGaussianLaw_lin {ι : Type*} [Fintype ι] {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    HasGaussianLaw (fun G t => ssbLin (a t) G) (gaussianMatrix p m) := by
  have h := (ssb_hasGaussianLaw_id p m).map_fun (ssbLinCLM a)
  have e : (fun G t => ssbLin (a t) G) = fun G => ssbLinCLM a G := by
    funext G t
    simp [ssbLinCLM, ssbLin]
  rw [e]; exact h


lemma ssb_integrable_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    Integrable (ssbLin c) (gaussianMatrix p m) := by
  unfold ssbLin
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((ssb_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _

lemma ssb_continuous_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) : Continuous (ssbLin c) := by
  unfold ssbLin; fun_prop

lemma ssb_integral_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, ssbLin c G ∂(gaussianMatrix p m) = 0 := by
  unfold ssbLin
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((ssb_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    ((ssb_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, ssb_integral_coord, mul_zero]

lemma ssb_lin_sub {p m : ℕ} (c d : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    ssbLin c G - ssbLin d G = ssbLin (c - d) G := by
  simp only [ssbLin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_mul]

lemma ssb_integral_lin_sq {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, ssbLin c G ^ 2 ∂(gaussianMatrix p m) = ∑ i, ∑ j, c i j ^ 2 := by
  have hexp : ∀ G : Fin p → Fin m → ℝ, ssbLin c G ^ 2 =
      ∑ i, ∑ k, ∑ j, ∑ l, c i j * c k l * (G i j * G k l) := by
    intro G
    unfold ssbLin
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    ssb_integrable_coord_mul i k j l _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    ssb_integrable_coord_mul i k j l _]
  rw [Finset.sum_eq_single i]
  · rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      ssb_integrable_coord_mul i i j l _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => ssb_integrable_coord_mul i i j l _]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, ssb_integral_coord_mul]; simp [sq]
    · intro l _ hl
      rw [integral_const_mul, ssb_integral_coord_mul]; simp [Ne.symm hl]
    · simp
  · intro k _ hk
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      ssb_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => ssb_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_const_mul, ssb_integral_coord_mul]; simp [Ne.symm hk]
  · simp


/-! ### Deterministic part -/

lemma ssb_norm_sq_eq {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ ^ 2 = ∑ j, u j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

lemma ssb_norm_eq_sqrt {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ = Real.sqrt (∑ j, u j ^ 2) := by
  rw [← ssb_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

open scoped RealInnerProductSpace in
lemma ssb_inner_matrix {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin N)) :
    ⟪v, (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A u⟫
      = ∑ i, ∑ j, v i * A i j * u j := by
  simp [PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

open scoped Matrix.Norms.L2Operator RealInnerProductSpace in
/-- Net argument: if every pair of unit vectors is `ε`-close to a pair in `I` (whose second
components are unit vectors), then `(1 - 2ε)‖A‖ ≤ max_{(u,v) ∈ I} ⟨v, A u⟩`. -/
lemma ssb_net_bound {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (I : Finset (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin N)))
    (hI : ∀ t ∈ I, ‖t.2‖ = 1)
    (hcov : ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N)), ‖u‖ = 1 → ‖v‖ = 1 →
      ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε) :
    (1 - 2 * ε) * specNorm A ≤ ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j := by
  set Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A with hΦ
  have hM : specNorm A = ‖Φ‖ := rfl
  set S := ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j with hS
  have hbdd : BddAbove (Set.range fun t : I => ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j) :=
    (Set.finite_range _).bddAbove
  set M := ‖Φ‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  rw [hM]
  rcases hM0.lt_or_eq with hMpos | hMzero
  · -- main case
    have claim : ∀ r : ℝ, 0 ≤ r → r < M → r - 2 * ε * M ≤ S := by
      intro r hr0 hrM
      obtain ⟨x, hx1, hrx⟩ := Φ.exists_lt_apply_of_lt_opNorm hrM
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hrx
        linarith
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      set u : EuclideanSpace ℝ (Fin n) := (‖x‖⁻¹ : ℝ) • x with hu
      have hu1 : ‖u‖ = 1 := norm_smul_inv_norm hx0
      have hΦu : ‖Φ x‖ ≤ ‖Φ u‖ := by
        rw [hu, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
        rw [le_inv_mul_iff₀ hxpos]
        exact mul_le_of_le_one_left (norm_nonneg _) hx1.le
      set w := Φ u with hw
      have hrw : r < ‖w‖ := lt_of_lt_of_le hrx hΦu
      have hw0 : w ≠ 0 := by
        intro h; rw [h, norm_zero] at hrw; linarith
      set v : EuclideanSpace ℝ (Fin N) := (‖w‖⁻¹ : ℝ) • w with hv
      have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hw0
      have hvw : ⟪v, w⟫ = ‖w‖ := by
        rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
        have : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
        field_simp
      obtain ⟨t, ht, htu, htv⟩ := hcov u v hu1 hv1
      have ht2 : ‖t.2‖ = 1 := hI t ht
      have hwM : ‖w‖ ≤ M := by
        have := Φ.le_opNorm u; rw [hu1, mul_one] at this; exact this
      have hdecomp : Φ t.1 = w - Φ (u - t.1) := by
        rw [map_sub]; abel
      have hval : ∑ i, ∑ j, t.2 i * A i j * t.1 j = ⟪t.2, Φ t.1⟫ :=
        (ssb_inner_matrix A t.1 t.2).symm
      have hval2 : ⟪t.2, Φ t.1⟫ = ⟪v, w⟫ - ⟪v - t.2, w⟫ - ⟪t.2, Φ (u - t.1)⟫ := by
        rw [hdecomp, inner_sub_right, inner_sub_left]; ring
      have hb1 : ⟪v - t.2, w⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        exact mul_le_mul htv hwM (norm_nonneg _) hε
      have hb2 : ⟪t.2, Φ (u - t.1)⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        rw [ht2, one_mul]
        refine (Φ.le_opNorm _).trans ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right htu hM0
      have hle : ∑ i, ∑ j, t.2 i * A i j * t.1 j ≤ S :=
        le_ciSup hbdd (⟨t, ht⟩ : I)
      rw [hval, hval2, hvw] at hle
      linarith
    by_contra hcon
    push Not at hcon
    set r := (S + 2 * ε * M + M) / 2
    have h1 := claim (max r 0) (le_max_right _ _) (max_lt (by
      simp only [r]; nlinarith) hMpos)
    have : r ≤ max r 0 := le_max_left _ _
    simp only [r] at this
    nlinarith
  · -- `A = 0`
    have hA : Φ = 0 := norm_eq_zero.1 hMzero.symm
    have hA' : ∀ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j = 0 := by
      intro t
      rw [← ssb_inner_matrix, ← hΦ, hA]
      simp
    rw [← hMzero]
    simp only [mul_zero]
    rw [hS]
    simp only [hA', Real.iSup_const_zero, le_refl]


/-! ### Probabilistic estimates -/

lemma ssb_integrable_iSup {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => ⨆ t, f t ω) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).abs)
    (Measurable.iSup hm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨t0⟩ := ‹Nonempty ι›
  have hb : BddAbove (Set.range fun t => f t ω) := (Set.finite_range _).bddAbove
  have hs : ∀ t, |f t ω| ≤ ∑ t, |f t ω| := fun t =>
    Finset.single_le_sum (f := fun t => |f t ω|) (fun t _ => abs_nonneg _) (Finset.mem_univ t)
  constructor
  · have h1 := le_ciSup hb t0
    have h2 := hs t0
    have := neg_abs_le (f t0 ω)
    linarith
  · exact ciSup_le fun t => (le_abs_self _).trans (hs t)

/-- `𝔼 X ≤ (𝔼 X² / δ + δ) / 2` for every `δ > 0` (from `2δx ≤ x² + δ²`). -/
lemma ssb_integral_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (δ : ℝ) (hδ : 0 < δ) :
    ∫ ω, X ω ∂μ ≤ ((∫ ω, X ω ^ 2 ∂μ) / δ + δ) / 2 := by
  have hI : Integrable (fun ω => (X ω ^ 2 / δ + δ) / 2) μ :=
    ((hX2.div_const δ).add (integrable_const δ)).div_const 2
  have hpt : ∀ ω, X ω ≤ (X ω ^ 2 / δ + δ) / 2 := by
    intro ω
    rw [div_add' _ _ _ hδ.ne', div_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (X ω - δ)]
  refine (integral_mono hX hI hpt).trans (le_of_eq ?_)
  rw [integral_div, integral_add (hX2.div_const δ) (integrable_const δ), integral_div,
    integral_const]
  simp

/-- Jensen (Cauchy–Schwarz) in the form: `𝔼 X² ≤ c²` with `c ≥ 0` implies `𝔼 X ≤ c`. -/
lemma ssb_integral_le_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫ ω, X ω ^ 2 ∂μ ≤ c ^ 2) : ∫ ω, X ω ∂μ ≤ c := by
  rcases hc.lt_or_eq with hc | hc
  · refine (ssb_integral_le_of_sq μ X hX hX2 c hc).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / c ≤ c := by
      rw [div_le_iff₀ hc]; nlinarith
    linarith
  · subst hc
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    refine (ssb_integral_le_of_sq μ X hX hX2 δ hδ).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by simpa using h) hδ.le
    linarith


/-- `𝔼 √(∑ⱼ H₀,σ(j)²) ≤ √k` for a family of `k` coordinates of a Gaussian row. -/
lemma ssb_integral_sqrt_sumsq_le {k m : ℕ} (σ : Fin k → Fin m) :
    ∫ H, Real.sqrt (∑ j, H 0 (σ j) ^ 2) ∂(gaussianMatrix 1 m) ≤ Real.sqrt k := by
  have hQ : Integrable (fun H : Fin 1 → Fin m → ℝ => ∑ j, H 0 (σ j) ^ 2) (gaussianMatrix 1 m) :=
    integrable_finsetSum _ fun j _ => (ssb_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq
  have hQ0 : ∀ H : Fin 1 → Fin m → ℝ, 0 ≤ ∑ j, H 0 (σ j) ^ 2 := fun H =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcont : Continuous (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2)) := by
    fun_prop
  have hS : Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix 1 m) := by
    refine Integrable.mono' ((integrable_const 1).add hQ) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun H => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := Real.sq_sqrt (hQ0 H)
    have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]
  have hS2 : Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2) ^ 2)
      (gaussianMatrix 1 m) := by
    refine hQ.congr (Filter.Eventually.of_forall fun H => ?_)
    exact (Real.sq_sqrt (hQ0 H)).symm
  refine ssb_integral_le_of_integral_sq_le _ _ hS hS2 _ (Real.sqrt_nonneg _) (le_of_eq ?_)
  rw [Real.sq_sqrt (Nat.cast_nonneg k)]
  simp_rw [Real.sq_sqrt (hQ0 _)]
  rw [integral_finsetSum _ fun j _ => (ssb_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq]
  simp [ssb_integral_coord_sq]

/-- Coefficient comparison for unit vectors:
`‖v uᵀ - v' u'ᵀ‖_F² ≤ ‖u - u'‖² + ‖v - v'‖²`. -/
lemma ssb_coeff_ineq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2 ≤ ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← ssb_norm_sq_eq, hu, one_pow]
  have su' : ∑ j, u' j ^ 2 = 1 := by rw [← ssb_norm_sq_eq, hu', one_pow]
  have sv : ∑ i, v i ^ 2 = 1 := by rw [← ssb_norm_sq_eq, hv, one_pow]
  have sv' : ∑ i, v' i ^ 2 = 1 := by rw [← ssb_norm_sq_eq, hv', one_pow]
  set α := ∑ j, u j * u' j with hαdef
  set β := ∑ i, v i * v' i with hβdef
  have hL : ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2
      = (∑ i, v i ^ 2) * (∑ j, u j ^ 2) - 2 * (β * α) + (∑ i, v' i ^ 2) * (∑ j, u' j ^ 2) := by
    rw [hαdef, hβdef, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRu : ∑ j, (u j - u' j) ^ 2 = ∑ j, u j ^ 2 - 2 * α + ∑ j, u' j ^ 2 := by
    rw [hαdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRv : ∑ i, (v i - v' i) ^ 2 = ∑ i, v i ^ 2 - 2 * β + ∑ i, v' i ^ 2 := by
    rw [hβdef, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hα : α ≤ 1 := by
    have : 0 ≤ ∑ j, (u j - u' j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hβ : β ≤ 1 := by
    have : 0 ≤ ∑ i, (v i - v' i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  rw [hL, hRu, hRv, su, su', sv, sv']
  nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hβ)]

/-- Increments of the comparison process `⟨g, u⟩ + ⟨h, v⟩`, written with one Gaussian row
`H₀ ∈ ℝ^{n+N}`. -/
lemma ssb_coeffY_sq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N)) :
    ∑ _i : Fin 1, ∑ k : Fin (n + N),
      (Fin.append (fun j => u j) (fun i => v i) k - Fin.append (fun j => u' j) (fun i => v' i) k) ^ 2
      = ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

lemma ssb_Y_le {N n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (H : Fin 1 → Fin (n + N) → ℝ) :
    ssbLin (fun _ k => Fin.append (fun j => u j) (fun i => v i) k) H
      ≤ Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2) + Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2) := by
  unfold ssbLin
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => u j) (fun j => H 0 (Fin.castAdd N j))
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => v i) (fun i => H 0 (Fin.natAdd n i))
  rw [← ssb_norm_eq_sqrt, hu, one_mul] at h1
  rw [← ssb_norm_eq_sqrt, hv, one_mul] at h2
  exact add_le_add h1 h2


/-! ### Integrability -/

/-- `‖G‖_F² = ∑ᵢⱼ Gᵢⱼ²` is integrable under the Gaussian matrix law. -/
lemma ssb_integrable_frobSq (p m : ℕ) :
    Integrable (fun X : Fin p → Fin m → ℝ => frobSq (Matrix.of X)) (gaussianMatrix p m) := by
  unfold frobSq
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp only [Matrix.of_apply]
  exact ((memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving
    (ssb_measurePreserving_coord i j)).integrable_sq

lemma ssb_frobSq_nonneg {p m : ℕ} (X : Fin p → Fin m → ℝ) : 0 ≤ frobSq (Matrix.of X) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma ssb_continuous_frobNorm (p m : ℕ) :
    Continuous (fun X : Fin p → Fin m → ℝ => frobNorm (Matrix.of X)) := by
  unfold frobNorm frobSq
  simp only [Matrix.of_apply]
  fun_prop

/-- A function that is `L`-Lipschitz for the Frobenius norm is continuous. -/
lemma ssb_continuous_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro X₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀))) :=
    continuous_const.mul ((ssb_continuous_frobNorm p m).comp (continuous_id.sub
      continuous_const))
  have h0 : Filter.Tendsto (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀)))
      (nhds X₀) (nhds 0) := by
    have := hc.tendsto X₀
    simpa [frobNorm, frobSq] using this
  refine squeeze_zero (fun _ => dist_nonneg) (fun Y => ?_) h0
  rw [Real.dist_eq]
  have := hLip Y X₀
  simpa [Matrix.of_sub_of] using this

/-- A function that is `L`-Lipschitz for the Frobenius norm is integrable, with integrable
square, under the Gaussian matrix law. -/
lemma ssb_integrable_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) :
    Integrable h (gaussianMatrix p m) ∧
      Integrable (fun X => h X ^ 2) (gaussianMatrix p m) := by
  have hcont := ssb_continuous_of_lip h L hLip
  have hF := ssb_integrable_frobSq p m
  have hbound : ∀ X, |h X| ≤ |h 0| + L * frobNorm (Matrix.of X) := by
    intro X
    have h1 := hLip X 0
    have h2 : Matrix.of X - Matrix.of (0 : Fin p → Fin m → ℝ) = Matrix.of X := by
      ext i j; simp
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub (h X) (h 0)
    linarith
  have hsq : ∀ X : Fin p → Fin m → ℝ, frobNorm (Matrix.of X) ^ 2 = frobSq (Matrix.of X) := fun X =>
    Real.sq_sqrt (ssb_frobSq_nonneg X)
  have hfn : ∀ X : Fin p → Fin m → ℝ, 0 ≤ frobNorm (Matrix.of X) := fun X => Real.sqrt_nonneg _
  constructor
  · refine Integrable.mono' (((integrable_const (|h 0| + L)).add (hF.const_mul L)))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    refine (hbound X).trans ?_
    have := hsq X
    have := hfn X
    have : frobNorm (Matrix.of X) ≤ 1 + frobSq (Matrix.of X) := by
      nlinarith [sq_nonneg (frobNorm (Matrix.of X) - 1)]
    simp only [Pi.add_apply]
    nlinarith
  · refine Integrable.mono' (((integrable_const (2 * h 0 ^ 2)).add (hF.const_mul (2 * L ^ 2))))
      (hcont.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have hb := hbound X
    have h0 : 0 ≤ |h X| := abs_nonneg _
    have : |h X| ^ 2 ≤ (|h 0| + L * frobNorm (Matrix.of X)) ^ 2 := pow_le_pow_left₀ h0 hb 2
    rw [sq_abs] at this
    simp only [Pi.add_apply]
    have hs := hsq X
    nlinarith [sq_nonneg (|h 0| - L * frobNorm (Matrix.of X)), sq_abs (h 0)]


/-- Row-wise Cauchy–Schwarz: `‖B x‖₂² ≤ ‖B‖_F² ‖x‖₂²`. -/
lemma ssb_mulVec_dot_le {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ frobSq B * (x ⬝ᵥ x) := by
  unfold frobSq
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) x
  calc (∑ j, B i j * x j) * (∑ j, B i j * x j) = (∑ j, B i j * x j) ^ 2 := by ring
    _ ≤ (∑ j, B i j ^ 2) * ∑ j, x j ^ 2 := h
    _ = (∑ j, B i j ^ 2) * ∑ j, x j * x j := by simp only [sq]

lemma ssb_frobSq_nonneg' {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ) :
    0 ≤ frobSq B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma ssb_euclid_norm {n : Type*} [Fintype n] (v : EuclideanSpace ℝ n) :
    ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

open scoped Matrix.Norms.L2Operator in
/-- The `ℓ₂ → ℓ₂` operator norm is at most the Frobenius norm. -/
lemma ssb_specNorm_le_frobNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (B : Matrix m n ℝ) : specNorm B ≤ frobNorm B := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  show ‖(Matrix.toEuclideanLin B x)‖ ≤ frobNorm B * ‖x‖
  rw [ssb_euclid_norm, ssb_euclid_norm, frobNorm, ← Real.sqrt_mul
    (ssb_frobSq_nonneg' B)]
  exact Real.sqrt_le_sqrt (ssb_mulVec_dot_le B x.ofLp)

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖S G T‖` is `‖S‖‖T‖`-Lipschitz for the Frobenius norm. -/
lemma ssb_sandwich_lip {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) (X Y : Fin p → Fin m → ℝ) :
    |specNorm (S * Matrix.of X * T) - specNorm (S * Matrix.of Y * T)|
      ≤ (specNorm S * specNorm T) * frobNorm (Matrix.of X - Matrix.of Y) := by
  unfold specNorm
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have hd : S * Matrix.of X * T - S * Matrix.of Y * T = S * (Matrix.of X - Matrix.of Y) * T := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hd]
  have h1 := Matrix.l2_opNorm_mul (S * (Matrix.of X - Matrix.of Y)) T
  have h2 := Matrix.l2_opNorm_mul S (Matrix.of X - Matrix.of Y)
  have h3 := ssb_specNorm_le_frobNorm (Matrix.of X - Matrix.of Y)
  unfold specNorm at h3
  have hS : 0 ≤ ‖S‖ := norm_nonneg _
  have hT : 0 ≤ ‖T‖ := norm_nonneg _
  have hD : 0 ≤ ‖Matrix.of X - Matrix.of Y‖ := norm_nonneg _
  calc ‖S * (Matrix.of X - Matrix.of Y) * T‖
      ≤ ‖S * (Matrix.of X - Matrix.of Y)‖ * ‖T‖ := h1
    _ ≤ (‖S‖ * ‖Matrix.of X - Matrix.of Y‖) * ‖T‖ := mul_le_mul_of_nonneg_right h2 hT
    _ ≤ (‖S‖ * frobNorm (Matrix.of X - Matrix.of Y)) * ‖T‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hS) hT
    _ = (‖S‖ * ‖T‖) * frobNorm (Matrix.of X - Matrix.of Y) := by ring

open scoped Matrix.Norms.L2Operator in
lemma ssb_specNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (B : Matrix m n ℝ) : 0 ≤ specNorm B := norm_nonneg _


/-! ### The matrix process `X` on `(G, γ)` -/

/-- Joint law of an independent pair `(G, γ)`: Gaussian matrix and standard normal scalar. -/
noncomputable abbrev ssbP (p m : ℕ) : Measure ((Fin p → Fin m → ℝ) × ℝ) :=
  (gaussianMatrix p m).prod (gaussianReal 0 1)

/-- `X_{c,d}(G, γ) = ∑ᵢⱼ cᵢⱼ Gᵢⱼ + d γ`. -/
noncomputable def ssbX {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ)
    (ω : (Fin p → Fin m → ℝ) × ℝ) : ℝ := ssbLin c ω.1 + d * ω.2

instance ssb_isGaussian_gm (p m : ℕ) : IsGaussian (gaussianMatrix p m) := by
  have := (ssb_hasGaussianLaw_id p m).isGaussian_map
  rwa [Measure.map_id'] at this

lemma ssb_hasGaussianLaw_X {ι : Type*} [Fintype ι] {p m : ℕ} (c : ι → Fin p → Fin m → ℝ)
    (d : ι → ℝ) : HasGaussianLaw (fun ω t => ssbX (c t) (d t) ω) (ssbP p m) := by
  have h0 : HasGaussianLaw (fun ω : (Fin p → Fin m → ℝ) × ℝ => ω) (ssbP p m) := by
    have : IsGaussian (ssbP p m) := inferInstance
    exact ⟨by rw [Measure.map_id']; exact this⟩
  set L : ((Fin p → Fin m → ℝ) × ℝ) →L[ℝ] (ι → ℝ) :=
    (ssbLinCLM c).comp (ContinuousLinearMap.fst ℝ _ _) +
      (ContinuousLinearMap.pi fun t => d t • ContinuousLinearMap.snd ℝ (Fin p → Fin m → ℝ) ℝ)
  have h := h0.map_fun L
  have e : (fun ω t => ssbX (c t) (d t) ω) = fun ω => L ω := by
    funext ω t
    simp [L, ssbX, ssbLinCLM, ssbLin]
  rw [e]; exact h

lemma ssb_memLp_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    MemLp (ssbLin c) 2 (gaussianMatrix p m) := by
  unfold ssbLin
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
    (ssb_memLp_coord i j 2 (by simp)).const_mul _

lemma ssb_memLp_fst {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    MemLp (fun ω : (Fin p → Fin m → ℝ) × ℝ => ssbLin c ω.1) 2 (ssbP p m) :=
  (ssb_memLp_lin c).comp_measurePreserving measurePreserving_fst

lemma ssb_memLp_snd (p m : ℕ) :
    MemLp (fun ω : (Fin p → Fin m → ℝ) × ℝ => ω.2) 2 (ssbP p m) :=
  (memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving measurePreserving_snd

lemma ssb_memLp_X {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) :
    MemLp (ssbX c d) 2 (ssbP p m) :=
  (ssb_memLp_fst c).add ((ssb_memLp_snd p m).const_mul d)

lemma ssb_continuous_X {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) : Continuous (ssbX c d) := by
  unfold ssbX ssbLin; fun_prop

lemma ssb_integral_X {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) :
    ∫ ω, ssbX c d ω ∂(ssbP p m) = 0 := by
  unfold ssbX
  rw [integral_add ((ssb_memLp_fst c).integrable (by simp))
    (((ssb_memLp_snd p m).integrable (by simp)).const_mul d), integral_const_mul]
  rw [integral_fun_fst (fun G => ssbLin c G), integral_fun_snd (fun x : ℝ => x)]
  simp [ssb_integral_lin, integral_id_gaussianReal]

lemma ssb_X_sub {p m : ℕ} (c c' : Fin p → Fin m → ℝ) (d d' : ℝ) (ω : (Fin p → Fin m → ℝ) × ℝ) :
    ssbX c d ω - ssbX c' d' ω = ssbX (c - c') (d - d') ω := by
  unfold ssbX
  rw [← ssb_lin_sub]; ring

lemma ssb_integral_X_sq {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) :
    ∫ ω, ssbX c d ω ^ 2 ∂(ssbP p m) = ∑ i, ∑ j, c i j ^ 2 + d ^ 2 := by
  have hexp : ∀ ω : (Fin p → Fin m → ℝ) × ℝ, ssbX c d ω ^ 2 =
      ssbLin c ω.1 ^ 2 + 2 * d * (ssbLin c ω.1 * ω.2) + d ^ 2 * ω.2 ^ 2 := by
    intro ω; unfold ssbX; ring
  simp_rw [hexp]
  have i1 := (ssb_memLp_fst c).integrable_sq
  have i2 : Integrable (fun ω : (Fin p → Fin m → ℝ) × ℝ => 2 * d * (ssbLin c ω.1 * ω.2))
      (ssbP p m) := ((ssb_memLp_fst c).integrable_mul (ssb_memLp_snd p m)).const_mul (2 * d)
  have i3 := (ssb_memLp_snd p m).integrable_sq.const_mul (d ^ 2)
  rw [integral_add (f := fun ω => ssbLin c ω.1 ^ 2 + 2 * d * (ssbLin c ω.1 * ω.2)) (i1.add i2) i3,
    integral_add i1 i2, integral_const_mul, integral_const_mul]
  rw [integral_fun_fst (fun G => ssbLin c G ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2)]
  have hprod := integral_prod_mul (μ := gaussianMatrix p m) (ν := gaussianReal 0 1)
    (fun G => ssbLin c G) (fun x : ℝ => x)
  rw [hprod, ssb_integral_lin_sq]
  have h1 : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
    rw [variance_id_gaussianReal] at h
    simp [integral_id_gaussianReal] at h
    exact h.symm
  simp [h1, ssb_integral_lin]


/-! ### Positive part of a finite maximum, Fubini–Jensen step, layer cake -/

lemma ssb_sup_sq_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    max (⨆ t, f t) 0 ^ 2 ≤ ∑ t, f t ^ 2 := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := f)
  rw [← ht0]
  have h : max (f t0) 0 ^ 2 ≤ f t0 ^ 2 := by
    rcases le_total (f t0) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (f t0)]
    · rw [max_eq_left h]
  exact h.trans (Finset.single_le_sum (f := fun t => f t ^ 2) (fun t _ => sq_nonneg _)
    (Finset.mem_univ t0))

lemma ssb_integrable_supsq {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, MemLp (f t) 2 μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => max (⨆ t, f t ω) 0 ^ 2) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).integrable_sq)
    (((Measurable.iSup hm).max measurable_const).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ssb_sup_sq_le_sum (fun t => f t ω)

/-- Averaging out an independent scalar Gaussian can only increase `(max ·)₊²`:
`(maxₜ Bₜ)₊² ≤ 𝔼_γ (maxₜ (Bₜ + dₜ γ))₊²`. (Jensen's inequality in elementary form.) -/
lemma ssb_gamma_jensen {ι : Type*} [Fintype ι] [Nonempty ι] (B d : ι → ℝ)
    (hint : Integrable (fun γ : ℝ => max (⨆ t, B t + d t * γ) 0 ^ 2) (gaussianReal 0 1)) :
    max (⨆ t, B t) 0 ^ 2 ≤ ∫ γ, max (⨆ t, B t + d t * γ) 0 ^ 2 ∂(gaussianReal 0 1) := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := B)
  rw [← ht0]
  rcases le_total (B t0) 0 with hb | hb
  · rw [max_eq_right hb]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact integral_nonneg fun γ => sq_nonneg _
  · rw [max_eq_left hb]
    have hpt : ∀ γ : ℝ, B t0 ^ 2 + 2 * B t0 * d t0 * γ ≤ max (⨆ t, B t + d t * γ) 0 ^ 2 := by
      intro γ
      have h1 : B t0 + d t0 * γ ≤ max (⨆ t, B t + d t * γ) 0 :=
        (le_ciSup (f := fun t => B t + d t * γ) (Set.finite_range _).bddAbove t0).trans
          (le_max_left _ _)
      nlinarith [sq_nonneg (max (⨆ t, B t + d t * γ) 0 - B t0), mul_le_mul_of_nonneg_left h1 hb]
    have hid : Integrable (fun γ : ℝ => γ) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal' 2 (by simp)).integrable (by simp)
    have hlin : Integrable (fun γ : ℝ => B t0 ^ 2 + 2 * B t0 * d t0 * γ) (gaussianReal 0 1) :=
      (integrable_const _).add (hid.const_mul _)
    calc B t0 ^ 2 = ∫ γ, (B t0 ^ 2 + 2 * B t0 * d t0 * γ) ∂(gaussianReal 0 1) := by
          rw [integral_add (integrable_const _) (hid.const_mul _), integral_const,
            integral_const_mul, integral_id_gaussianReal]
          simp
      _ ≤ _ := integral_mono hlin hint hpt

/-- Fubini + Jensen: `𝔼_G (maxₜ Bₜ(G))₊² ≤ 𝔼_{G,γ} (maxₜ Xₜ(G,γ))₊²`. -/
lemma ssb_fubini {ι : Type*} [Fintype ι] [Nonempty ι] {p m : ℕ} (c : ι → Fin p → Fin m → ℝ)
    (d : ι → ℝ) :
    ∫ G, max (⨆ t, ssbLin (c t) G) 0 ^ 2 ∂(gaussianMatrix p m)
      ≤ ∫ ω, max (⨆ t, ssbX (c t) (d t) ω) 0 ^ 2 ∂(ssbP p m) := by
  have hint := ssb_integrable_supsq (μ := ssbP p m) (fun t => ssbX (c t) (d t))
    (fun t => ssb_memLp_X _ _) (fun t => (ssb_continuous_X _ _).measurable)
  rw [integral_prod _ hint]
  have hL := ssb_integrable_supsq (μ := gaussianMatrix p m) (fun t => ssbLin (c t))
    (fun t => ssb_memLp_lin _) (fun t => (ssb_continuous_lin _).measurable)
  refine integral_mono_ae hL hint.integral_prod_left ?_
  filter_upwards [hint.prod_right_ae] with G hG
  exact ssb_gamma_jensen (fun t => ssbLin (c t) G) d hG

lemma ssb_layercake_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω → ℝ)
    (hh : Measurable h) :
    ∫⁻ ω, ENNReal.ofReal (max (h ω) 0 ^ 2) ∂μ
      = ∫⁻ t in Set.Ioi 0, μ {ω | t < h ω} * ENNReal.ofReal (2 * t) := by
  have := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun ω => max (h ω) 0)
    (Filter.Eventually.of_forall fun ω => le_max_right _ _) (hh.max measurable_const).aemeasurable
    (g := fun t => 2 * t) (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
      simp only [Set.mem_Ioi] at ht; linarith))
  have e1 : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, 2 * t = x ^ 2 := by
    intro x
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  simp only [e1] at this
  rw [this]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [Set.mem_Ioi] at ht
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, lt_max_iff]
  constructor
  · rintro (h1 | h1)
    · exact h1
    · exact absurd h1 (not_lt.2 ht.le)
  · exact fun h1 => Or.inl h1

/-- Layer cake: a tail comparison `P(f > t) ≤ Q(g > t)` for `t > 0` gives
`𝔼 f₊² ≤ 𝔼 g₊²`. -/
lemma ssb_layercake_sq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') (f : Ω → ℝ) (g : Ω' → ℝ) (hf : Measurable f)
    (hg : Measurable g) (hfi : Integrable (fun ω => max (f ω) 0 ^ 2) P)
    (hgi : Integrable (fun ω => max (g ω) 0 ^ 2) Q)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < f ω} ≤ Q {ω | t < g ω}) :
    ∫ ω, max (f ω) 0 ^ 2 ∂P ≤ ∫ ω, max (g ω) 0 ^ 2 ∂Q := by
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ssb_layercake_eq P f hf, ssb_layercake_eq Q g hg]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  exact mul_le_mul_left (htail t ht) _


/-! ### The Tropp–Webber comparison processes -/

/-- Euclidean norm of a coordinate vector. -/
noncomputable def ssbN {κ : Type*} [Fintype κ] (x : κ → ℝ) : ℝ := Real.sqrt (∑ k, x k ^ 2)

lemma ssbN_nonneg {κ : Type*} [Fintype κ] (x : κ → ℝ) : 0 ≤ ssbN x := Real.sqrt_nonneg _

lemma ssbN_sq {κ : Type*} [Fintype κ] (x : κ → ℝ) : ∑ k, x k ^ 2 = ssbN x ^ 2 :=
  (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm

lemma ssb_inner_le {κ : Type*} [Fintype κ] (x x' : κ → ℝ) : ∑ k, x k * x' k ≤ ssbN x * ssbN x' :=
  Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The coefficient comparison behind Tropp–Webber's covariance identity
`𝔼 XX' - 𝔼 YY' = (‖x‖‖x'‖ - ⟨x,x'⟩)(‖y‖‖y'‖ - ⟨y,y'⟩) ≥ 0`, in increment form. -/
lemma ssb_coeff_cmp {p m : ℕ} (x x' : Fin p → ℝ) (y y' : Fin m → ℝ) :
    ∑ k, ∑ l, (x k * y l - x' k * y' l) ^ 2 + (ssbN x * ssbN y - ssbN x' * ssbN y') ^ 2
      ≤ ∑ k, (ssbN y * x k - ssbN y' * x' k) ^ 2 + ∑ l, (ssbN x * y l - ssbN x' * y' l) ^ 2 := by
  have hα := ssb_inner_le x x'
  have hβ := ssb_inner_le y y'
  have hL : ∑ k, ∑ l, (x k * y l - x' k * y' l) ^ 2
      = (∑ k, x k ^ 2) * (∑ l, y l ^ 2) - 2 * ((∑ k, x k * x' k) * (∑ l, y l * y' l))
        + (∑ k, x' k ^ 2) * (∑ l, y' l ^ 2) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hR1 : ∑ k, (ssbN y * x k - ssbN y' * x' k) ^ 2
      = ssbN y ^ 2 * (∑ k, x k ^ 2) - 2 * (ssbN y * ssbN y') * (∑ k, x k * x' k)
        + ssbN y' ^ 2 * (∑ k, x' k ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR2 : ∑ l, (ssbN x * y l - ssbN x' * y' l) ^ 2
      = ssbN x ^ 2 * (∑ l, y l ^ 2) - 2 * (ssbN x * ssbN x') * (∑ l, y l * y' l)
        + ssbN x' ^ 2 * (∑ l, y' l ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hL, hR1, hR2, ssbN_sq x, ssbN_sq x', ssbN_sq y, ssbN_sq y']
  nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hβ)]

lemma ssb_append_sq {p m : ℕ} (u : Fin p → ℝ) (w : Fin m → ℝ) :
    ∑ _i : Fin 1, ∑ k : Fin (p + m), Fin.append u w k ^ 2 = ∑ k, u k ^ 2 + ∑ l, w l ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

lemma ssb_append_sub_sq {p m : ℕ} (u u' : Fin p → ℝ) (w w' : Fin m → ℝ) :
    ∑ _i : Fin 1, ∑ k : Fin (p + m), (Fin.append u w k - Fin.append u' w' k) ^ 2
      = ∑ k, (u k - u' k) ^ 2 + ∑ l, (w l - w' l) ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

/-- Coefficients of the comparison process
`Yₜ = ‖yₜ‖ ⟨g, xₜ⟩ + ‖xₜ‖ ⟨h, yₜ⟩`, realized on one Gaussian row `(g, h) ∈ ℝ^{p+m}`. -/
noncomputable def ssbYc {ι : Type*} {p m : ℕ} (x : ι → Fin p → ℝ) (y : ι → Fin m → ℝ) (t : ι) :
    Fin 1 → Fin (p + m) → ℝ :=
  fun _ k => Fin.append (fun k => ssbN (y t) * x t k) (fun l => ssbN (x t) * y t l) k

/-- The Gaussian comparison (Tropp–Webber, proof of Lemma B.1, via Slepian's inequality):
`𝔼_G (maxₜ ⟨xₜ, G yₜ⟩)₊² ≤ 𝔼 (maxₜ Yₜ)₊²`. -/
lemma ssb_main_cmp {ι : Type*} [Fintype ι] [Nonempty ι] {p m : ℕ} (x : ι → Fin p → ℝ)
    (y : ι → Fin m → ℝ) :
    ∫ G, max (⨆ t, ssbLin (fun k l => x t k * y t l) G) 0 ^ 2 ∂(gaussianMatrix p m)
      ≤ ∫ H, max (⨆ t, ssbLin (ssbYc x y t) H) 0 ^ 2 ∂(gaussianMatrix 1 (p + m)) := by
  set c : ι → Fin p → Fin m → ℝ := fun t k l => x t k * y t l with hc
  set d : ι → ℝ := fun t => ssbN (x t) * ssbN (y t) with hd
  refine (ssb_fubini c d).trans ?_
  have hvar : ∀ t, ∫ ω, ssbX (c t) (d t) ω ^ 2 ∂(ssbP p m)
      = ∫ H, ssbLin (ssbYc x y t) H ^ 2 ∂(gaussianMatrix 1 (p + m)) := by
    intro t
    rw [ssb_integral_X_sq, ssb_integral_lin_sq]
    simp only [ssbYc, hc, hd]
    rw [ssb_append_sq]
    have e1 : ∑ k, ∑ l, (x t k * y t l) ^ 2 = (∑ k, x t k ^ 2) * ∑ l, y t l ^ 2 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ k, (ssbN (y t) * x t k) ^ 2 = ssbN (y t) ^ 2 * ∑ k, x t k ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have e3 : ∑ l, (ssbN (x t) * y t l) ^ 2 = ssbN (x t) ^ 2 * ∑ l, y t l ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2, e3, ssbN_sq (x t), ssbN_sq (y t)]
    ring
  have hinc : ∀ s t, ∫ ω, (ssbX (c s) (d s) ω - ssbX (c t) (d t) ω) ^ 2 ∂(ssbP p m)
      ≤ ∫ H, (ssbLin (ssbYc x y s) H - ssbLin (ssbYc x y t) H) ^ 2
          ∂(gaussianMatrix 1 (p + m)) := by
    intro s t
    simp_rw [ssb_X_sub, ssb_lin_sub]
    rw [ssb_integral_X_sq, ssb_integral_lin_sq]
    simp only [ssbYc, hc, hd, Pi.sub_apply]
    rw [ssb_append_sub_sq]
    exact ssb_coeff_cmp (x s) (x t) (y s) (y t)
  have hS := slepian_tail_comparison (fun t => ssbX (c t) (d t)) (fun t => ssbLin (ssbYc x y t))
    (ssb_hasGaussianLaw_X c d) (ssb_hasGaussianLaw_lin _) (fun t => ssb_integral_X _ _)
    (fun t => ssb_integral_lin _) hvar hinc
  refine ssb_layercake_sq _ _ _ _ (Measurable.iSup fun t => (ssb_continuous_X _ _).measurable)
    (Measurable.iSup fun t => (ssb_continuous_lin _).measurable)
    (ssb_integrable_supsq _ (fun t => ssb_memLp_X _ _) fun t => (ssb_continuous_X _ _).measurable)
    (ssb_integrable_supsq _ (fun t => ssb_memLp_lin _) fun t => (ssb_continuous_lin _).measurable)
    fun τ _ => hS τ


/-! ### Deterministic matrix facts -/

lemma ssb_sandwich_entry {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (G : Fin p → Fin m → ℝ) (u : Fin a → ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, u i * (S * Matrix.of G * T) i j * v j
      = ∑ k, ∑ l, ((∑ i, u i * S i k) * (∑ j, T l j * v j)) * G k l := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ({ toFun := fun x => (x.2.2.2, (x.2.2.1, (x.2.1, x.1)))
       invFun := fun x => (x.2.2.2, (x.2.2.1, (x.2.1, x.1)))
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : Fin a × Fin n × Fin m × Fin p ≃ Fin p × Fin m × Fin n × Fin a)
    _ _ fun x => ?_
  simp only [Equiv.coe_fn_mk]
  ring

open scoped Matrix.Norms.L2Operator in
lemma ssb_norm_vecMul_le {a p : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (u : EuclideanSpace ℝ (Fin a))
    (hu : ‖u‖ = 1) : Real.sqrt (∑ k, (∑ i, u i * S i k) ^ 2) ≤ specNorm S := by
  have h := Matrix.l2_opNorm_mulVec Sᵀ u
  rw [hu, mul_one, ← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose] at h
  refine le_of_eq_of_le ?_ h
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

open scoped Matrix.Norms.L2Operator in
lemma ssb_norm_mulVec_le {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) : Real.sqrt (∑ l, (∑ j, T l j * v j) ^ 2) ≤ specNorm T := by
  have h := Matrix.l2_opNorm_mulVec T v
  rw [hv, mul_one] at h
  refine le_of_eq_of_le ?_ h
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Matrix.mulVec, dotProduct]

/-- `⟨x, g⟩ ≤ ‖S g‖` for `x = Sᵀ u`, `‖u‖ = 1`. -/
lemma ssb_vecMul_inner_le {a p : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (u : EuclideanSpace ℝ (Fin a))
    (hu : ‖u‖ = 1) (g : Fin p → ℝ) :
    ∑ k, (∑ i, u i * S i k) * g k ≤ Real.sqrt (∑ i, (∑ k, S i k * g k) ^ 2) := by
  have e : ∑ k, (∑ i, u i * S i k) * g k = ∑ i, u i * (∑ k, S i k * g k) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => u i) (fun i => ∑ k, S i k * g k)
  rw [← ssb_norm_eq_sqrt, hu, one_mul] at h
  exact h

/-- `⟨y, h⟩ ≤ ‖Tᵀ h‖` for `y = T v`, `‖v‖ = 1`. -/
lemma ssb_mulVec_inner_le {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (h : Fin m → ℝ) :
    ∑ l, (∑ j, T l j * v j) * h l ≤ Real.sqrt (∑ j, (∑ l, T l j * h l) ^ 2) := by
  have e : ∑ l, (∑ j, T l j * v j) * h l = ∑ j, v j * (∑ l, T l j * h l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h' := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => v j) (fun j => ∑ l, T l j * h l)
  rw [← ssb_norm_eq_sqrt, hv, one_mul] at h'
  exact h'

/-! ### Bounding the comparison process -/

/-- Minkowski in `L²` for nonnegative functions. -/
lemma ssb_minkowski {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a b : Ω → ℝ)
    (ha0 : ∀ ω, 0 ≤ a ω) (hb0 : ∀ ω, 0 ≤ b ω) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ ω, (a ω + b ω) ^ 2 ∂μ
      ≤ (Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ)) ^ 2 := by
  have hab : ∫ ω, a ω * b ω ∂μ
      ≤ Real.sqrt (∫ ω, a ω ^ 2 ∂μ) * Real.sqrt (∫ ω, b ω ^ 2 ∂μ) := by
    have h2 : ENNReal.ofReal 2 = 2 := by simp
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall ha0) (Filter.Eventually.of_forall hb0)
      (by rw [h2]; exact ha) (by rw [h2]; exact hb)
    simp only [Real.rpow_two] at h
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact h
  have hexp : ∀ ω, (a ω + b ω) ^ 2 = a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2 := fun ω => by ring
  simp_rw [hexp]
  have i1 := ha.integrable_sq
  have i2 : Integrable (fun ω => 2 * (a ω * b ω)) μ := (ha.integrable_mul hb).const_mul 2
  have i3 := hb.integrable_sq
  rw [integral_add (f := fun ω => a ω ^ 2 + 2 * (a ω * b ω)) (i1.add i2) i3, integral_add i1 i2,
    integral_const_mul]
  have hA := Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (a ω) : 0 ≤ ∫ ω, a ω ^ 2 ∂μ)
  have hB := Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (b ω) : 0 ≤ ∫ ω, b ω ^ 2 ∂μ)
  nlinarith [hab]

lemma ssb_lin_left {p m : ℕ} (w : Fin p → ℝ) (H : Fin 1 → Fin (p + m) → ℝ) :
    ∑ k, w k * H 0 (Fin.castAdd m k) = ssbLin (fun _ k => Fin.append w (0 : Fin m → ℝ) k) H := by
  unfold ssbLin; rw [Fin.sum_univ_one, Fin.sum_univ_add]; simp

lemma ssb_lin_right {p m : ℕ} (w : Fin m → ℝ) (H : Fin 1 → Fin (p + m) → ℝ) :
    ∑ l, w l * H 0 (Fin.natAdd p l) = ssbLin (fun _ k => Fin.append (0 : Fin p → ℝ) w k) H := by
  unfold ssbLin; rw [Fin.sum_univ_one, Fin.sum_univ_add]; simp

/-- `𝔼 ∑ᵢ (∑ₖ Wᵢₖ gₖ)² = ‖W‖_F²` for the first block `g` of a Gaussian row. -/
lemma ssb_integral_left_sq {r p m : ℕ} (W : Fin r → Fin p → ℝ) :
    Integrable (fun H : Fin 1 → Fin (p + m) → ℝ => ∑ i, (∑ k, W i k * H 0 (Fin.castAdd m k)) ^ 2)
      (gaussianMatrix 1 (p + m)) ∧
    ∫ H, ∑ i, (∑ k, W i k * H 0 (Fin.castAdd m k)) ^ 2 ∂(gaussianMatrix 1 (p + m))
      = ∑ i, ∑ k, W i k ^ 2 := by
  simp_rw [ssb_lin_left]
  have hi : ∀ i, Integrable (fun H : Fin 1 → Fin (p + m) → ℝ =>
      ssbLin (fun _ k => Fin.append (W i) (0 : Fin m → ℝ) k) H ^ 2) (gaussianMatrix 1 (p + m)) :=
    fun i => (ssb_memLp_lin _).integrable_sq
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ssb_integral_lin_sq, ssb_append_sq]
  simp

lemma ssb_integral_right_sq {r p m : ℕ} (W : Fin r → Fin m → ℝ) :
    Integrable (fun H : Fin 1 → Fin (p + m) → ℝ => ∑ i, (∑ l, W i l * H 0 (Fin.natAdd p l)) ^ 2)
      (gaussianMatrix 1 (p + m)) ∧
    ∫ H, ∑ i, (∑ l, W i l * H 0 (Fin.natAdd p l)) ^ 2 ∂(gaussianMatrix 1 (p + m))
      = ∑ i, ∑ l, W i l ^ 2 := by
  simp_rw [ssb_lin_right]
  have hi : ∀ i, Integrable (fun H : Fin 1 → Fin (p + m) → ℝ =>
      ssbLin (fun _ k => Fin.append (0 : Fin p → ℝ) (W i) k) H ^ 2) (gaussianMatrix 1 (p + m)) :=
    fun i => (ssb_memLp_lin _).integrable_sq
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ssb_integral_lin_sq, ssb_append_sq]
  simp

/-- `√Q` has a finite second moment when `Q ≥ 0` is integrable. -/
lemma ssb_memLp_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Ω → ℝ)
    (hQ0 : ∀ ω, 0 ≤ Q ω) (hQ : Integrable Q μ) (hm : Measurable Q) (c : ℝ) :
    MemLp (fun ω => c * Real.sqrt (Q ω)) 2 μ := by
  refine MemLp.const_mul ?_ c
  refine (memLp_two_iff_integrable_sq (hm.sqrt.aestronglyMeasurable)).2 ?_
  exact hQ.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hQ0 ω)).symm)

/-- The bound on the comparison process: if `‖xₜ‖ ≤ α`, `‖yₜ‖ ≤ β`, `⟨xₜ, g⟩ ≤ ‖S g‖` and
`⟨yₜ, h⟩ ≤ ‖Tᵀ h‖`, then `𝔼 (maxₜ Yₜ)₊² ≤ (β‖S‖_F + α‖T‖_F)²`. -/
lemma ssb_Y_bound {ι : Type*} [Fintype ι] [Nonempty ι] {a p m n : ℕ}
    (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) (x : ι → Fin p → ℝ)
    (y : ι → Fin m → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : ∀ t, ssbN (x t) ≤ α) (hy : ∀ t, ssbN (y t) ≤ β)
    (hxg : ∀ t (g : Fin p → ℝ), ∑ k, x t k * g k ≤ Real.sqrt (∑ i, (∑ k, S i k * g k) ^ 2))
    (hyh : ∀ t (h : Fin m → ℝ), ∑ l, y t l * h l ≤ Real.sqrt (∑ j, (∑ l, T l j * h l) ^ 2)) :
    ∫ H, max (⨆ t, ssbLin (ssbYc x y t) H) 0 ^ 2 ∂(gaussianMatrix 1 (p + m))
      ≤ (β * frobNorm S + α * frobNorm T) ^ 2 := by
  set Q1 : (Fin 1 → Fin (p + m) → ℝ) → ℝ :=
    fun H => ∑ i, (∑ k, S i k * H 0 (Fin.castAdd m k)) ^ 2 with hQ1
  set Q2 : (Fin 1 → Fin (p + m) → ℝ) → ℝ :=
    fun H => ∑ j, (∑ l, (fun j l => T l j) j l * H 0 (Fin.natAdd p l)) ^ 2 with hQ2
  have hQ10 : ∀ H, 0 ≤ Q1 H := fun H => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ20 : ∀ H, 0 ≤ Q2 H := fun H => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ1m : Measurable Q1 := by rw [hQ1]; fun_prop
  have hQ2m : Measurable Q2 := by rw [hQ2]; fun_prop
  obtain ⟨hQ1i, hQ1e⟩ := ssb_integral_left_sq (m := m) S
  obtain ⟨hQ2i, hQ2e⟩ := ssb_integral_right_sq (p := p) (fun j l => T l j)
  have hYle : ∀ H t, ssbLin (ssbYc x y t) H
      ≤ β * Real.sqrt (Q1 H) + α * Real.sqrt (Q2 H) := by
    intro H t
    have e : ssbLin (ssbYc x y t) H
        = ssbN (y t) * (∑ k, x t k * H 0 (Fin.castAdd m k))
          + ssbN (x t) * (∑ l, y t l * H 0 (Fin.natAdd p l)) := by
      unfold ssbLin ssbYc
      rw [Fin.sum_univ_one, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    have h1 := hxg t (fun k => H 0 (Fin.castAdd m k))
    have h2 := hyh t (fun l => H 0 (Fin.natAdd p l))
    have r1 : 0 ≤ Real.sqrt (Q1 H) := Real.sqrt_nonneg _
    have r2 : 0 ≤ Real.sqrt (Q2 H) := Real.sqrt_nonneg _
    have n1 := ssbN_nonneg (y t)
    have n2 := ssbN_nonneg (x t)
    have k1 : ssbN (y t) * (∑ k, x t k * H 0 (Fin.castAdd m k)) ≤ β * Real.sqrt (Q1 H) :=
      (mul_le_mul_of_nonneg_left h1 n1).trans (mul_le_mul_of_nonneg_right (hy t) r1)
    have k2 : ssbN (x t) * (∑ l, y t l * H 0 (Fin.natAdd p l)) ≤ α * Real.sqrt (Q2 H) :=
      (mul_le_mul_of_nonneg_left h2 n2).trans (mul_le_mul_of_nonneg_right (hx t) r2)
    linarith
  have hW0 : ∀ H, 0 ≤ β * Real.sqrt (Q1 H) + α * Real.sqrt (Q2 H) := fun H =>
    add_nonneg (mul_nonneg hβ (Real.sqrt_nonneg _)) (mul_nonneg hα (Real.sqrt_nonneg _))
  have hm1 := ssb_memLp_sqrt Q1 hQ10 hQ1i hQ1m β
  have hm2 := ssb_memLp_sqrt Q2 hQ20 hQ2i hQ2m α
  have hpt : ∀ H, max (⨆ t, ssbLin (ssbYc x y t) H) 0 ^ 2
      ≤ (β * Real.sqrt (Q1 H) + α * Real.sqrt (Q2 H)) ^ 2 := by
    intro H
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le (ciSup_le fun t => hYle H t) (hW0 H)) 2
  have hint := ssb_integrable_supsq (μ := gaussianMatrix 1 (p + m))
    (fun t => ssbLin (ssbYc x y t)) (fun t => ssb_memLp_lin _)
    (fun t => (ssb_continuous_lin _).measurable)
  refine (integral_mono hint (hm1.add hm2).integrable_sq hpt).trans ?_
  refine (ssb_minkowski _ _ _ (fun H => mul_nonneg hβ (Real.sqrt_nonneg _))
    (fun H => mul_nonneg hα (Real.sqrt_nonneg _)) hm1 hm2).trans (le_of_eq ?_)
  have s1 : ∫ H, (β * Real.sqrt (Q1 H)) ^ 2 ∂(gaussianMatrix 1 (p + m)) = β ^ 2 * frobSq S := by
    simp_rw [mul_pow, Real.sq_sqrt (hQ10 _)]
    rw [integral_const_mul]
    congr 1
  have s2 : ∫ H, (α * Real.sqrt (Q2 H)) ^ 2 ∂(gaussianMatrix 1 (p + m)) = α ^ 2 * frobSq T := by
    simp_rw [mul_pow, Real.sq_sqrt (hQ20 _)]
    rw [integral_const_mul]
    congr 1
    rw [hQ2e, frobSq, Finset.sum_comm]
  rw [s1, s2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ,
    Real.sqrt_sq hα]
  rfl


/-! ### Assembly -/

open scoped Matrix.Norms.L2Operator in
lemma ssb_specNorm_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    specNorm (0 : Matrix m n ℝ) = 0 := norm_zero

/-- The bound at a fixed net scale `ε`: `(1 - 2ε)² 𝔼‖SGT‖² ≤ (‖S‖‖T‖_F + ‖S‖_F‖T‖)²`. -/
lemma ssb_scaled_bound {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (ha : 0 < a) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (1 - 2 * ε) ^ 2 * ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by
  -- finite `ε`-nets of the two unit spheres
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).totallyBounded ε hε
  obtain ⟨Fv, hFvS, hFvfin, hFvcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin a)) 1).totallyBounded ε hε
  set I := hFufin.toFinset ×ˢ hFvfin.toFinset with hIdef
  have hI1 : ∀ t ∈ I, ‖t.1‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFuS ht.1
  have hI2 : ∀ t ∈ I, ‖t.2‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFvS ht.2
  have hcov : ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin a)), ‖u‖ = 1 →
      ‖v‖ = 1 → ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε := by
    intro u v hu hv
    have hu' : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa using hu
    have hv' : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin a)) 1 := by simpa using hv
    obtain ⟨y, hy, hyu⟩ := Set.mem_iUnion₂.1 (hFucov hu')
    obtain ⟨z, hz, hzv⟩ := Set.mem_iUnion₂.1 (hFvcov hv')
    refine ⟨(y, z), ?_, ?_, ?_⟩
    · rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact ⟨hy, hz⟩
    · rw [Metric.mem_ball, dist_eq_norm] at hyu; exact hyu.le
    · rw [Metric.mem_ball, dist_eq_norm] at hzv; exact hzv.le
  have hne : Nonempty I := by
    obtain ⟨t, ht, -⟩ := hcov (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1)
      (EuclideanSpace.single (⟨0, ha⟩ : Fin a) 1) (by simp) (by simp)
    exact ⟨⟨t, ht⟩⟩
  -- the vectors `xₜ = Sᵀ uₜ` and `yₜ = T vₜ`
  set x : I → Fin p → ℝ := fun t k => ∑ i, t.1.2 i * S i k with hx
  set y : I → Fin m → ℝ := fun t l => ∑ j, T l j * t.1.1 j with hy
  have hspec : Integrable (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T) ^ 2)
      (gaussianMatrix p m) :=
    (ssb_integrable_of_lip (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T))
      (specNorm S * specNorm T) (mul_nonneg (ssb_specNorm_nonneg S) (ssb_specNorm_nonneg T))
      (ssb_sandwich_lip S T)).2
  have hL := ssb_integrable_supsq (μ := gaussianMatrix p m)
    (fun t => ssbLin (fun k l => x t k * y t l)) (fun t => ssb_memLp_lin _)
    (fun t => (ssb_continuous_lin _).measurable)
  have step1 : ∀ G : Fin p → Fin m → ℝ, (1 - 2 * ε) ^ 2 * specNorm (S * Matrix.of G * T) ^ 2
      ≤ max (⨆ t, ssbLin (fun k l => x t k * y t l) G) 0 ^ 2 := by
    intro G
    have hnet := ssb_net_bound (S * Matrix.of G * T) ε hε.le I hI2 hcov
    have e : (⨆ t : I, ∑ i, ∑ j, t.1.2 i * (S * Matrix.of G * T) i j * t.1.1 j)
        = ⨆ t, ssbLin (fun k l => x t k * y t l) G := by
      congr 1
      funext t
      exact ssb_sandwich_entry S T G (fun i => t.1.2 i) (fun j => t.1.1 j)
    rw [e] at hnet
    have h0 : 0 ≤ (1 - 2 * ε) * specNorm (S * Matrix.of G * T) :=
      mul_nonneg (by linarith) (ssb_specNorm_nonneg _)
    calc (1 - 2 * ε) ^ 2 * specNorm (S * Matrix.of G * T) ^ 2
        = ((1 - 2 * ε) * specNorm (S * Matrix.of G * T)) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ h0 (hnet.trans (le_max_left _ _)) 2
  calc (1 - 2 * ε) ^ 2 * ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      = ∫ G, (1 - 2 * ε) ^ 2 * specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ G, max (⨆ t, ssbLin (fun k l => x t k * y t l) G) 0 ^ 2 ∂(gaussianMatrix p m) :=
        integral_mono (hspec.const_mul _) hL step1
    _ ≤ ∫ H, max (⨆ t, ssbLin (ssbYc x y t) H) 0 ^ 2 ∂(gaussianMatrix 1 (p + m)) :=
        ssb_main_cmp x y
    _ ≤ (specNorm T * frobNorm S + specNorm S * frobNorm T) ^ 2 :=
        ssb_Y_bound S T x y (specNorm S) (specNorm T) (ssb_specNorm_nonneg S)
          (ssb_specNorm_nonneg T)
          (fun t => ssb_norm_vecMul_le S t.1.2 (hI2 _ t.2))
          (fun t => ssb_norm_mulVec_le T t.1.1 (hI1 _ t.2))
          (fun t g => ssb_vecMul_inner_le S t.1.2 (hI2 _ t.2) g)
          (fun t h => ssb_mulVec_inner_le T t.1.1 (hI1 _ t.2) h)
    _ = (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by ring

end GaussianMatrix

open GaussianMatrix

theorem solution {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by
  have hC : 0 ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := sq_nonneg _
  have hzero : (∀ G : Fin p → Fin m → ℝ, specNorm (S * Matrix.of G * T) = 0) →
      ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
        ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by
    intro h0
    have : ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m) = 0 := by simp [h0]
    rw [this]; exact hC
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact hzero fun G => by rw [Subsingleton.elim (S * Matrix.of G * T) 0, ssb_specNorm_zero]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact hzero fun G => by rw [Subsingleton.elim (S * Matrix.of G * T) 0, ssb_specNorm_zero]
  set E := ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m) with hE
  set C := (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 with hCdef
  have hE0 : 0 ≤ E := integral_nonneg fun G => sq_nonneg _
  by_contra hcon
  have hlt : C < E := not_le.1 hcon
  have hEpos : 0 < E := lt_of_le_of_lt hC hlt
  have hε : 0 < (E - C) / (8 * E) := div_pos (by linarith) (by linarith)
  have hε2 : (E - C) / (8 * E) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h := ssb_scaled_bound S T ha hn ((E - C) / (8 * E)) hε hε2
  rw [← hE, ← hCdef] at h
  have h1 : (1 - 4 * ((E - C) / (8 * E))) * E ≤ (1 - 2 * ((E - C) / (8 * E))) ^ 2 * E :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ((E - C) / (8 * E))]) hE0
  have h2 : (1 - 4 * ((E - C) / (8 * E))) * E = (E + C) / 2 := by
    field_simp; ring
  linarith
