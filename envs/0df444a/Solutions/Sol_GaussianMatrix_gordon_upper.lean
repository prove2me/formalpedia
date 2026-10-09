-- Prove2me | solution 1 for GaussianMatrix.gordon_upper
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:31:58.619975+00:00
-- url     : https://prove2.me/submissions/5726d821-f11d-4436-9e5b-b22029b1fa3c

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_specNorm_lipschitz
import Theorems.Thm_GaussianMatrix_sudakov_fernique
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma gu_hasGaussianLaw_pi (κ : Type*) [Fintype κ] :
    HasGaussianLaw (fun x : κ → ℝ => x) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have h := iIndepFun.hasGaussianLaw (P := Measure.pi fun _ : κ => gaussianReal 0 1)
    (X := fun k (x : κ → ℝ) => x k) (fun k => ⟨by
      have := (measurePreserving_eval (fun _ : κ => gaussianReal (0 : ℝ) 1) k).map_eq
      rw [this]; infer_instance⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

lemma gu_hasGaussianLaw_id (p m : ℕ) :
    HasGaussianLaw (fun G : Fin p → Fin m → ℝ => G) (gaussianMatrix p m) := by
  have h := iIndepFun.hasGaussianLaw (P := gaussianMatrix p m)
    (X := fun i (G : Fin p → Fin m → ℝ) => G i) (fun i => ⟨by
      have := (measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) i).map_eq
      unfold gaussianMatrix
      rw [this]
      have := (gu_hasGaussianLaw_pi (Fin m)).isGaussian_map
      rwa [Measure.map_id'] at this⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

lemma gu_measurePreserving_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

lemma gu_memLp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (q : ENNReal) (hq : q ≠ ⊤) :
    MemLp (fun G : Fin p → Fin m → ℝ => G a b) q (gaussianMatrix p m) :=
  (memLp_id_gaussianReal' q hq).comp_measurePreserving (gu_measurePreserving_coord a b)

lemma gu_integral_comp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (f : ℝ → ℝ)
    (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix p m) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (gu_measurePreserving_coord a b).map_eq, integral_map]
  · exact (gu_measurePreserving_coord a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

lemma gu_integral_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ∂(gaussianMatrix p m) = 0 := by
  have := gu_integral_comp_coord a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

lemma gu_integral_coord_sq {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix p m) = 1 := by
  rw [gu_integral_comp_coord a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

lemma gu_integral_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) :
    ∫ G, G a b * G c d ∂(gaussianMatrix p m) = if a = c ∧ b = d then 1 else 0 := by
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simpa [← pow_two] using gu_integral_coord_sq a b
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
    rw [this, gu_integral_coord]
    simp

lemma gu_integrable_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) (k : ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => k * (G a b * G c d)) (gaussianMatrix p m) :=
  ((gu_memLp_coord a b 2 (by simp)).integrable_mul (gu_memLp_coord c d 2 (by simp))).const_mul k


noncomputable def guLin {p m : ℕ} (c : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * G i j

/-- The coefficient-to-form map as a continuous linear map into `ι → ℝ`. -/
noncomputable def guLinCLM {ι : Type*} {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    (Fin p → Fin m → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun t => ∑ i, ∑ j,
    a t i j • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => Fin m → ℝ) i))

lemma gu_hasGaussianLaw_lin {ι : Type*} [Fintype ι] {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    HasGaussianLaw (fun G t => guLin (a t) G) (gaussianMatrix p m) := by
  have h := (gu_hasGaussianLaw_id p m).map_fun (guLinCLM a)
  have e : (fun G t => guLin (a t) G) = fun G => guLinCLM a G := by
    funext G t
    simp [guLinCLM, guLin]
  rw [e]; exact h


lemma gu_integrable_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    Integrable (guLin c) (gaussianMatrix p m) := by
  unfold guLin
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((gu_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _

lemma gu_continuous_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) : Continuous (guLin c) := by
  unfold guLin; fun_prop

lemma gu_integral_lin {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, guLin c G ∂(gaussianMatrix p m) = 0 := by
  unfold guLin
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((gu_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    ((gu_memLp_coord i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, gu_integral_coord, mul_zero]

lemma gu_lin_sub {p m : ℕ} (c d : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    guLin c G - guLin d G = guLin (c - d) G := by
  simp only [guLin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_mul]

lemma gu_integral_lin_sq {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, guLin c G ^ 2 ∂(gaussianMatrix p m) = ∑ i, ∑ j, c i j ^ 2 := by
  have hexp : ∀ G : Fin p → Fin m → ℝ, guLin c G ^ 2 =
      ∑ i, ∑ k, ∑ j, ∑ l, c i j * c k l * (G i j * G k l) := by
    intro G
    unfold guLin
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    gu_integrable_coord_mul i k j l _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    gu_integrable_coord_mul i k j l _]
  rw [Finset.sum_eq_single i]
  · rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      gu_integrable_coord_mul i i j l _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => gu_integrable_coord_mul i i j l _]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, gu_integral_coord_mul]; simp [sq]
    · intro l _ hl
      rw [integral_const_mul, gu_integral_coord_mul]; simp [Ne.symm hl]
    · simp
  · intro k _ hk
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      gu_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => gu_integrable_coord_mul i k j l _]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_const_mul, gu_integral_coord_mul]; simp [Ne.symm hk]
  · simp


/-! ### Deterministic part -/

lemma gu_norm_sq_eq {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ ^ 2 = ∑ j, u j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

lemma gu_norm_eq_sqrt {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ = Real.sqrt (∑ j, u j ^ 2) := by
  rw [← gu_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

open scoped RealInnerProductSpace in
lemma gu_inner_matrix {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n))
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
lemma gu_net_bound {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
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
        (gu_inner_matrix A t.1 t.2).symm
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
      rw [← gu_inner_matrix, ← hΦ, hA]
      simp
    rw [← hMzero]
    simp only [mul_zero]
    rw [hS]
    simp only [hA', Real.iSup_const_zero, le_refl]


/-! ### Probabilistic estimates -/

lemma gu_integrable_iSup {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
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
lemma gu_integral_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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
lemma gu_integral_le_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫ ω, X ω ^ 2 ∂μ ≤ c ^ 2) : ∫ ω, X ω ∂μ ≤ c := by
  rcases hc.lt_or_eq with hc | hc
  · refine (gu_integral_le_of_sq μ X hX hX2 c hc).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / c ≤ c := by
      rw [div_le_iff₀ hc]; nlinarith
    linarith
  · subst hc
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    refine (gu_integral_le_of_sq μ X hX hX2 δ hδ).trans ?_
    have : (∫ ω, X ω ^ 2 ∂μ) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by simpa using h) hδ.le
    linarith


/-- `𝔼 √(∑ⱼ H₀,σ(j)²) ≤ √k` for a family of `k` coordinates of a Gaussian row. -/
lemma gu_integral_sqrt_sumsq_le {k m : ℕ} (σ : Fin k → Fin m) :
    ∫ H, Real.sqrt (∑ j, H 0 (σ j) ^ 2) ∂(gaussianMatrix 1 m) ≤ Real.sqrt k := by
  have hQ : Integrable (fun H : Fin 1 → Fin m → ℝ => ∑ j, H 0 (σ j) ^ 2) (gaussianMatrix 1 m) :=
    integrable_finsetSum _ fun j _ => (gu_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq
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
  refine gu_integral_le_of_integral_sq_le _ _ hS hS2 _ (Real.sqrt_nonneg _) (le_of_eq ?_)
  rw [Real.sq_sqrt (Nat.cast_nonneg k)]
  simp_rw [Real.sq_sqrt (hQ0 _)]
  rw [integral_finsetSum _ fun j _ => (gu_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq]
  simp [gu_integral_coord_sq]

/-- Coefficient comparison for unit vectors:
`‖v uᵀ - v' u'ᵀ‖_F² ≤ ‖u - u'‖² + ‖v - v'‖²`. -/
lemma gu_coeff_ineq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    ∑ i, ∑ j, (v i * u j - v' i * u' j) ^ 2 ≤ ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  have su : ∑ j, u j ^ 2 = 1 := by rw [← gu_norm_sq_eq, hu, one_pow]
  have su' : ∑ j, u' j ^ 2 = 1 := by rw [← gu_norm_sq_eq, hu', one_pow]
  have sv : ∑ i, v i ^ 2 = 1 := by rw [← gu_norm_sq_eq, hv, one_pow]
  have sv' : ∑ i, v' i ^ 2 = 1 := by rw [← gu_norm_sq_eq, hv', one_pow]
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
lemma gu_coeffY_sq {N n : ℕ} (u u' : EuclideanSpace ℝ (Fin n)) (v v' : EuclideanSpace ℝ (Fin N)) :
    ∑ _i : Fin 1, ∑ k : Fin (n + N),
      (Fin.append (fun j => u j) (fun i => v i) k - Fin.append (fun j => u' j) (fun i => v' i) k) ^ 2
      = ∑ j, (u j - u' j) ^ 2 + ∑ i, (v i - v' i) ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

lemma gu_Y_le {N n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (H : Fin 1 → Fin (n + N) → ℝ) :
    guLin (fun _ k => Fin.append (fun j => u j) (fun i => v i) k) H
      ≤ Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2) + Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2) := by
  unfold guLin
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => u j) (fun j => H 0 (Fin.castAdd N j))
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => v i) (fun i => H 0 (Fin.natAdd n i))
  rw [← gu_norm_eq_sqrt, hu, one_mul] at h1
  rw [← gu_norm_eq_sqrt, hv, one_mul] at h2
  exact add_le_add h1 h2


/-! ### Integrability -/

/-- `‖G‖_F² = ∑ᵢⱼ Gᵢⱼ²` is integrable under the Gaussian matrix law. -/
lemma gu_integrable_frobSq (p m : ℕ) :
    Integrable (fun X : Fin p → Fin m → ℝ => frobSq (Matrix.of X)) (gaussianMatrix p m) := by
  unfold frobSq
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp only [Matrix.of_apply]
  exact ((memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving
    (gu_measurePreserving_coord i j)).integrable_sq

lemma gu_frobSq_nonneg {p m : ℕ} (X : Fin p → Fin m → ℝ) : 0 ≤ frobSq (Matrix.of X) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gu_continuous_frobNorm (p m : ℕ) :
    Continuous (fun X : Fin p → Fin m → ℝ => frobNorm (Matrix.of X)) := by
  unfold frobNorm frobSq
  simp only [Matrix.of_apply]
  fun_prop

/-- A function that is `L`-Lipschitz for the Frobenius norm is continuous. -/
lemma gu_continuous_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro X₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun Y : Fin p → Fin m → ℝ => L * frobNorm (Matrix.of (Y - X₀))) :=
    continuous_const.mul ((gu_continuous_frobNorm p m).comp (continuous_id.sub
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
lemma gu_integrable_of_lip {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) :
    Integrable h (gaussianMatrix p m) ∧
      Integrable (fun X => h X ^ 2) (gaussianMatrix p m) := by
  have hcont := gu_continuous_of_lip h L hLip
  have hF := gu_integrable_frobSq p m
  have hbound : ∀ X, |h X| ≤ |h 0| + L * frobNorm (Matrix.of X) := by
    intro X
    have h1 := hLip X 0
    have h2 : Matrix.of X - Matrix.of (0 : Fin p → Fin m → ℝ) = Matrix.of X := by
      ext i j; simp
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub (h X) (h 0)
    linarith
  have hsq : ∀ X : Fin p → Fin m → ℝ, frobNorm (Matrix.of X) ^ 2 = frobSq (Matrix.of X) := fun X =>
    Real.sq_sqrt (gu_frobSq_nonneg X)
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


open scoped Matrix.Norms.L2Operator in
/-- The comparison bound for a fixed net scale: `(1 - 2ε) 𝔼‖G‖ ≤ √N + √n`. -/
lemma gu_scaled_bound {N n : ℕ} (hN : 0 < N) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    (1 - 2 * ε) * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n)
      ≤ Real.sqrt N + Real.sqrt n := by
  -- finite `ε`-nets of the two unit spheres
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).totallyBounded ε hε
  obtain ⟨Fv, hFvS, hFvfin, hFvcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).totallyBounded ε hε
  set I := hFufin.toFinset ×ˢ hFvfin.toFinset with hIdef
  have hI1 : ∀ t ∈ I, ‖t.1‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFuS ht.1
  have hI2 : ∀ t ∈ I, ‖t.2‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFvS ht.2
  have hcov : ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N)), ‖u‖ = 1 →
      ‖v‖ = 1 → ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε := by
    intro u v hu hv
    have hu' : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa using hu
    have hv' : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := by simpa using hv
    obtain ⟨y, hy, hyu⟩ := Set.mem_iUnion₂.1 (hFucov hu')
    obtain ⟨z, hz, hzv⟩ := Set.mem_iUnion₂.1 (hFvcov hv')
    refine ⟨(y, z), ?_, ?_, ?_⟩
    · rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact ⟨hy, hz⟩
    · rw [Metric.mem_ball, dist_eq_norm] at hyu; exact hyu.le
    · rw [Metric.mem_ball, dist_eq_norm] at hzv; exact hzv.le
  have hne : Nonempty I := by
    obtain ⟨t, ht, -⟩ := hcov (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1)
      (EuclideanSpace.single (⟨0, hN⟩ : Fin N) 1) (by simp) (by simp)
    exact ⟨⟨t, ht⟩⟩
  -- the two Gaussian processes indexed by the net
  set a : I → Fin N → Fin n → ℝ := fun t i j => t.1.2 i * t.1.1 j with ha
  set b : I → Fin 1 → Fin (n + N) → ℝ :=
    fun t _ k => Fin.append (fun j => t.1.1 j) (fun i => t.1.2 i) k with hb
  have hinc : ∀ s t : I,
      ∫ G, (guLin (a s) G - guLin (a t) G) ^ 2 ∂(gaussianMatrix N n)
        ≤ ∫ H, (guLin (b s) H - guLin (b t) H) ^ 2 ∂(gaussianMatrix 1 (n + N)) := by
    intro s t
    simp_rw [gu_lin_sub]
    rw [gu_integral_lin_sq, gu_integral_lin_sq]
    simp only [ha, hb, Pi.sub_apply]
    rw [gu_coeffY_sq]
    exact gu_coeff_ineq _ _ _ _ (hI1 _ s.2) (hI1 _ t.2) (hI2 _ s.2) (hI2 _ t.2)
  have hSF := sudakov_fernique (fun t G => guLin (a t) G) (fun t H => guLin (b t) H)
    (gu_hasGaussianLaw_lin a) (gu_hasGaussianLaw_lin b) (fun t => gu_integral_lin _)
    (fun t => gu_integral_lin _) hinc
  -- integrability
  have hspec : Integrable (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A))
      (gaussianMatrix N n) :=
    (gu_integrable_of_lip (fun A : Fin N → Fin n → ℝ => specNorm (Matrix.of A)) 1 zero_le_one
      fun X Y => by rw [one_mul]; exact specNorm_lipschitz (Matrix.of X) (Matrix.of Y)).1
  have hXsup := gu_integrable_iSup (μ := gaussianMatrix N n) (fun t G => guLin (a t) G)
    (fun t => gu_integrable_lin _) (fun t => (gu_continuous_lin _).measurable)
  have hYsup := gu_integrable_iSup (μ := gaussianMatrix 1 (n + N)) (fun t H => guLin (b t) H)
    (fun t => gu_integrable_lin _) (fun t => (gu_continuous_lin _).measurable)
  have hsq : ∀ {k : ℕ} (σ : Fin k → Fin (n + N)), Integrable
      (fun H : Fin 1 → Fin (n + N) → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix 1 (n + N)) := by
    intro k σ
    have hQ : Integrable (fun H : Fin 1 → Fin (n + N) → ℝ => ∑ j, H 0 (σ j) ^ 2)
        (gaussianMatrix 1 (n + N)) :=
      integrable_finsetSum _ fun j _ => (gu_memLp_coord 0 (σ j) 2 (by simp)).integrable_sq
    refine Integrable.mono' ((integrable_const 1).add hQ) (by fun_prop : Continuous
      (fun H : Fin 1 → Fin (n + N) → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun H => ?_)
    have hQ0 : 0 ≤ ∑ j, H 0 (σ j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := Real.sq_sqrt hQ0
    have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]
  -- chain of inequalities
  calc (1 - 2 * ε) * ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n)
      = ∫ A, (1 - 2 * ε) * specNorm (Matrix.of A) ∂(gaussianMatrix N n) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ G, (⨆ t, guLin (a t) G) ∂(gaussianMatrix N n) := by
        refine integral_mono (hspec.const_mul _) hXsup fun G => ?_
        refine (gu_net_bound (Matrix.of G) ε hε.le I hI2 hcov).trans (le_of_eq ?_)
        congr 1
        funext t
        simp only [guLin, ha, Matrix.of_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∫ H, (⨆ t, guLin (b t) H) ∂(gaussianMatrix 1 (n + N)) := hSF
    _ ≤ ∫ H, (Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2)
          + Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2)) ∂(gaussianMatrix 1 (n + N)) := by
        refine integral_mono hYsup ((hsq _).add (hsq _)) fun H => ?_
        exact ciSup_le fun t => gu_Y_le t.1.1 t.1.2 (hI1 _ t.2) (hI2 _ t.2) H
    _ = ∫ H, Real.sqrt (∑ j, H 0 (Fin.castAdd N j) ^ 2) ∂(gaussianMatrix 1 (n + N))
          + ∫ H, Real.sqrt (∑ i, H 0 (Fin.natAdd n i) ^ 2) ∂(gaussianMatrix 1 (n + N)) :=
        integral_add (hsq _) (hsq _)
    _ ≤ Real.sqrt n + Real.sqrt N :=
        add_le_add (gu_integral_sqrt_sumsq_le _) (gu_integral_sqrt_sumsq_le _)
    _ = Real.sqrt N + Real.sqrt n := add_comm _ _

open scoped Matrix.Norms.L2Operator in
lemma gu_specNorm_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    specNorm (0 : Matrix m n ℝ) = 0 := norm_zero

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} :
    ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) ≤ Real.sqrt N + Real.sqrt n := by
  have hs : 0 ≤ Real.sqrt N + Real.sqrt n := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : ∀ A : Fin 0 → Fin n → ℝ, specNorm (Matrix.of A) = 0 := fun A => by
      rw [Subsingleton.elim (Matrix.of A) 0, gu_specNorm_zero]
    simp only [h0, integral_zero]
    exact hs
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ A : Fin N → Fin 0 → ℝ, specNorm (Matrix.of A) = 0 := fun A => by
      rw [Subsingleton.elim (Matrix.of A) 0, gu_specNorm_zero]
    simp only [h0, integral_zero]
    exact hs
  set E := ∫ A, specNorm (Matrix.of A) ∂(gaussianMatrix N n) with hE
  set s := Real.sqrt N + Real.sqrt n
  by_contra hcon
  push Not at hcon
  have hEpos : 0 < E := lt_of_le_of_lt hs hcon
  have h := gu_scaled_bound hN hn ((E - s) / (4 * E)) (div_pos (by linarith) (by linarith))
  rw [← hE] at h
  have : (1 - 2 * ((E - s) / (4 * E))) * E = (E + s) / 2 := by
    field_simp; ring
  rw [this] at h
  linarith
