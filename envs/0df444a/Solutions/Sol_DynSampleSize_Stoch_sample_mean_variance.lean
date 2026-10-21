-- Prove2me | solution 1 for DynSampleSize.Stoch.sample_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:22:47.439698+00:00
-- url     : https://prove2.me/submissions/4b624224-7537-41b4-8914-d24a22707a16

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory DynSampleSize.Stoch



section meas

variable {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]

lemma dss_memLp_batch (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) :
    MemLp (batchGrad gradℓ n w) 2 (Measure.pi (fun _ : Fin n => P)) := by
  unfold batchGrad
  have h : ∀ i : Fin n, MemLp (fun b : Fin n → Z => gradℓ w (b i)) 2
      (Measure.pi (fun _ : Fin n => P)) := fun i =>
    hgrad.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i)
  have hs := memLp_finsetSum' (s := Finset.univ) (fun i _ => h i)
  have e : (fun b : Fin n → Z => (1 / (n : ℝ)) • ∑ i, gradℓ w (b i)) =
      (1 / (n : ℝ)) • ∑ i : Fin n, fun b : Fin n → Z => gradℓ w (b i) := by
    ext b
    simp
  rw [e]
  exact hs.const_smul _

lemma dss_integral_eval (f : Z → EuclideanSpace ℝ (Fin m)) (hf : AEStronglyMeasurable f P)
    (n : ℕ) (i : Fin n) :
    ∫ b : Fin n → Z, f (b i) ∂(Measure.pi (fun _ : Fin n => P)) = ∫ z, f z ∂P := by
  have hmp := measurePreserving_eval (fun _ : Fin n => P) i
  have h := integral_map (μ := Measure.pi (fun _ : Fin n => P)) (φ := Function.eval i)
    (measurable_pi_apply i).aemeasurable (f := f) (by rw [hmp.map_eq]; exact hf)
  rw [hmp.map_eq] at h
  exact h.symm

lemma dss_integral_batch (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    ∫ b, batchGrad gradℓ n w b ∂(Measure.pi (fun _ : Fin n => P)) = ∫ z, gradℓ w z ∂P := by
  unfold batchGrad
  rw [integral_smul, integral_finsetSum]
  · have h : ∀ i : Fin n, ∫ b : Fin n → Z, gradℓ w (b i) ∂(Measure.pi (fun _ : Fin n => P)) =
        ∫ z, gradℓ w z ∂P := fun i => dss_integral_eval P (gradℓ w) hgrad.1 n i
    simp only [h]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (by omega)), one_smul]
  · intro i _
    exact (hgrad.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => P) i)).integrable one_le_two

end meas

lemma dss_sq_decomp {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → EuclideanSpace ℝ (Fin m)) (hY : MemLp Y 2 μ) :
    ∫ x, ‖Y x‖ ^ 2 ∂μ = ‖∫ x, Y x ∂μ‖ ^ 2 + ∫ x, ‖Y x - ∫ y, Y y ∂μ‖ ^ 2 ∂μ := by
  set c := ∫ x, Y x ∂μ with hc
  have hint : Integrable Y μ := hY.integrable one_le_two
  have hsq : Integrable (fun x => ‖Y x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hY.1).1 hY)
  have hYc : MemLp (fun x => Y x - c) 2 μ := hY.sub (memLp_const c)
  have hsq2 : Integrable (fun x => ‖Y x - c‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hYc.1).1 hYc)
  have hinner : Integrable (fun x => inner ℝ c (Y x - c)) μ :=
    (hint.sub (integrable_const c)).const_inner c
  have hpt : ∀ x, ‖Y x‖ ^ 2 = ‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2 := by
    intro x
    have := norm_add_sq_real c (Y x - c)
    simpa using this
  have hsub : Integrable (fun x => Y x - c) μ := hint.sub (integrable_const c)
  have h0 : ∫ x, inner ℝ c (Y x - c) ∂μ = 0 := by
    have := integral_inner (𝕜 := ℝ) hsub c
    rw [this, integral_sub hint (integrable_const c)]
    simp [hc]
  have e1 : Integrable (fun x => ‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) μ :=
    (integrable_const _).add (hinner.const_mul 2)
  have i1 : ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2) ∂μ =
      (∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) ∂μ) + ∫ x, ‖Y x - c‖ ^ 2 ∂μ :=
    integral_add e1 hsq2
  have i2 : ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) ∂μ =
      (∫ x, ‖c‖ ^ 2 ∂μ) + ∫ x, 2 * inner ℝ c (Y x - c) ∂μ :=
    integral_add (integrable_const _) (hinner.const_mul 2)
  have i3 : ∫ x, 2 * inner ℝ c (Y x - c) ∂μ = 2 * ∫ x, inner ℝ c (Y x - c) ∂μ :=
    integral_const_mul 2 _
  calc ∫ x, ‖Y x‖ ^ 2 ∂μ
      = ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2) ∂μ := by
        congr 1; ext x; exact hpt x
    _ = ‖c‖ ^ 2 + ∫ x, ‖Y x - c‖ ^ 2 ∂μ := by
        rw [i1, i2, i3, h0]
        simp

lemma dss_vecVar_eq {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → EuclideanSpace ℝ (Fin m)) (hY : MemLp Y 2 μ) :
    vecVar μ Y = ∑ k, variance (fun x => Y x k) μ := by
  have hk : ∀ k, MemLp (fun x => Y x k) 2 μ := fun k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).comp_memLp' hY
  have hmean : ∀ k, (∫ x, Y x ∂μ) k = ∫ x, Y x k ∂μ := fun k => by
    have := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).integral_comp_comm
      (hY.integrable one_le_two)
    simpa using this.symm
  unfold vecVar
  have e : ∀ x, ‖Y x - ∫ y, Y y ∂μ‖ ^ 2 = ∑ k, (Y x k - ∫ y, Y y k ∂μ) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, hmean k]
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [variance_eq_integral (hk k).aemeasurable]
  · intro k _
    exact ((hk k).sub (memLp_const _)).integrable_sq

lemma dss_smv {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) =
      vecVar P (gradℓ w) / n := by
  rw [dss_vecVar_eq _ _ (dss_memLp_batch P gradℓ w hgrad n), dss_vecVar_eq P _ hgrad,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hX : MemLp (fun z => gradℓ w z k) 2 P :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).comp_memLp' hgrad
  have e : (fun b : Fin n → Z => batchGrad gradℓ n w b k) =
      (1 / (n : ℝ)) • ∑ i : Fin n, fun b : Fin n → Z => gradℓ w (b i) k := by
    ext b
    simp [batchGrad, Finset.sum_apply]
  rw [e, variance_smul, variance_sum_pi (X := fun _ : Fin n => fun z => gradℓ w z k)
    (fun _ => hX)]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem solution {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P]
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) ≤
      vecVar P (gradℓ w) / n :=
  (dss_smv P gradℓ w hgrad n hn).le
