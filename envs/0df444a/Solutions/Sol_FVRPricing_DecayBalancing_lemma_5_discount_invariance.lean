-- Prove2me | solution 1 for FVRPricing.DecayBalancing.lemma_5_discount_invariance
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:42:36.788198+00:00
-- url     : https://prove2.me/submissions/11c88cde-dfce-47ad-a916-12942a06bfb9

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

open MeasureTheory ProbabilityTheory FVRPricing.DecayBalancing

lemma fvr5_subst (c : ℝ) (hc : 0 < c) (G : ℝ → ENNReal) :
    ∫⁻ y, G y = ENNReal.ofReal c * ∫⁻ t, G (c * t) := by
  have h1 : ∫⁻ t, G (c * t) = ∫⁻ y, G y ∂(Measure.map (c * ·) volume) := by
    have := lintegral_map_equiv (μ := (volume : Measure ℝ)) G (MeasurableEquiv.mulLeft₀ c hc.ne')
    rw [MeasurableEquiv.coe_mulLeft₀] at this
    exact this.symm
  rw [h1, Real.map_volume_mul_left hc.ne', lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

lemma fvr5_subst_Ioc (c : ℝ) (hc : 0 < c) (u v : ℝ) (H : ℝ → ENNReal) :
    ∫⁻ β in Set.Ioc (c * u) (c * v), H β = ENNReal.ofReal c * ∫⁻ t in Set.Ioc u v, H (c * t) := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    fvr5_subst c hc]
  congr 1
  refine lintegral_congr (fun t => ?_)
  have hmem : c * t ∈ Set.Ioc (c * u) (c * v) ↔ t ∈ Set.Ioc u v := by
    simp only [Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(mul_lt_mul_iff_right₀ hc).mp h1, (mul_le_mul_iff_right₀ hc).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mul_lt_mul_iff_right₀ hc).mpr h1, (mul_le_mul_iff_right₀ hc).mpr h2⟩
  by_cases ht : t ∈ Set.Ioc u v
  · rw [Set.indicator_of_mem (hmem.mpr ht), Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem (fun h => ht (hmem.mp h)), Set.indicator_of_notMem ht]

lemma fvr5_bClock (α b μ : ℝ) (hα : 0 < α) (hμ : 0 < μ) {x : ℕ} (e : Fin x → ℝ) (j : ℕ) :
    bClock (α * b) μ e j = α * bClock b (α * μ) e j := by
  unfold bClock
  field_simp

lemma fvr5_pathRevenue (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ)
    (a b μ : ℝ) (e : Fin x → ℝ) :
    pathRevenue f α π π x a b (α * μ) e =
      pathRevenue f 1 (fun x a b => π x a (b / α)) (fun x a b => π x a (b / α)) x a (α * b) μ e := by
  unfold pathRevenue
  by_cases hμ : μ ≤ 0
  · rw [if_pos hμ, if_pos (mul_nonpos_of_nonneg_of_nonpos hα.le hμ)]
  push Not at hμ
  rw [if_neg (not_le.mpr (mul_pos hα hμ)), if_neg (not_le.mpr hμ)]
  have hsd : ∀ j, stageDuration f (fun x a b => π x a (b / α)) x a (α * b) μ e j =
      ENNReal.ofReal α * stageDuration f π x a b (α * μ) e j := by
    intro j
    unfold stageDuration
    rw [fvr5_bClock α b μ hα hμ, fvr5_bClock α b μ hα hμ, fvr5_subst_Ioc α hα]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [mul_div_cancel_left₀ _ hα.ne']
  have hst : ∀ k, saleTime f (fun x a b => π x a (b / α)) x a (α * b) μ e k =
      ENNReal.ofReal α * saleTime f π x a b (α * μ) e k := by
    intro k
    unfold saleTime
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hsd j)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hst, fvr5_bClock α b μ hα hμ]
  simp only [mul_div_cancel_left₀ _ hα.ne']
  congr 1
  unfold disc
  set T := saleTime f π x a b (α * μ) e ((j : ℕ) + 1)
  by_cases hT : T = ⊤
  · rw [if_pos hT, if_pos (by rw [hT]; exact ENNReal.mul_top (by simpa using hα))]
  · have hT' : ENNReal.ofReal α * T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT
    rw [if_neg hT, if_neg hT', ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le, one_mul]

lemma fvr5_gammaPDF (α a b μ : ℝ) (hα : 0 < α) (hb : 0 < b) :
    ENNReal.ofReal α * gammaPDF a b (α * μ) = gammaPDF a (α * b) μ := by
  by_cases hμ : μ < 0
  · rw [gammaPDF_of_neg hμ, gammaPDF_of_neg (mul_neg_of_pos_of_neg hα hμ), mul_zero]
  push Not at hμ
  rw [gammaPDF_of_nonneg hμ, gammaPDF_of_nonneg (mul_nonneg hα.le hμ), ← ENNReal.ofReal_mul hα.le]
  congr 1
  rw [Real.mul_rpow hα.le hμ, Real.mul_rpow hα.le hb.le, Real.rpow_sub_one hα.ne']
  have : -(b * (α * μ)) = -(α * b * μ) := by ring
  rw [this]
  field_simp

lemma fvr5_Jpi (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b : ℝ)
    (hb : 0 < b) :
    Jpi f α π x a b = Jpi f 1 (fun x a b => π x a (b / α)) x a (α * b) := by
  unfold Jpi gammaMeasure
  have hm : ∀ c d : ℝ, Measurable (gammaPDF c d) := fun c d =>
    (measurable_gammaPDFReal c d).ennreal_ofReal
  have hfin : ∀ c d : ℝ, ∀ᵐ y ∂(volume : Measure ℝ), gammaPDF c d y < ⊤ := fun c d =>
    Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (hm a b) (hfin a b),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (hm a (α * b)) (hfin a (α * b)),
    fvr5_subst α hα, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun μ => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, fvr5_gammaPDF α a b μ hα hb]
  congr 1
  refine lintegral_congr (fun e => ?_)
  exact fvr5_pathRevenue f α hα π x a b μ e

theorem solution (f : ℝ → ℝ) (h1 : Assumption1 f)
    (π : ℕ → ℝ → ℝ → ℝ) (hπ : IsPolicy π) (α : ℝ) (hα : 0 < α) (x : ℕ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    Jpi f α π x a b = Jpi f 1 (fun x a b => π x a (b / α)) x a (α * b) ∧
    Jstar f α x a b = Jstar f 1 x a (α * b) := by
  refine ⟨fvr5_Jpi f α hα π x a b hb, ?_⟩
  unfold Jstar
  simp_rw [fvr5_Jpi f α hα _ x a b hb]
  apply le_antisymm
  · refine iSup₂_le (fun σ hσ => ?_)
    have hσ' : IsPolicy (fun x a b => σ x a (b / α)) := by
      refine ⟨fun n => ?_, fun n a b => hσ.2 n a _⟩
      exact (hσ.1 n).comp (measurable_fst.prodMk (measurable_snd.div_const α))
    exact le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
      Jpi f 1 π x a (α * b)) _ hσ'
  · refine iSup₂_le (fun σ hσ => ?_)
    have hσ' : IsPolicy (fun x a b => σ x a (α * b)) := by
      refine ⟨fun n => ?_, fun n a b => hσ.2 n a _⟩
      exact (hσ.1 n).comp (measurable_fst.prodMk (measurable_snd.const_mul α))
    have := le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
      Jpi f 1 (fun x a b => π x a (b / α)) x a (α * b)) _ hσ'
    have heq : (fun x a b => σ x a (α * (b / α))) = σ := by
      funext x a b; rw [mul_div_cancel₀ _ hα.ne']
    rw [heq] at this
    exact this
