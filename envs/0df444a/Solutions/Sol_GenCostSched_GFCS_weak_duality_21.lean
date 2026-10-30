-- Prove2me | solution 1 for GenCostSched.GFCS.weak_duality_21
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:29:59.569984+00:00
-- url     : https://prove2.me/submissions/b4ec80a0-7e99-4e34-b273-79355dae8767

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

open GenCostSched.GFCS in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (a : Fin n → ℝ) (β : ℝ → ℝ)
    (hfeas : I.IsDualFeas a β) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (I.dualObj c a β) ≤ I.optLP c := by
  obtain ⟨hβint, ha0, hβ0, hcon⟩ := hfeas
  have hr0 : ∀ j, 0 ≤ I.r j := fun j => (hI.1 j).2.1
  have hg0 : ∀ j t, I.r j ≤ t → 0 ≤ I.g j t := fun j => (hI.1 j).2.2.1
  have hv0 : ∀ j, 0 < I.v j := fun j => (hI.1 j).1
  have hBnn : 0 ≤ ∫ t in Ici 0, β t := by
    apply setIntegral_nonneg_of_ae_restrict
    exact (ae_restrict_iff' measurableSet_Ici).2 (hβ0.mono fun t ht ht0 => ht (mem_Ici.1 ht0))
  have hBeq : ENNReal.ofReal (∫ t in Ici 0, β t) = ∫⁻ t in Ici 0, ENNReal.ofReal (β t) := by
    apply ofReal_integral_eq_lintegral_ofReal hβint
    exact (ae_restrict_iff' measurableSet_Ici).2 (hβ0.mono fun t ht ht0 => ht (mem_Ici.1 ht0))
  unfold Instance.optLP
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxm, hxnn, hx0, hxc, hxv⟩ := hx
  -- per-job inequality
  set F : Fin n → ℝ → ℝ≥0∞ := fun j t => ENNReal.ofReal (β t) * ENNReal.ofReal (x j t) with hF
  have hFm : ∀ j, AEMeasurable (F j) (volume.restrict (Ici 0)) := fun j =>
    (hβint.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mul
      ((hxm j).ennreal_ofReal.aemeasurable)
  have hjob : ∀ j, ENNReal.ofReal (a j * I.v j) ≤
      (∫⁻ t in Ici 0, F j t) + ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) := by
    intro j
    calc ENNReal.ofReal (a j * I.v j) = ENNReal.ofReal (a j) * ENNReal.ofReal (I.v j) :=
          ENNReal.ofReal_mul (ha0 j)
      _ ≤ ENNReal.ofReal (a j) * ∫⁻ t, ENNReal.ofReal (x j t) := by gcongr; exact hxv j
      _ = ∫⁻ t, ENNReal.ofReal (a j) * ENNReal.ofReal (x j t) := by
          rw [lintegral_const_mul _ (hxm j).ennreal_ofReal]
      _ ≤ ∫⁻ t, ((Ici (0:ℝ)).indicator (F j) t + ENNReal.ofReal (I.g j t * x j t)) := by
          apply lintegral_mono_ae
          filter_upwards [hcon j, hβ0] with t h1 h2
          by_cases htr : I.r j ≤ t
          · have ht0 : 0 ≤ t := (hr0 j).trans htr
            rw [indicator_of_mem (mem_Ici.2 ht0)]
            have hb := h2 ht0
            have hle := h1 htr
            rw [← ENNReal.ofReal_mul (ha0 j)]
            simp only [hF]
            rw [← ENNReal.ofReal_mul hb]
            calc ENNReal.ofReal (a j * x j t) ≤ ENNReal.ofReal (β t * x j t + I.g j t * x j t) := by
                  apply ENNReal.ofReal_le_ofReal
                  nlinarith [hxnn j t]
              _ ≤ _ := ENNReal.ofReal_add_le
          · rw [hx0 j t (lt_of_not_ge htr)]; simp
      _ = (∫⁻ t in Ici 0, F j t) + ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) := by
          rw [lintegral_add_left' ((aemeasurable_indicator_iff measurableSet_Ici).2 (hFm j)),
            lintegral_indicator measurableSet_Ici]
  have hsum : ENNReal.ofReal (∑ j, a j * I.v j) ≤
      (∑ j, ∫⁻ t in Ici 0, F j t) + I.cost x := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (ha0 j) (hv0 j).le)]
    unfold Instance.cost offCost
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hjob j
  have hFsum : ∑ j, ∫⁻ t in Ici 0, F j t ≤ ENNReal.ofReal (c * ∫ t in Ici 0, β t) := by
    rw [← lintegral_finsetSum' _ (fun j _ => hFm j), ENNReal.ofReal_mul hc.le, hBeq,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro t
    simp only [hF]
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hxnn j t), mul_comm]
    gcongr
    exact hxc t
  have key : ENNReal.ofReal (∑ j, a j * I.v j) ≤
      ENNReal.ofReal (c * ∫ t in Ici 0, β t) + I.cost x :=
    hsum.trans (add_le_add hFsum le_rfl)
  unfold Instance.dualObj
  rw [ENNReal.ofReal_sub _ (mul_nonneg hc.le hBnn)]
  exact tsub_le_iff_left.2 key
