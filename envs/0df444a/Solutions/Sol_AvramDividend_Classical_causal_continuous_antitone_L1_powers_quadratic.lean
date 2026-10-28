-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuous_antitone_L1_powers_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:33:04.572402+00:00
-- url     : https://prove2.me/submissions/c8bc35d2-62a4-4ff4-beca-40078a61dc5a

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_antitone_powers_quadratic_pointwise_of_measurable_recursion
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Integrable continuous powers satisfy the measurable antitone quadratic bound interface. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hKpoint : ∀ x : ℝ, 0 < x → κ x ≤ ρ / x)
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hKL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hKmass : ∀ y : ℝ, 0 < y → (∫ t in (0 : ℝ)..y, κ t) ≤ ρ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      F (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ F n t)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFmass : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ s in (0 : ℝ)..u, F n s) ≤ ρ ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by
  have hKinterval : ∀ y : ℝ, 0 < y →
      IntervalIntegrable κ volume 0 y := by
    intro y hy
    exact causal_positive_L1_intervalIntegrable κ hKL1 y hy
  have hFinterval : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      IntervalIntegrable (F n) volume 0 u := by
    intro n u hu
    rcases lt_or_eq_of_le hu with hpos | hzero
    · exact causal_positive_L1_intervalIntegrable (F n) (hFL1 n) u hpos
    · subst u
      exact IntervalIntegrable.refl
  have hKleftMeas : ∀ x u : ℝ, 0 < u → u < x →
      AEStronglyMeasurable (fun s : ℝ => κ (x - s))
        (volume.restrict (Ioc (0 : ℝ) u)) := by
    intro x u hu hux
    have hmap : MapsTo (fun s : ℝ => x - s)
        (Ioc (0 : ℝ) u) (Ioi (0 : ℝ)) := by
      intro s hs
      exact (mem_Ioi).2 (sub_pos.mpr (lt_of_le_of_lt hs.2 hux))
    have hcsub : ContinuousOn (fun s : ℝ => x - s)
        (Ioc (0 : ℝ) u) :=
      (continuous_const.sub continuous_id).continuousOn
    have hc : ContinuousOn (fun s : ℝ => κ (x - s))
        (Ioc (0 : ℝ) u) := by
      exact hκcont.comp hcsub hmap
    exact hc.aestronglyMeasurable measurableSet_Ioc
  have hFrightMeas : ∀ n : ℕ, ∀ x u : ℝ, 0 < u → u < x →
      AEStronglyMeasurable (F n) (volume.restrict (Ioc u x)) := by
    intro n x u hu hux
    have hsub : Ioc u x ⊆ Ioi (0 : ℝ) := by
      intro s hs
      exact (mem_Ioi).2 (lt_trans hu hs.1)
    exact ((hFL1 n).mono_set hsub).aestronglyMeasurable
  exact causal_antitone_powers_quadratic_pointwise_of_measurable_recursion
    κ F ρ hρ hanti hKpoint hKnonneg hKinterval hKmass
    hzero hsucc hFnonneg hFinterval hFmass hKleftMeas hFrightMeas