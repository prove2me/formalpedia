-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:16:40.605082+00:00
-- url     : https://prove2.me/submissions/dd9f5b2e-b961-4aca-8dd7-b39d108d2c98

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_uniform_secant_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A uniformly bounded q-scale family is Lipschitz in the discount on [0,Q]. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q))
    (x : ℝ) (hx : 0 < x) :
    ∀ a ∈ Icc (0 : ℝ) Q, ∀ b ∈ Icc (0 : ℝ) Q,
      |W b x - W a x| ≤ |b - a| *
        ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) := by
  have hWQ : IsScaleFunction X Q (W Q) := hW Q ⟨hQ, le_rfl⟩
  intro a ha b hb
  rcases lt_trichotomy a b with hab | heq | hba
  · have hs := unbounded_scale_discount_uniform_secant_bound
      X hnbv a b Q ha.1 hb.1 hQ hab hb.2
      (W a) (W b) (W Q) (hW a ha) (hW b hb) hWQ x hx
    calc
      |W b x - W a x| = W b x - W a x := abs_of_nonneg hs.1
      _ ≤ (b - a) *
        ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) := hs.2
      _ = |b - a| *
        ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hab.le)]
  · subst b
    simp
  · have hs := unbounded_scale_discount_uniform_secant_bound
      X hnbv b a Q hb.1 ha.1 hQ hba ha.2
      (W b) (W a) (W Q) (hW b hb) (hW a ha) hWQ x hx
    calc
      |W b x - W a x| = |W a x - W b x| := abs_sub_comm _ _
      _ = W a x - W b x := abs_of_nonneg hs.1
      _ ≤ (a - b) *
        ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) := hs.2
      _ = |b - a| *
        ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hba.le)]
        ring
