-- Prove2me | solution 13 for AvramDividend.Classical.local_verification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:38:44.951639+00:00
-- url     : https://prove2.me/submissions/44c348ea-a6de-4dad-b9e4-4543bb6201dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
Direct exact verification of the local HJB milestone's deterministic stage.
The full original-source fixed-horizon stochastic theorem remains the sole
Open import. Expand the integer-horizon supremum and both strategy suprema
within this proof, preserving the canonical Stieltjes dividend definition.
-/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
      (C = ⊤ → ∀ x : ℝ, 0 ≤ x → valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x) := by
    intro x hx hxC D hD n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact admissible_cap_truncated_dividendValue_le
      X hX q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb
      x hx hxC D hD (n : ℝ) hn
  have hStrategy : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
      dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
    intro x hx hxC D hD
    rw [dividendValue_eq_iSup_truncated X q x D hD.1]
    exact iSup_le (hBudget x hx hxC D hD)
  have hCap : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxC
    unfold valueFunctionLe
    refine iSup_le fun D => ?_
    refine iSup_le fun hD => ?_
    exact hStrategy x hx hxC D hD
  refine ⟨hCap, ?_⟩
  intro htop x hx
  have hval := hCap x hx (by rw [htop]; exact le_top)
  rw [htop] at hval
  rw [valueFunctionLe_top_eq_valueFunction] at hval
  exact hval
