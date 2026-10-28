-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_killed_of_shifted_safe_witness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:32:28.731017+00:00
-- url     : https://prove2.me/submissions/b197e687-6f3b-42a5-a120-8f24d729fa12

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_le_shifted_witness
import Theorems.Thm_AvramDividend_Classical_nextRecord_killed_survival_of_shifted_guard

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hNext : ε < X.X (u + T) ω - X.X u ω)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω := by
  have hle := AvramDividend.Classical.nextRecord_upclock_le_shifted_witness X b ε u T ω hAt hNext
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top ENNReal.coe_ne_top hle)
  rw [← hv] at hle ⊢
  exact AvramDividend.Classical.nextRecord_killed_survival_of_shifted_guard X a b ε ha hb hε ω u v T
    hu hv hBefore (ENNReal.coe_le_coe.1 hle) hPost
