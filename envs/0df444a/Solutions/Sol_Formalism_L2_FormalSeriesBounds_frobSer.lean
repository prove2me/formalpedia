-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.frobSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:08:52.795007+00:00
-- url     : https://prove2.me/submissions/74cd6a19-1676-45e4-9012-38d5a7e92271

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_mm_of_mul_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open FrobP
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : FrobSerSt := by
  intro C _ V σ f hf μ ⟨i, hi⟩
  have hpos : 1 ≤ μ i := by
    rcases Nat.eq_zero_or_pos (μ i) with h0 | h0
    · rw [h0] at hi
      exact absurd (dvd_zero _) hi
    · exact h0
  have h1 := hf i (μ - Finsupp.single i 1)
  rw [MvPowerSeries.coeff_pderiv] at h1
  have e1 : μ - Finsupp.single i 1 + Finsupp.single i 1 = μ :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hpos)
  have e2 : (μ - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = μ i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  rw [e1] at h1
  have e3 : (((μ - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : C) + 1 = ((μ i : ℕ) : C) := by
    rw [← e2]
    push_cast
    ring
  rw [e3] at h1
  exact FrobP.mm_of_mul_nat hi h1
end Formalism.L2.FormalSeriesBounds
