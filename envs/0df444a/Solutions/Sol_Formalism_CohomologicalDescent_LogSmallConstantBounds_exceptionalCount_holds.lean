-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.exceptionalCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:23.07394+00:00
-- url     : https://prove2.me/submissions/eee364f6-5b2f-48c4-8e12-24a9b6dd7c53

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_pos
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_add_one_lt_lJ
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_exceptionalRange_holds
import Theorems.Thm_Formalism_CohomologicalDescent_largePrimeDivisorCount_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
private theorem toNat_cast_le_of_le {a : ℤ} {r : ℝ} (h : (a : ℝ) ≤ r) (hr : 0 ≤ r) : ((a.toNat : ℕ) : ℝ) ≤ r := by
  rcases le_or_gt 0 a with h0 | h0
  · have e : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
    have e' : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast e
    rw [e']
    exact h
  · have : a.toNat = 0 := by omega
    rw [this, Nat.cast_zero]
    exact hr
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : ExceptionalCount := by
  intro P H G Q hQ
  have hJ0 : 0 ≤ P.lJ := by linarith [lstar_add_one_lt_lJ H G, lstar_pos H G]
  have hP : ∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ∃ n ∈ Finset.Icc
      ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉
      ⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋, (l : ℤ) ∣ n := by
    intro l hl
    obtain ⟨hp, hlt, z, hz1, hz2, hz3⟩ := hQ l hl
    exact ⟨hp, hlt, z, Finset.mem_Icc.2 ⟨Int.ceil_le.2 hz1, Int.le_floor.2 hz2⟩, hz3⟩
  have hTT : ∀ n ∈ Finset.Icc
      ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉
      ⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋,
      n ≠ 0 ∧ ((|n| : ℤ) : ℝ) < P.lJ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨h1, h2⟩ := exceptionalRange_holds P H G n (Int.ceil_le.1 hn.1) (Int.le_floor.1 hn.2)
    refine ⟨h1.ne', ?_⟩
    rw [abs_of_pos h1]
    exact h2
  have hc := Formalism.CohomologicalDescent.largePrimeDivisorCount_holds P.lJ _ Q hJ0 hTT hP
  rw [Int.card_Icc] at hc
  have hcR : (Q.card : ℝ) ≤ ((⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋ + 1
      - ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉).toNat : ℝ) := by exact_mod_cast hc
  have hfl := Int.floor_le (P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ))
  have hce := Int.le_ceil (P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ))
  have hS := H.S_nonneg
  have hη := eta_nonneg' H
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ P.kmax := Nat.cast_nonneg _
  have hfin := toNat_cast_le_of_le (a := ⌊P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ)⌋ + 1
      - ⌈P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ)⌉)
      (r := P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 1) (by push_cast; linarith) (by linarith)
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
