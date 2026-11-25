-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLargePrime_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:44.81622+00:00
-- url     : https://prove2.me/submissions/839eeedd-bf08-4b25-9183-68dd640e93f1

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_mul_lstar_le_b
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsBasic_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_kmax_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLJ_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_add_one_lt_lJ
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
private theorem size_bounds_of_large {P : Par} (H : P.Hyp) (G : P.Large) :
    P.S + P.η < P.lstar ∧ 2 * P.η + P.t + 8 * (P.b / P.lstar) + 7 < P.lstar ∧
      2 * P.lstar ≤ P.b ∧ 0 < P.b / P.lstar ∧ (P.kmax : ℝ) ≤ 2 * (P.b / P.lstar) ∧
      P.h = P.b + P.S + P.η + P.t + 1 ∧ 0 ≤ P.η ∧ (P.t : ℝ) ≤ P.η ∧ 0 ≤ P.S ∧ 0 < P.lstar := by
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have hb' := H.b'_pos
  have hbl := b_div_lstar_pos H G
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  exact ⟨by linarith, by linarith, two_mul_lstar_le_b H G, hbl, kmax_le H G, rfl, eta_nonneg' H,
    H.t_le, H.S_nonneg, lstar_pos H G⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : Elem_d := by
  intro P H G l hl
  have nb := natBounds H
  have hb := b_pos' P
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  have hJ := lstar_add_one_lt_lJ H G
  have hLJ := paramsLJ_holds P H G
  have hbasic := paramsBasic_holds P H G
  have hl1 : P.lstar ≤ (l : ℝ) - 1 := by linarith
  have hl1p : 0 < (l : ℝ) - 1 := by linarith
  have hq : P.h / ((l : ℝ) - 1) ≤ 2 * P.b / P.lstar := by
    rw [div_le_div_iff₀ hl1p a10]
    nlinarith [mul_le_mul_of_nonneg_right hbasic.2.2 a10.le,
      mul_le_mul_of_nonneg_left hl1 (by linarith : (0 : ℝ) ≤ 2 * P.b)]
  have hkap : (P.kap l : ℝ) ≤ 2 * P.b / P.lstar := by
    have h0 : 0 ≤ P.h / ((l : ℝ) - 1) := div_nonneg (by linarith) hl1p.le
    exact le_trans (Nat.floor_le h0) hq
  have e2 : 2 * P.b / P.lstar = 2 * (P.b / P.lstar) := by ring
  have hkapmax : P.kap l ≤ P.kmax := Nat.floor_mono hq
  have hNr := nb.nr
  refine ⟨hl1, hkap, hkapmax, ?_, by linarith, ?_, by linarith [nb.kt, nb.m1], ?_⟩
  · have : (P.t : ℝ) + 2 * (P.kap l : ℝ) < l := by linarith
    exact_mod_cast this
  · have : (P.Nr : ℝ) + 1 < l := by linarith [nb.mlek, nb.kt]
    exact_mod_cast this
  · have hl0 : 0 < P.lJ := by linarith
    have := mul_self_lt_mul_self hl0.le hl
    linarith [hLJ.2.1, hLJ.2.2.1]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
