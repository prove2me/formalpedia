-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.small_terms_le_of_log_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:24.52357+00:00
-- url     : https://prove2.me/submissions/c98a4a30-54d4-47d8-8068-f064c514a372

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_h_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_h_add_Nr_bounds
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
private theorem log_h_pos_and_le {P : Par} (H : P.Hyp) (G : P.Large) :
    0 < Real.log P.h ∧ Real.log P.h ≤ P.L + 7 / 10 := by
  obtain ⟨h1, h2⟩ := log_h_bounds H G
  have d : (0.7 : ℝ) = 7 / 10 := by norm_num
  rw [d] at h2
  exact ⟨h1, h2⟩
private theorem h_add_Nr_bounds_and_log_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    1 < P.h + (P.Nr : ℝ) ∧ P.h + (P.Nr : ℝ) ≤ 3 * P.b ∧
      0 < Real.log (P.h + (P.Nr : ℝ)) ∧ Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 11 / 10 := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h_add_Nr_bounds H G
  have d : (1.1 : ℝ) = 11 / 10 := by norm_num
  rw [d] at h4
  exact ⟨h1, h2, h3, h4⟩
private theorem log_four_le' : Real.log 4 ≤ 139 / 100 := by
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have := Real.log_two_lt_d9
  norm_num at this
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) (s3 s4 : ℝ)
    (h3 : s3 ≤ Real.log (P.h + (P.Nr : ℝ)) + Real.log 4) (h4 : s4 ≤ (P.S + 1) * Real.log P.h) :
    (P.k : ℝ) * P.S * s3 + (P.k : ℝ) * s4 ≤ 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) := by
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hS := H.S_nonneg
  obtain ⟨_, _, _, hl1⟩ := h_add_Nr_bounds_and_log_bounds H G
  obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
  have h4' := log_four_le'
  have hL := G.L_ge
  have a1 : (P.k : ℝ) * P.S * s3 ≤ (P.k : ℝ) * P.S * (P.L + 249 / 100) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hk0 hS)
  have a2 : (P.k : ℝ) * s4 ≤ (P.k : ℝ) * ((P.S + 1) * (P.L + 7 / 10)) :=
    mul_le_mul_of_nonneg_left (h4.trans (mul_le_mul_of_nonneg_left c2 (by linarith))) hk0
  nlinarith [mul_nonneg hk0 (show (0 : ℝ) ≤ 81 / 100 * P.S + P.L + 33 / 10 by linarith)]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
