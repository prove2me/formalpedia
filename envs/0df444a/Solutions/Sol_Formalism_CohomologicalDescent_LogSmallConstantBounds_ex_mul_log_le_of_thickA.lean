-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.ex_mul_log_le_of_thickA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:14.418032+00:00
-- url     : https://prove2.me/submissions/47d6c5af-787c-4fab-aafc-412079e806c9

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_choose_two_le_sq_div_two
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_h_bounds
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
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThickA P) {τ : ι} (hτ : τ ∈ D.T2) {l : ℕ} (hl : l.Prime) :
    (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr : ℝ) ^ 2 * P.L := by
  obtain ⟨_, h2, _⟩ := hA τ hτ l hl
  obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
  have hC := choose_two_le_sq_div_two P.Nr
  have hL := G.L_ge
  calc (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr.choose 2 : ℝ) * Real.log P.h := h2
    _ ≤ ((P.Nr : ℝ) ^ 2 / 2) * (P.L + 7 / 10) := mul_le_mul hC c2 c1.le (by positivity)
    _ ≤ (P.Nr : ℝ) ^ 2 * P.L := by
        nlinarith [mul_nonneg (sq_nonneg (P.Nr : ℝ)) (by linarith : (0 : ℝ) ≤ P.L / 2 - 7 / 20)]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
