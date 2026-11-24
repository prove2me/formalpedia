-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.q_j_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:47:02.558381+00:00
-- url     : https://prove2.me/submissions/e89c24e6-2e6f-4fac-94f5-2abc182c16f9

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} {ι : Type} {D : SizeData₂ ι} (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) :
    (D.q τ : ℝ) ≤ P.m ∧ (D.q τ : ℝ) + 2 * (D.j τ : ℝ) ≤ 2 * P.m ∧ (0 : ℝ) ≤ D.q τ ∧
      (0 : ℝ) ≤ D.j τ := by
  obtain ⟨_, _, _, _, _, hqj⟩ := hT τ hτ
  have h1 : (D.q τ : ℝ) + D.j τ ≤ P.m := by exact_mod_cast hqj
  have hq0 : (0 : ℝ) ≤ D.q τ := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ D.j τ := Nat.cast_nonneg _
  exact ⟨by linarith, by linarith, hq0, hj0⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
