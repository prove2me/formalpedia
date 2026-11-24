-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.toNat_xlo_sub_maxB_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:39.41479+00:00
-- url     : https://prove2.me/submissions/73fca108-1d50-4cda-9989-db5bc481236b

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_le_floor_h

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
theorem _root_.solution {P : Par} (H : P.Hyp) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) :
    (((D.xlo τ - D.maxB τ).toNat : ℕ) : ℤ) = D.xlo τ - D.maxB τ ∧
      1 ≤ (D.xlo τ - D.maxB τ).toNat ∧ (D.xlo τ - D.maxB τ).toNat ≤ ⌊P.h⌋₊ := by
  obtain ⟨hmb0, hmbx, hxx, hxh, _, _⟩ := hT τ hτ
  have hxhN := le_floor_h H hxh
  refine ⟨by omega, by omega, by omega⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
