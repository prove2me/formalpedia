-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.eF_beFam_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:51:03.204856+00:00
-- url     : https://prove2.me/submissions/218b67bf-80a1-4dc8-bed9-9abd1d66e01b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_fin_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_beFam_castSucc
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_beFam_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.CSym
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution (Q : K) (hQ : Q ≠ 0) (g l : ℕ) :
    eF (beFam Q (g + 1)) (l + 1) =
      Q ^ (l + 1) * eF (beFam Q g) (l + 1) + Q ^ (-(g : ℤ)) * (Q ^ l * eF (beFam Q g) l) := by
  rw [eF_fin_succ]
  simp_rw [beFam_castSucc Q hQ]
  rw [eF_smul, eF_smul, beFam_last]
end Formalism.InvariantFactorPaths.G7.CSym
