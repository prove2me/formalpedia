-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.psiPath_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:31:14.075317+00:00
-- url     : https://prove2.me/submissions/a55e964c-452d-4c59-82aa-fea14c860340

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_PathBasisTheorem
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_path_basis_theorem
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_countPAll


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
open Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
theorem _root_.solution (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (R : Type) [CommRing R] :
    LinearIndependent R (fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) ∧
      Submodule.span R (Set.range fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) =
        polB R n N B := path_basis_theorem n N isVec B (countPAll n N isVec B) R
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
