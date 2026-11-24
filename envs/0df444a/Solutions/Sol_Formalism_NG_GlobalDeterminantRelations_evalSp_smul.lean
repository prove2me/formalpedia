-- Prove2me | solution 1 for Formalism.NG.GlobalDeterminantRelations.evalSp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:35.621718+00:00
-- url     : https://prove2.me/submissions/c7f98496-4f11-462d-a5b3-d313be20f762

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.GlobalDeterminantRelations
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')
namespace Formalism.NG.GlobalDeterminantRelations
theorem _root_.solution (r : R') (v : EvalSp O d R' x') (a : d) :
    (r • v : d → FractionRing O) a =
      ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b := rfl
end Formalism.NG.GlobalDeterminantRelations
