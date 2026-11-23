-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.IsPoly.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:57.025001+00:00
-- url     : https://prove2.me/submissions/293467df-d363-4b5a-98b0-e6b2dbea2253

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6.PC
namespace IsPoly
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → ℂ → B} (hf : ∀ i ∈ s, IsPoly (f i)) :
    IsPoly fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPoly.const (0 : B)
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine (funext fun y => ?_ : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y) ▸ h1
    rw [Finset.sum_insert ha]
end IsPoly
end Formalism.FourierDecayAlt.P.Mx6.PC
