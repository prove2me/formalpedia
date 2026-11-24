-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.isOpen_adelicUnipotentTimesIntegralOutsideSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:44:02.202003+00:00
-- url     : https://prove2.me/submissions/c7b947e0-02dd-40ce-9168-1b5e8637ec8f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_iH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_sm_cF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution : IsOpen (C0 k r l) := by
  have h1 : Continuous fun g : Mx k r => cF k r l g :=
    continuousOn_univ.1 (sm_cF (smM_id Set.univ)).continuousOn
  have h2 : Continuous fun g : Mx k r => cF k r l (iH g) :=
    continuousOn_univ.1 (sm_cF (smM_iH (smM_id Set.univ))).continuousOn
  exact (isOpen_ne_fun h1 continuous_const).inter (isOpen_ne_fun h2 continuous_const)
end Formalism.FourierDecayAlt.P.Qx4
