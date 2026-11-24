-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.h_es_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:09.796399+00:00
-- url     : https://prove2.me/submissions/6dd966ec-27f5-44dc-bd12-30c2466c0ffb

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_herm_es_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_eI_ne_esI

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
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (a b : Fin r) : ⟪bvec (esI k r a), bvec (esI k r b)⟫ = 0 := by
  rw [herm_es_right]; exact Pi.single_eq_of_ne (eI_ne_esI b a) _
end Formalism.FourierDecayAlt.P.Qx4
