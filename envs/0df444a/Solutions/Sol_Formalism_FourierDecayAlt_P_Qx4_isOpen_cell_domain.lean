-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.isOpen_cell_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:16.263927+00:00
-- url     : https://prove2.me/submissions/05a65bff-5626-49db-9a5a-0d4f2805c923

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_isOpen_adelicUnipotentTimesIntegralOutsideSet

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {D₁ : Set (Mx k r)} (hD : IsOpen D₁) : IsOpen (D0 k r l D₁) :=
  (smM_contDiffOn smM_rho).continuousOn.isOpen_inter_preimage isOpen_adelicUnipotentTimesIntegralOutsideSet hD
end Formalism.FourierDecayAlt.P.Qx4
