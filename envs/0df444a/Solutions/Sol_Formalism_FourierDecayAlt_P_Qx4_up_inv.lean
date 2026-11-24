-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.up_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:12.208146+00:00
-- url     : https://prove2.me/submissions/1882aba0-e8ff-4f34-97b3-73ee923f9175

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_inv

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
theorem _root_.solution {u : Mx k r} (hu : u ∈ UP k r l) : u⁻¹ ∈ UP k r l := by
  refine ⟨glev_inv hu.1, uh_inv_fix hu.1.1 hu.2.1, fun y hy => ?_⟩
  obtain ⟨t, ht⟩ := hu.2.2 y hy
  refine ⟨-t, uh_inv_fix hu.1.1 ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hu.2.1, ht, neg_smul, add_neg_cancel_right]
end Formalism.FourierDecayAlt.P.Qx4
