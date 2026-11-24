-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.psi_conjN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:30:57.020512+00:00
-- url     : https://prove2.me/submissions/2e41e075-1a8f-4d01-b84d-d5096a8b0bdc

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_ne
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_mul


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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n u : Mx k r} (hn : n ∈ Nset k r) (hu : u ∈ Nset k r) :
    psi k r z cStd (n * u * n⁻¹) = psi k r z cStd u := by
  have h1 := psi_mul hz (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul hn hu) (WeylGroupFacts.mem_n_inv hn)) hn
  rw [Matrix.mul_assoc, uh_inv_mul hn.1, Matrix.mul_one, psi_mul hz hn hu, mul_comm] at h1
  exact (mul_right_cancel₀ (psi_ne _) h1).symm
end Formalism.FourierDecayAlt.P.Qx4
