-- Prove2me | solution 1 for Formalism.L2.DIV.fockL_blockAct_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:31.651164+00:00
-- url     : https://prove2.me/submissions/ee113826-13fd-4f86-85a0-c3585a0e86b3

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockL_X_pderiv
import Theorems.Thm_Formalism_L2_DIV_fockL_C_left
import Theorems.Thm_Formalism_L2_DIV_blockAct_X
import Theorems.Thm_Formalism_L2_DIV_constantCoeff_blockAct
import Theorems.Thm_Formalism_L2_DIV_pderiv_blockAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K]
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (U : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    fockL (Formalism.GradedWeylDivisibility.blockAct K U F) F' = fockL F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (U τ)ᴴ) F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_blockAct]
  | add p q hp hq => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : Formalism.GradedWeylDivisibility.blockAct K U (p * X v) =
        ∑ b : Fin n, U v.1 v.2.1 b • (X (v.1, (b, v.2.2)) * Formalism.GradedWeylDivisibility.blockAct K U p) := by
      rw [map_mul, blockAct_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring
    rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]
    rw [mul_comm p, fockL_X_pderiv, show v = (v.1, (v.2.1, v.2.2)) from rfl, pderiv_blockAct, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]
end Formalism.L2.DIV
