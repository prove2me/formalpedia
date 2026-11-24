-- Prove2me | solution 1 for Formalism.L2.DIV.fk_fock_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:28.848293+00:00
-- url     : https://prove2.me/submissions/9ad08209-eb2d-494b-a34a-e9681662258e

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_blockEmb_X
import Theorems.Thm_Formalism_L2_DIV_fk_blockEmb_C
import Theorems.Thm_Formalism_L2_DIV_fockL_pderiv_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (τ : ι) (P Q : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (g : MvPolynomial (Fin n × Fin n) K) :
    fockL P (Formalism.GradedWeylDivisibility.blockEmb K τ g * Q) = constantCoeff g * fockL P Q := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => rw [fk_blockEmb_C, ← smul_eq_C_mul, map_smul, smul_eq_mul, constantCoeff_C]
  | add p q hp hq => rw [map_add, add_mul, map_add, hp, hq, map_add, add_mul]
  | mul_X p v _ =>
    rw [map_mul (Formalism.GradedWeylDivisibility.blockEmb K τ), fk_blockEmb_X, mul_comm _ (X (τ, v)), mul_assoc, ← fockL_pderiv_X, hP, map_zero,
      LinearMap.zero_apply, map_mul constantCoeff, constantCoeff_X, mul_zero, zero_mul]
end Formalism.L2.DIV
