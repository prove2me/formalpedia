-- Prove2me | solution 1 for Formalism.L2.DIV.fk_fock_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:45.729704+00:00
-- url     : https://prove2.me/submissions/11b67eae-3689-4d27-9b5c-966ab634186a

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_blockEmb_X
import Theorems.Thm_Formalism_L2_DIV_fk_blockEmb_C
import Theorems.Thm_Formalism_L2_DIV_fk_pderiv_blockEmb
import Theorems.Thm_Formalism_L2_DIV_fk_fock_right
import Theorems.Thm_Formalism_L2_DIV_fockL_C_left
import Theorems.Thm_Formalism_L2_DIV_fockL_X_pderiv


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
theorem _root_.solution (τ : ι) (P P' : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (hP' : ∀ v, pderiv (τ, v) P' = 0) (f g : MvPolynomial (Fin n × Fin n) K) :
    fockL (Formalism.GradedWeylDivisibility.blockEmb K τ f * P) (Formalism.GradedWeylDivisibility.blockEmb K τ g * P') = fockL f g * fockL P P' := by
  classical
  induction f using MvPolynomial.induction_on generalizing g with
  | C a =>
    rw [fk_blockEmb_C, ← smul_eq_C_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, fk_fock_right τ P P' hP,
      fockL_C_left, smul_eq_mul, starRingEnd_apply, mul_assoc]
  | add p q hp hq =>
    rw [map_add, add_mul, map_add, LinearMap.add_apply, hp, hq, map_add, LinearMap.add_apply, add_mul]
  | mul_X p v hp =>
    rw [map_mul (Formalism.GradedWeylDivisibility.blockEmb K τ), fk_blockEmb_X, mul_comm _ (X (τ, v)), mul_assoc, fockL_X_pderiv, Derivation.leibniz, hP',
      smul_zero, zero_add, fk_pderiv_blockEmb, smul_eq_mul, mul_comm P', hp, mul_comm p, fockL_X_pderiv]
end Formalism.L2.DIV
