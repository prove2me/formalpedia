-- Prove2me | solution 1 for Formalism.L2.DIV.fockL_pderiv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:46:36.559353+00:00
-- url     : https://prove2.me/submissions/bc5c33dd-3853-4a17-b2a8-df1a9856fa7e

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockL_monomial_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_REAL_prod_factorial_support_sub_single
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution {σ : Type} [DecidableEq σ] (v : σ) (f g : MvPolynomial σ K) :
    fockL (pderiv v f) g = fockL f (X v * g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [pderiv_monomial, fockL_monomial_left, fockL_monomial_left, coeff_X_mul']
    by_cases hv : u v = 0
    · have : v ∉ u.support := Finsupp.notMem_support_iff.mpr hv
      simp [hv, this]
    · have : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
      rw [if_pos this]
      unfold mfact
      rw [Formalism.REAL.prod_factorial_support_sub_single u v hv, star_mul', star_natCast]
      push_cast; ring
  | add p q hp hq => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
end Formalism.L2.DIV
