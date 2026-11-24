-- Prove2me | solution 1 for Formalism.L2.DIV.fockL_X_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:18:45.675804+00:00
-- url     : https://prove2.me/submissions/85ff6793-7bd1-402e-add9-fd5cfbf55dbd

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockL_X_pderiv
import Theorems.Thm_Formalism_L2_DIV_fockL_C_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
variable {K : Type} [Field K]
variable [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution {σ : Type} [DecidableEq σ] (i j : σ) :
    fockL (X i : MvPolynomial σ K) (X j) = if i = j then 1 else 0 := by
  have h := fockL_X_pderiv (K := K) i 1 (X j)
  rw [mul_one] at h
  rw [h, ← C_1, fockL_C_left, pderiv_X]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]
end Formalism.L2.DIV
