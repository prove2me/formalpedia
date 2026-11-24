-- Prove2me | solution 1 for Formalism.L2.LamCM.sum_comp_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:36.186678+00:00
-- url     : https://prove2.me/submissions/cda12128-64ba-41dd-97b0-afcfd1882a87

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
import Theorems.Thm_Formalism_L2_LamCM_card_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution (f : (K →+* ℂ) → ℝ) :
    ∑ σ1 : K1 →+* ℂ, f (σ1.comp (algebraMap K K1)) = (Module.finrank K K1 : ℝ) * ∑ σ : K →+* ℂ, f σ := by
  classical
  have h1 : ∀ σ : K →+* ℂ, (∑ σ1 : K1 →+* ℂ, if σ1.comp (algebraMap K K1) = σ then f σ else 0) =
      (Module.finrank K K1 : ℝ) * f σ := by
    intro σ
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have h := card_fibre (K1 := K1) σ
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact_mod_cast h
  calc ∑ σ1 : K1 →+* ℂ, f (σ1.comp (algebraMap K K1))
      = ∑ σ1 : K1 →+* ℂ, ∑ σ : K →+* ℂ, if σ1.comp (algebraMap K K1) = σ then f σ else 0 := by
        refine Finset.sum_congr rfl (fun σ1 _ => ?_)
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ σ : K →+* ℂ, ∑ σ1 : K1 →+* ℂ, if σ1.comp (algebraMap K K1) = σ then f σ else 0 := Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => h1 σ)
end Formalism.L2.LamCM
