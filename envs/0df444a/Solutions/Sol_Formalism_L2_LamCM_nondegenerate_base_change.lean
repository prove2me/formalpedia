-- Prove2me | solution 1 for Formalism.L2.LamCM.nondegenerate_base_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:24.345606+00:00
-- url     : https://prove2.me/submissions/f5dc6451-b901-42c0-8401-0a16a30066cc

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
import Theorems.Thm_Formalism_L2_LamCM_eq_bcI
import Theorems.Thm_Formalism_L2_LamCM_bcI_ne_zero
import Theorems.Thm_Formalism_L2_LamCM_absNorm_bcI
import Theorems.Thm_Formalism_L2_LamCM_sum_comp_algebraMap

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
namespace Formalism.L2.LamCM
theorem _root_.solution : NdegBaseChange := by
  intro K K1 _ _ _ _ _ L L1 hG hB
  have hI := eq_bcI hB
  have hn : ∀ σ, L1.n σ = L.n (σ.comp (algebraMap K K1)) := by
    unfold IsBaseChangeLine at hB
    exact hB.2
  unfold MLine.Good at hG ⊢
  refine ⟨⟨by rw [hI]; exact bcI_ne_zero hG.1, fun σ => by rw [hn]; exact hG.2 _⟩, ?_⟩
  unfold MLine.ndeg MLine.deg
  rw [hI, absNorm_bcI]
  simp only [hn]
  rw [show (∑ σ : K1 →+* ℂ, Real.log (L.n (σ.comp (algebraMap K K1)))) =
      (Module.finrank K K1 : ℝ) * ∑ σ : K →+* ℂ, Real.log (L.n σ) from
      sum_comp_algebraMap (fun σ => Real.log (L.n σ))]
  have hd : Module.finrank ℚ K1 = Module.finrank ℚ K * Module.finrank K K1 :=
    (Module.finrank_mul_finrank ℚ K K1).symm
  have hpos : (0:ℝ) < Module.finrank K K1 := by exact_mod_cast Module.finrank_pos
  have hpos2 : (0:ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [Rat.cast_pow, Real.log_pow, hd, Nat.cast_mul, div_eq_div_iff (mul_pos hpos2 hpos).ne' hpos2.ne']
  ring
end Formalism.L2.LamCM
