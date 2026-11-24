-- Prove2me | solution 1 for Formalism.L2.LamCM.degree_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:19:25.87592+00:00
-- url     : https://prove2.me/submissions/f61c1363-43ce-476a-9166-c9b30435158e

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Theorems.Thm_Formalism_L2_LamCM_log_absNorm_mul

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
theorem _root_.solution : DegAlg := by
  intro K _ _ L M hL hM
  obtain ⟨hLI, hLn⟩ := hL
  obtain ⟨hMI, hMn⟩ := hM
  refine ⟨⟨mul_ne_zero hLI hMI, fun σ => mul_pos (hLn σ) (hMn σ)⟩, ?_,
    ⟨inv_ne_zero hLI, fun σ => inv_pos.mpr (hLn σ)⟩, ?_,
    fun k => ⟨⟨pow_ne_zero _ hLI, fun σ => pow_pos (hLn σ) k⟩, ?_⟩⟩
  · simp only [MLine.deg, MLine.tensor]
    rw [log_absNorm_mul hLI hMI,
      Finset.sum_congr rfl (fun σ _ => Real.log_mul (hLn σ).ne' (hMn σ).ne'), Finset.sum_add_distrib]
    ring
  · simp only [MLine.deg, MLine.dual]
    rw [map_inv₀, Rat.cast_inv, Real.log_inv,
      Finset.sum_congr rfl (fun σ _ => Real.log_inv (L.n σ)), Finset.sum_neg_distrib]
    ring
  · simp only [MLine.deg, MLine.pow]
    rw [map_pow, Rat.cast_pow, Real.log_pow,
      Finset.sum_congr rfl (fun σ _ => Real.log_pow (L.n σ) k), ← Finset.mul_sum]
    ring
end Formalism.L2.LamCM
