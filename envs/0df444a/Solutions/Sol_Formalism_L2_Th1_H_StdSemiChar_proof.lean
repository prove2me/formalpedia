-- Prove2me | solution 1 for Formalism.L2.Th1.H.StdSemiChar_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:28.285579+00:00
-- url     : https://prove2.me/submissions/909dc6ff-8d32-40fe-bf82-cd680d5fa4d5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_altE_std
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat
import Theorems.Thm_Formalism_L2_Th1_H_th0Char_pm
import Theorems.Thm_Formalism_L2_Th1_H_th0Char_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : StdSemiChar := by
  intro L ω₀ n _ _ h0
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [mem_stdLat] at hx
    unfold stdChar
    refine Finset.prod_induction _ (fun c : ℂ => c = 1 ∨ c = -1) ?_ (Or.inl rfl)
      (fun i _ => th0Char_pm L ω₀ (x i) h0 (hx i))
    intro a b ha hb
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · rw [mem_stdLat] at hx hy
    simp only [stdChar, Pi.add_apply]
    rw [altE_std, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => th0Char_add L ω₀ (x i) (y i) (hx i) (hy i)
end Formalism.L2.Th1.H
