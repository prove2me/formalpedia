-- Prove2me | solution 1 for Formalism.L2.Th1.H.product_theta_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:17.026399+00:00
-- url     : https://prove2.me/submissions/9dd0153e-b016-4639-930d-4d323b063c01

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat
import Theorems.Thm_Formalism_L2_Th1_H_th0Char_mul_opU_th0_half_period_eq
import Theorems.Thm_Formalism_L2_Th1_F_th0Basic
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergStandard


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
theorem _root_.solution : ProductThetaMem := by
  intro L ω₀ n _ _ h0 hh α hα
  obtain ⟨hd, h1, -⟩ := Formalism.L2.Th1.F.th0Basic L ω₀ h0 hh
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z _
    unfold F0 prodFn
    refine Finset.analyticAt_fun_prod _ fun i _ => ?_
    exact (hd.analyticAt (z i)).comp_of_eq
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt z) rfl
  · intro x hx z
    rw [hα x hx, F0, heisenbergStandard, stdChar, ← Finset.prod_mul_distrib, prodFn]
    rw [mem_stdLat] at hx
    exact Finset.prod_congr rfl fun i _ => th0Char_mul_opU_th0_half_period_eq L ω₀ h0 hh (x i) (hx i) (z i)
  · simp [F0, prodFn, h1]
end Formalism.L2.Th1.H
