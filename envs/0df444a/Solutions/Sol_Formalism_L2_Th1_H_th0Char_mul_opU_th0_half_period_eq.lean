-- Prove2me | solution 1 for Formalism.L2.Th1.H.th0Char_mul_opU_th0_half_period_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:06:38.950275+00:00
-- url     : https://prove2.me/submissions/c3b93147-af48-418b-855b-78d514f2a4bc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_th0Char_sq
import Theorems.Thm_Formalism_L2_Th1_F_EvenThetaIsogeny_th0Char_sq
import Theorems.Thm_Formalism_L2_Th1_F_th0Basic


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
theorem _root_.solution (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (hh : ω₀ / 2 ∉ L.lattice) (ω : ℂ)
    (hω : ω ∈ L.lattice) (z : ℂ) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω * Formalism.L2.Th1.F.opU L ω (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) z
      = Formalism.L2.Th1.F.th0 L (ω₀ / 2) z := by
  have h := (Formalism.L2.Th1.F.th0Basic L ω₀ h0 hh).2.2.2.2 ω hω z
  have hsq := th0Char_sq L ω₀ ω h0 hω
  rw [Formalism.L2.Th1.F.opU, h, ← Formalism.L2.Th1.F.thetaZeroCharacter]
  have he : Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
        + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
      * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination
    (Formalism.L2.Th1.F.th0 L (ω₀ / 2) z * (Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
              + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
      * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2))) * hsq
    + Formalism.L2.Th1.F.th0 L (ω₀ / 2) z * he
end Formalism.L2.Th1.H
