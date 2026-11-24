-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.phi_orth4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:12.87503+00:00
-- url     : https://prove2.me/submissions/38ffad3a-d134-468e-8117-846f78740c37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_nsmul_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
namespace Formalism.L2.Th1.H.IsQuadFn
theorem _root_.solution (h : IsQuadFn φ b) (x₀ x₁ x₂ x₃ : M) (h01 : b x₀ x₁ = 1) (h02 : b x₀ x₂ = 1)
    (h03 : b x₀ x₃ = 1) (h12 : b x₁ x₂ = 1) (h13 : b x₁ x₃ = 1) (h23 : b x₂ x₃ = 1)
    (k₀ k₁ k₂ k₃ : ℕ) :
    φ (k₀ • x₀ + k₁ • x₁ + k₂ • x₂ + k₃ • x₃)
      = φ x₀ ^ (k₀ ^ 2) * φ x₁ ^ (k₁ ^ 2) * φ x₂ ^ (k₂ ^ 2) * φ x₃ ^ (k₃ ^ 2) := by
  simp only [h.add, h.left, h.b_nsmul_nsmul, h01, h02, h03, h12, h13, h23, one_pow, mul_one,
    h.sq]
  try ring
end Formalism.L2.Th1.H.IsQuadFn
