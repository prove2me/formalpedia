-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.num_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:42.047972+00:00
-- url     : https://prove2.me/submissions/9c162d71-97b0-40a6-8fb3-8bb82f32be4f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_sg_sq_add
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_herm_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hq : SgStarQuasi) (hst : MulStable L α) (hc : (S.card : ℝ) + 1 = Complex.normSq α)
    (ω z : ℂ) (hω : ω ∈ L.lattice) :
    num L α (z + ω) = (mlt L ω z ^ 2) ^ (S.card + 1) * num L α z := by
  simp only [num]
  rw [mul_add, sg_sq_add L hq (α * ω) (α * z) (hst ω hω)]
  congr 1
  have hN : (Complex.normSq α : ℂ) = ((S.card + 1 : ℕ) : ℂ) := by
    rw [← hc]; push_cast; ring
  have key : ∀ x y : ℂ, Complex.exp ((Real.pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * x) +
      (Real.pi : ℂ) * (((S.card + 1 : ℕ) : ℂ) * y) / 2) =
      Complex.exp ((Real.pi : ℂ) * x + (Real.pi : ℂ) * y / 2) ^ (S.card + 1) := by
    intro x y; rw [← Complex.exp_nat_mul]; congr 1; ring
  simp only [mlt]
  rw [herm_mul L α z ω, herm_mul L α ω ω, hN, key]
  ring
end Formalism.L2.Th1.F.IsogenySigmaQuotient
