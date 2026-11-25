-- Prove2me | solution 1 for Formalism.L2.Ker.KS.parity_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:22:24.373368+00:00
-- url     : https://prove2.me/submissions/a4094366-3695-4c5f-96a3-ac763a19dfd1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM

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
open Formalism Formalism.L2 Formalism.L2.Ker Formalism.L2.Ker.KS
open Formalism.L2.Th1.H (cmL CmOK)
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
omit a b c d lam
namespace Formalism.L2.Ker.KS
theorem _root_.solution (r s k a c : ℤ) (hc : Even c) (ha : ¬ Even a) (h3 : ¬ (Even (-s * c - k * r) ∧ Even (r * a + s * (k + 1))))
    (h4 : ¬ (Even (r - (-s * c - k * r)) ∧ Even (s - (r * a + s * (k + 1))))) : Even (r - 1) ∧ Even s := by
  simp [Int.even_sub, Int.even_add, Int.even_mul, Int.even_add_one, hc, ha] at h3 h4 ⊢
  simp only [← Int.not_even_iff_odd] at h3 h4 ⊢
  tauto
end Formalism.L2.Ker.KS
