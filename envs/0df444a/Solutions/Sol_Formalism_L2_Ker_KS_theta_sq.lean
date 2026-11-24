-- Prove2me | solution 1 for Formalism.L2.Ker.KS.theta_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:06.454899+00:00
-- url     : https://prove2.me/submissions/008c171d-9115-4579-b3c4-5acb4038ea4d

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
namespace Formalism.L2.Ker.KS
theorem _root_.solution (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    Formalism.L2.Th1.F.cmTheta b d * Formalism.L2.Th1.F.cmTheta b d = (b : ℂ) * Formalism.L2.Th1.F.cmTheta b d - (a : ℂ) * (c : ℂ) := by
  have h' : 4 * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ) := by exact_mod_cast h
  have hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  unfold Formalism.L2.Th1.F.cmTheta
  linear_combination (1 / 4 : ℂ) * h' + (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq
    - (1 / 4 : ℂ) * hS
end Formalism.L2.Ker.KS
