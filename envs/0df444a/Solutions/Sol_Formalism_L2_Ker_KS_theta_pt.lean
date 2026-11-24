-- Prove2me | solution 1 for Formalism.L2.Ker.KS.theta_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:41:25.529812+00:00
-- url     : https://prove2.me/submissions/63748d5c-2e77-4a4e-923e-a825f4ee1b4c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_theta_sq
import Theorems.Thm_Formalism_L2_Ker_KS_theta_one
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_theta_sq


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
theorem _root_.solution (h : 4 * (a : ℤ) * c = b ^ 2 + d) (k : ℤ) (hb : b = 2 * k + 1) (u v : ℝ) :
    Formalism.L2.Th1.F.cmTheta 1 d * pt a b d lam u v = pt a b d lam (-v * c - k * u) (u * a + v * (k + 1)) := by
  have hsq := theta_sq a b c d h
  have hbC : (b : ℂ) = 2 * (k : ℂ) + 1 := by exact_mod_cast hb
  rw [theta_one b d k hb]
  simp only [pt]
  push_cast
  linear_combination (lam * (v : ℂ)) * hsq + (lam * (v : ℂ) * Formalism.L2.Th1.F.cmTheta b d) * hbC
end Formalism.L2.Ker.KS
