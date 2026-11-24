-- Prove2me | solution 1 for Formalism.L2.Ker.KS.pt_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:56.459801+00:00
-- url     : https://prove2.me/submissions/435472bc-5f53-4edb-9a4c-ce1dda65b91e

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
include ha hd hlam
namespace Formalism.L2.Ker.KS
theorem _root_.solution {u v u' v' : ℝ} (h : pt a b d lam u v = pt a b d lam u' v') : u = u' ∧ v = v' := by
  have h' : (u : ℂ) * a + (v : ℂ) * Formalism.L2.Th1.F.cmTheta b d
      = (u' : ℂ) * a + (v' : ℂ) * Formalism.L2.Th1.F.cmTheta b d := by
    unfold pt at h
    exact mul_left_cancel₀ hlam h
  have hind := (Formalism.L2.Th1.F.cmPair a b d ha hd).indep
  rw [LinearIndependent.pair_iff] at hind
  obtain ⟨h1, h2⟩ := hind (u - u') (v - v') (by
    show (u - u') • (a : ℂ) + (v - v') • Formalism.L2.Th1.F.cmTheta b d = 0
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination h')
  exact ⟨by linarith, by linarith⟩
end Formalism.L2.Ker.KS
