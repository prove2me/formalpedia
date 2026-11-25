-- Prove2me | solution 1 for Formalism.L2.Ker.KS.half_period_standard_CM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:43:33.538118+00:00
-- url     : https://prove2.me/submissions/bb3810b0-cf3e-41ec-a10b-8e1227a9f157

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_mem_cmL
import Theorems.Thm_Formalism_L2_Ker_KS_pt_mem_iff
import Theorems.Thm_Formalism_L2_Ker_KS_pt_sub
import Theorems.Thm_Formalism_L2_Ker_KS_theta_one
import Theorems.Thm_Formalism_L2_Ker_KS_even_c

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
theorem _root_.solution (hcm : CmOK a b c d) :
    2 * (lam * a / 2) ∈ (cmL a b d ha hd lam hlam).lattice ∧
    Formalism.L2.Th1.F.cmTheta 1 d * (lam * a / 2) ∉ (cmL a b d ha hd lam hlam).lattice ∧
    (1 - Formalism.L2.Th1.F.cmTheta 1 d) * (lam * a / 2) ∉ (cmL a b d ha hd lam hlam).lattice := by
  obtain ⟨hc2, k, hk⟩ := even_c a b c d hcm
  obtain ⟨a', ha2⟩ := hcm.2.1
  have hpt : lam * (a : ℂ) / 2 = pt a b d lam (1 / 2) 0 := by
    simp only [pt]; push_cast; ring
  have hθ : Formalism.L2.Th1.F.cmTheta 1 d * (lam * (a : ℂ) / 2) = pt a b d lam (-(k : ℝ) / 2) ((a : ℝ) / 2) := by
    rw [theta_one b d k hk]
    simp only [pt]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_cmL]
    exact ⟨1, 0, by simp only [pt]; push_cast; ring⟩
  · rw [hθ, pt_mem_iff]
    rintro ⟨-, s, hs⟩
    have e : ((a : ℤ) : ℝ) = ((2 * s : ℤ) : ℝ) := by push_cast; linarith
    have e' : (a : ℤ) = 2 * s := by exact_mod_cast e
    omega
  · rw [sub_mul, one_mul, hθ, hpt, pt_sub, pt_mem_iff]
    rintro ⟨-, s, hs⟩
    have e : ((a : ℤ) : ℝ) = ((-2 * s : ℤ) : ℝ) := by push_cast; linarith
    have e' : (a : ℤ) = -2 * s := by exact_mod_cast e
    omega
end Formalism.L2.Ker.KS
