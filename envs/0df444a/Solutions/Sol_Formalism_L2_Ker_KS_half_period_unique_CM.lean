-- Prove2me | solution 1 for Formalism.L2.Ker.KS.half_period_unique_CM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:04.825356+00:00
-- url     : https://prove2.me/submissions/69a3334d-6d59-41a3-b5e4-46c4b90427c2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_mem_cmL
import Theorems.Thm_Formalism_L2_Ker_KS_pt_mem_iff
import Theorems.Thm_Formalism_L2_Ker_KS_pt_sub
import Theorems.Thm_Formalism_L2_Ker_KS_theta_pt
import Theorems.Thm_Formalism_L2_Ker_KS_half_int
import Theorems.Thm_Formalism_L2_Ker_KS_even_c
import Theorems.Thm_Formalism_L2_Ker_KS_parity_key

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
theorem _root_.solution (hcm : CmOK a b c d) (t : ℂ) (h2 : 2 * t ∈ (cmL a b d ha hd lam hlam).lattice)
    (h3 : Formalism.L2.Th1.F.cmTheta 1 d * t ∉ (cmL a b d ha hd lam hlam).lattice)
    (h4 : (1 - Formalism.L2.Th1.F.cmTheta 1 d) * t ∉ (cmL a b d ha hd lam hlam).lattice) :
    t - lam * a / 2 ∈ (cmL a b d ha hd lam hlam).lattice := by
  obtain ⟨hc2, k, hk⟩ := even_c a b c d hcm
  have hform := hcm.1
  have hao : ¬ Even (a : ℤ) := by
    rintro ⟨e, he⟩
    obtain ⟨a', ha2⟩ := hcm.2.1
    omega
  rw [mem_cmL] at h2
  obtain ⟨r, s, hrs⟩ := h2
  have ht : t = pt a b d lam ((r : ℝ) / 2) ((s : ℝ) / 2) := by
    simp only [pt] at hrs ⊢
    push_cast at hrs ⊢
    linear_combination hrs / 2
  have e3 : Formalism.L2.Th1.F.cmTheta 1 d * t
      = pt a b d lam (((-s * c - k * r : ℤ) : ℝ) / 2) (((r * (a : ℤ) + s * (k + 1) : ℤ) : ℝ) / 2) := by
    rw [ht, theta_pt a b c d lam hform k hk]
    simp only [pt]
    push_cast
    ring
  have e4 : (1 - Formalism.L2.Th1.F.cmTheta 1 d) * t
      = pt a b d lam (((r - (-s * c - k * r) : ℤ) : ℝ) / 2)
          (((s - (r * (a : ℤ) + s * (k + 1)) : ℤ) : ℝ) / 2) := by
    rw [sub_mul, one_mul, e3, ht]
    simp only [pt]
    push_cast
    ring
  rw [e3, pt_mem_iff, half_int, half_int] at h3
  rw [e4, pt_mem_iff, half_int, half_int] at h4
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := parity_key r s k (a : ℤ) c hc2 hao h3 h4
  have hpt : lam * (a : ℂ) / 2 = pt a b d lam (1 / 2) 0 := by
    simp only [pt]; push_cast; ring
  rw [ht, hpt, pt_sub, pt_mem_iff]
  have em : ((r - 1 : ℤ) : ℝ) = ((m + m : ℤ) : ℝ) := by exact_mod_cast hm
  have en : ((s : ℤ) : ℝ) = ((n + n : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at em en
  exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩
end Formalism.L2.Ker.KS
