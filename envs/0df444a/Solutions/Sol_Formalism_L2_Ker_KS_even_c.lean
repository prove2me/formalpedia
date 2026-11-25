-- Prove2me | solution 1 for Formalism.L2.Ker.KS.even_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:06:54.237092+00:00
-- url     : https://prove2.me/submissions/3953ff74-0fd3-47a0-9f41-baf74d302ad3

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
theorem _root_.solution (hcm : CmOK a b c d) : Even c ∧ Odd b := by
  obtain ⟨h, ⟨a', ha'⟩, hd8, -⟩ := hcm
  rcases Int.even_or_odd b with ⟨t, ht⟩ | ⟨t, ht⟩
  · exfalso
    have e : 4 * ((a : ℤ) * c) = 4 * (t * t) + (d : ℤ) := by
      linear_combination h + (b + t + t) * ht
    generalize (a : ℤ) * c = P at e
    generalize t * t = Q at e
    omega
  · have e : 4 * ((a : ℤ) * c) = 4 * (t * t + t) + 1 + (d : ℤ) := by
      linear_combination h + (b + 2 * t + 1) * ht
    have hev : Even (t * t + t) := by
      have := Int.even_mul_succ_self t
      rw [mul_add, mul_one] at this
      exact this
    obtain ⟨m, hm⟩ := hev
    rw [hm] at e
    have hP : ((a : ℤ) * c) % 2 = 0 := by
      generalize (a : ℤ) * c = P at e ⊢
      omega
    rcases Int.even_mul.mp (Int.even_iff.mpr hP) with ⟨e', he'⟩ | hce
    · exfalso
      omega
    · exact ⟨hce, ⟨t, ht⟩⟩
end Formalism.L2.Ker.KS
