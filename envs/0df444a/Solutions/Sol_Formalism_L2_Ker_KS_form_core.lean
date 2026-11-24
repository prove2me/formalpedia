-- Prove2me | solution 1 for Formalism.L2.Ker.KS.form_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:45.503493+00:00
-- url     : https://prove2.me/submissions/993414a3-a05c-4ab5-93af-fc3d49ff714f

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
namespace Formalism.L2.Ker.KS
theorem _root_.solution (d : ℕ) (hd : 0 < d) (w1 w2 : ℂ) (hw1 : w1 ≠ 0) (p q r s : ℤ) (hq : 0 < q)
    (h1 : (p : ℂ) * w1 + (q : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w1)
    (h2 : (r : ℂ) * w1 + (s : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w2) :
    4 * q * (-r) = (1 - 2 * p) ^ 2 + d ∧ w1 / q ≠ 0 ∧ w1 = w1 / q * q ∧ w2 = w1 / q * Formalism.L2.Th1.F.cmTheta (1 - 2 * p) d := by
  have hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hθsq : Formalism.L2.Th1.F.cmTheta 1 d * Formalism.L2.Th1.F.cmTheta 1 d
      = Formalism.L2.Th1.F.cmTheta 1 d - (1 + (d : ℂ)) / 4 := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    linear_combination (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - (1 / 4 : ℂ) * hS
  have hkey : ((Formalism.L2.Th1.F.cmTheta 1 d - s) * (Formalism.L2.Th1.F.cmTheta 1 d - p) - r * q) * w1 = 0 := by
    linear_combination (-(Formalism.L2.Th1.F.cmTheta 1 d - s)) * h1 - (q : ℂ) * h2
  have hE := (mul_eq_zero.mp hkey).resolve_right hw1
  have hind := (Formalism.L2.Th1.F.cmPair 1 1 d one_pos hd).indep
  rw [LinearIndependent.pair_iff] at hind
  obtain ⟨e1, e2⟩ := hind (((4 * (p * s - r * q) - (1 + d) : ℤ) : ℝ)) (((4 * (1 - p - s) : ℤ) : ℝ)) (by
    show (((4 * (p * s - r * q) - (1 + d) : ℤ) : ℝ)) • (((1 : ℕ) : ℂ))
      + (((4 * (1 - p - s) : ℤ) : ℝ)) • Formalism.L2.Th1.F.cmTheta 1 d = 0
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination 4 * hE - 4 * hθsq)
  have e1' : 4 * (p * s - r * q) - (1 + (d : ℤ)) = 0 := by exact_mod_cast e1
  have e2' : 4 * (1 - p - s) = 0 := by exact_mod_cast e2
  have hs : s = 1 - p := by omega
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqq : (q : ℂ) * (q : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hq'
  have hθp : Formalism.L2.Th1.F.cmTheta (1 - 2 * p) d = Formalism.L2.Th1.F.cmTheta 1 d - (p : ℂ) := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    ring
  refine ⟨?_, div_ne_zero hw1 hq', by field_simp, ?_⟩
  · subst hs
    linear_combination e1'
  · rw [hθp]
    linear_combination (q : ℂ)⁻¹ * h1 - w2 * hqq
end Formalism.L2.Ker.KS
