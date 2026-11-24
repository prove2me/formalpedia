-- Prove2me | solution 1 for Formalism.L2.Ker.KS.cmL_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:49.464098+00:00
-- url     : https://prove2.me/submissions/e197228f-4766-4ee7-913b-69b6304f6356

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_mem_cmL
import Theorems.Thm_Formalism_L2_Ker_KS_lattice_ext

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
theorem _root_.solution (hc : 0 < c) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    ∃ (lam' : ℂ) (hlam' : lam' ≠ 0), (cmL c.toNat (-b) d (by omega) hd lam' hlam').lattice = (cmL a b d ha hd lam hlam).lattice := by
  have hind := (Formalism.L2.Th1.F.cmPair a b d ha hd).indep
  rw [LinearIndependent.pair_iff] at hind
  have hθ : Formalism.L2.Th1.F.cmTheta b d ≠ 0 := by
    intro h0
    have := (hind 0 1 (by
      show (0 : ℝ) • (a : ℂ) + (1 : ℝ) • Formalism.L2.Th1.F.cmTheta b d = 0
      rw [h0]; simp)).2
    norm_num at this
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcc : (c : ℂ) * (c : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hc'
  have hct : ((c.toNat : ℕ) : ℂ) = (c : ℂ) := by
    have e : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc.le
    exact_mod_cast e
  have h' : 4 * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ) := by exact_mod_cast h
  have hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hprod : Formalism.L2.Th1.F.cmTheta b d * Formalism.L2.Th1.F.cmTheta (-b) d = -((a : ℂ) * (c : ℂ)) := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    linear_combination (1 / 4 : ℂ) * h' + (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq
      - (1 / 4 : ℂ) * hS
  refine ⟨lam * Formalism.L2.Th1.F.cmTheta b d / (c : ℂ), div_ne_zero (mul_ne_zero hlam hθ) hc', ?_⟩
  apply lattice_ext
  intro z
  rw [mem_cmL, mem_cmL]
  constructor
  · rintro ⟨r, s, rfl⟩
    refine ⟨-s, r, ?_⟩
    simp only [pt]
    rw [hct]
    push_cast
    linear_combination (lam * Formalism.L2.Th1.F.cmTheta b d * (r : ℂ) - lam * (s : ℂ) * (a : ℂ)) * hcc
      + (lam * (s : ℂ) * (c : ℂ)⁻¹) * hprod
  · rintro ⟨r, s, rfl⟩
    refine ⟨s, -r, ?_⟩
    simp only [pt]
    rw [hct]
    push_cast
    linear_combination (-(lam * (s : ℂ) * Formalism.L2.Th1.F.cmTheta b d) - lam * (r : ℂ) * (a : ℂ)) * hcc
      + (lam * (r : ℂ) * (c : ℂ)⁻¹) * hprod
end Formalism.L2.Ker.KS
