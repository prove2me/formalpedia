-- Prove2me | solution 1 for Formalism.L2.Ker.KS.cmL_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:47.335088+00:00
-- url     : https://prove2.me/submissions/f3868cd9-2e5a-4dfa-929e-4c66ba5a8e4e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_mem_cmL
import Theorems.Thm_Formalism_L2_Ker_KS_theta_sq
import Theorems.Thm_Formalism_L2_Ker_KS_lattice_ext
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
theorem _root_.solution (hs : 0 < (a : ℤ) + b + c) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    ∃ (lam' : ℂ) (hlam' : lam' ≠ 0),
      (cmL ((a : ℤ) + b + c).toNat (b + 2 * c) d (by omega) hd lam' hlam').lattice = (cmL a b d ha hd lam hlam).lattice := by
  have hind := (Formalism.L2.Th1.F.cmPair a b d ha hd).indep
  rw [LinearIndependent.pair_iff] at hind
  have hne : (a : ℂ) + Formalism.L2.Th1.F.cmTheta b d ≠ 0 := by
    intro h0
    have := (hind 1 1 (by
      show (1 : ℝ) • (a : ℂ) + (1 : ℝ) • Formalism.L2.Th1.F.cmTheta b d = 0
      rw [one_smul, one_smul]; exact h0)).1
    norm_num at this
  have hA : (a : ℂ) + (b : ℂ) + (c : ℂ) ≠ 0 := by
    have e : (((a : ℤ) + b + c : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast at e
    exact e
  have hAA : ((a : ℂ) + (b : ℂ) + (c : ℂ)) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hA
  have hAt : ((((a : ℤ) + b + c).toNat : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) + (c : ℂ) := by
    have e : ((((a : ℤ) + b + c).toNat : ℕ) : ℤ) = (a : ℤ) + b + c := Int.toNat_of_nonneg hs.le
    have e' : (((((a : ℤ) + b + c).toNat : ℕ) : ℤ) : ℂ) = (((a : ℤ) + b + c : ℤ) : ℂ) := by rw [e]
    push_cast at e'
    exact e'
  have hθ' : Formalism.L2.Th1.F.cmTheta (b + 2 * c) d = Formalism.L2.Th1.F.cmTheta b d + (c : ℂ) := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    ring
  have hsq := theta_sq a b c d h
  refine ⟨lam * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d) / ((a : ℂ) + (b : ℂ) + (c : ℂ)),
    div_ne_zero (mul_ne_zero hlam hne) hA, ?_⟩
  apply lattice_ext
  intro z
  rw [mem_cmL, mem_cmL]
  constructor
  · rintro ⟨r, s, rfl⟩
    refine ⟨r, r + s, ?_⟩
    simp only [pt]
    rw [hAt, hθ']
    push_cast
    linear_combination (lam * (r : ℂ) * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d)
        + lam * (s : ℂ) * Formalism.L2.Th1.F.cmTheta b d) * hAA
      + (lam * (s : ℂ) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹) * hsq
  · rintro ⟨r, s, rfl⟩
    refine ⟨r, s - r, ?_⟩
    simp only [pt]
    rw [hAt, hθ']
    push_cast
    linear_combination (-(lam * (r : ℂ) * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d))
        - lam * ((s : ℂ) - (r : ℂ)) * Formalism.L2.Th1.F.cmTheta b d) * hAA
      - (lam * ((s : ℂ) - (r : ℂ)) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹) * hsq
end Formalism.L2.Ker.KS
