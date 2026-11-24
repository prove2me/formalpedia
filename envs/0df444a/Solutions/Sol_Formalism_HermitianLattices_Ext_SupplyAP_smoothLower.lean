-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.smoothLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.010457+00:00
-- url     : https://prove2.me/submissions/9a76011a-c966-42c7-8d9d-66bbb0c2e99a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_one_le_zetaMul_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_zetaMul_eq_sum
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_smoothLowerReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (K N : ℕ) (x : ℝ) (hx : 0 < x) (hKx : (K : ℝ) ^ 2 ≤ x) (hKN : K ^ 2 ≤ N) :
    (K : ℝ) / Real.exp 1 ≤
      x * (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) / (d : ℂ)).re +
      (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)).re +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by
  set c : ℕ → ℝ := fun d => (χ (d : ZMod q)).re with hcdef
  have hχc : ∀ d : ℕ, χ (d : ZMod q) = ((c d : ℝ) : ℂ) := by
    intro d
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2 (d : ZMod q) with h | h | h <;>
      simp [hcdef, h]
  have hc : ∀ d, |c d| ≤ 1 := by
    intro d
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2 (d : ZMod q) with h | h | h <;>
      simp [hcdef, h]
  have hz : ∀ n, DirichletCharacter.zetaMul χ n = ((∑ d ∈ n.divisors, c d : ℝ) : ℂ) := by
    intro n
    rw [zetaMul_eq_sum]
    push_cast
    exact Finset.sum_congr rfl (fun d _ => hχc d)
  have key := smoothLowerReal c (fun n => ∑ d ∈ n.divisors, c d) (fun _ => rfl) hc
    (fun n => by
      have := DirichletCharacter.zetaMul_nonneg hχ2 n
      rw [hz] at this
      exact_mod_cast this)
    (fun k hk => by
      have := one_le_zetaMul_sq hχ2 k hk
      rw [hz] at this
      exact_mod_cast this) K N x hx hKx hKN
  have e1 : (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) / (d : ℂ)).re = ∑ d ∈ Icc 1 N, c d / (d : ℝ) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hχc d, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  have e2 : (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)).re =
      ∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hχc d, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [e1, e2]
  exact key
end Formalism.HermitianLattices.Ext.SupplyAP
