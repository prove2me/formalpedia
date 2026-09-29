-- Prove2me | solution 1 for CuspForm.eq_zero_of_forall_vadd_inv_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9fc80349-5ca3-5c5e-a5d2-c037fe251d51

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped ModularForm UpperHalfPlane MatrixGroups Real

theorem solution
    {R q' : ℕ} [NeZero R] (hq' : 1 < q') (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ (j : ℕ) (τ : ℍ), y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ) :
    y = 0 := by
  have h1 : (1 : ℝ) ∈ (((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [show (((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) =
      Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma0 R) from rfl, CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  haveI : Fact (IsCusp OnePoint.infty (((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have hper : Function.Periodic ((⇑y : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex y h1
  have hmd := ModularFormClass.holo y
  have hbd : IsBoundedAtImInfty (⇑y : ℍ → ℂ) := ModularFormClass.bdd_at_infty y
  have hcoeff : ∀ m, PowerSeries.coeff m (qExpansion 1 (⇑y : ℍ → ℂ)) = 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [qExpansion_coeff]
      simp [CuspFormClass.cuspFunction_apply_zero y one_pos h1]
    · set δ : ℝ := ((q' : ℝ) ^ m)⁻¹ with hδ
      set ζ : ℂ := Complex.exp (2 * π * Complex.I * (δ : ℂ)) with hζdef
      have hζq : ∀ τ : ℍ, Function.Periodic.qParam 1 ((δ +ᵥ τ : ℍ) : ℂ) = ζ * Function.Periodic.qParam 1 (τ : ℂ) := by
        intro τ
        rw [UpperHalfPlane.coe_vadd]
        simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
        rw [hζdef, ← Complex.exp_add]
        congr 1
        ring
      have key := ModularFormClass.qExpansion_coeff_unique (k := k) one_pos h1 (f := y)
        (c := fun n => PowerSeries.coeff n (qExpansion 1 (⇑y : ℍ → ℂ)) * ζ ^ n) (fun τ => by
          have hs := hasSum_qExpansion one_pos hper hmd hbd (δ +ᵥ τ)
          rw [h m τ] at hs
          simp_rw [hζq τ, mul_pow, smul_eq_mul] at hs
          simp_rw [smul_eq_mul]
          convert hs using 1
          ext n
          ring) m

      have hζ : ζ ^ m ≠ 1 := by
        rw [hζdef, ← Complex.exp_nat_mul, Ne, Complex.exp_eq_one_iff]
        rintro ⟨n, hn⟩
        have h2pi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have hreal : ((m : ℝ) * δ : ℝ) = (n : ℝ) := by
          have : ((m : ℂ)) * (δ : ℂ) * (2 * π * Complex.I) = (n : ℂ) * (2 * π * Complex.I) := by
            rw [← hn]; ring
          have := mul_right_cancel₀ h2pi this
          exact_mod_cast this

        have hpos : (0 : ℝ) < (m : ℝ) * δ := by
          have : (0 : ℝ) < δ := by rw [hδ]; positivity
          positivity
        have hlt : (m : ℝ) * δ < 1 := by
          rw [hδ, ← div_eq_mul_inv, div_lt_one (by positivity)]
          exact_mod_cast Nat.lt_pow_self hq'
        rw [hreal] at hpos hlt
        have h0 : (0 : ℤ) < n := by exact_mod_cast hpos
        have h1' : n < (1 : ℤ) := by exact_mod_cast hlt
        omega
      have h2 : PowerSeries.coeff m (qExpansion 1 (⇑y : ℍ → ℂ)) * (ζ ^ m - 1) = 0 := by
        linear_combination key
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3) hζ
  have hq0 : qExpansion 1 (⇑y : ℍ → ℂ) = 0 := by
    ext m; rw [hcoeff m, map_zero]
  have hf : (⇑y : ℍ → ℂ) = 0 := (qExpansion_eq_zero_iff one_pos hper hmd hbd).1 hq0
  exact DFunLike.ext y 0 (fun τ => by simpa using congrFun hf τ)

end S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq
end P2MW
export P2MW.S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq (solution)
