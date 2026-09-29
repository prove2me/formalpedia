-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c439a8c8-3c07-5634-8ba8-f193713c2932

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace AwaySpanGlue

section Quat

variable {a b : ℚ}

open QuaternionAlgebra

theorem sq_eq_trd_smul_sub (x : ℍ[ℚ, a, b]) :
    x * x = (trd x) • x - (nrd x) • (1 : ℍ[ℚ, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [QuaternionAlgebra.trd, QuaternionAlgebra.nrd] <;> ring

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem eq_zero_of_nrd_eq_zero (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (h : nrd z = 0) : z = 0 := by
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [QuaternionAlgebra.nrd_mk] at h
  have h1 : 0 ≤ -a * z₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ -b * z₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ (a * b) * z₃ ^ 2 := mul_nonneg (mul_pos_of_neg_of_neg ha hb).le (sq_nonneg _)
  have h0 : 0 ≤ z₀ ^ 2 := sq_nonneg _
  have e0 : z₀ ^ 2 = 0 := by linarith
  have e1 : -a * z₁ ^ 2 = 0 := by linarith
  have e2 : -b * z₂ ^ 2 = 0 := by linarith
  have e3 : (a * b) * z₃ ^ 2 = 0 := by linarith
  have ha0 : -a ≠ 0 := by linarith
  have hb0 : -b ≠ 0 := by linarith
  have hab0 : a * b ≠ 0 := (mul_pos_of_neg_of_neg ha hb).ne'
  have f0 : z₀ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e0
  have f1 : z₁ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 e1).resolve_left ha0)
  have f2 : z₂ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 e2).resolve_left hb0)
  have f3 : z₃ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 e3).resolve_left hab0)
  ext <;> simp [f0, f1, f2, f3]

theorem eq_zero_or_eq_zero_of_mul_eq_zero (ha : a < 0) (hb : b < 0) {x y : ℍ[ℚ, a, b]} (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  have hn := congrArg nrd h
  rw [nrd_mul', QuaternionAlgebra.nrd_zero] at hn
  rcases mul_eq_zero.1 hn with h1 | h1
  · exact Or.inl (eq_zero_of_nrd_eq_zero ha hb h1)
  · exact Or.inr (eq_zero_of_nrd_eq_zero ha hb h1)

theorem coeff_eq_zero_of_mul_ne {x y : ℍ[ℚ, a, b]} (hxy : x * y ≠ y * x) (α β γ : ℚ)
    (h : α • (1 : ℍ[ℚ, a, b]) + β • x + γ • y = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [zero_smul, add_zero] at h
    by_cases hβ : β = 0
    · subst hβ
      rw [zero_smul, add_zero, smul_eq_zero] at h
      exact ⟨h.resolve_right one_ne_zero, rfl, rfl⟩
    · exfalso
      have hx : x = (-(α / β)) • (1 : ℍ[ℚ, a, b]) := by
        have e : β • x = -(α • (1 : ℍ[ℚ, a, b])) := eq_neg_of_add_eq_zero_right h
        have e2 : x = β⁻¹ • (β • x) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        rw [e2, e]
        module
      apply hxy
      rw [hx, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  · exfalso
    have hy : y = (-(α / γ)) • (1 : ℍ[ℚ, a, b]) + (-(β / γ)) • x := by
      have e : γ • y = -(α • (1 : ℍ[ℚ, a, b]) + β • x) := eq_neg_of_add_eq_zero_right h
      have e2 : y = γ⁻¹ • (γ • y) := by rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]
      rw [e2, e]
      module
    apply hxy
    rw [hy, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]

theorem span_eq_top_of_mul_ne (ha : a < 0) (hb : b < 0) {x y : ℍ[ℚ, a, b]} (hxy : x * y ≠ y * x) :
    Submodule.span ℚ (Set.range ![(1 : ℍ[ℚ, a, b]), x, y, x * y]) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hg

    have hg3 : g 3 = 0 := by
      by_contra hδ
      set α' : ℚ := -(g 0 / g 3) with hα'
      set β' : ℚ := -(g 1 / g 3) with hβ'
      set γ' : ℚ := -(g 2 / g 3) with hγ'
      have hxy' : x * y = α' • (1 : ℍ[ℚ, a, b]) + β' • x + γ' • y := by
        have e : g 3 • (x * y) = -(g 0 • (1 : ℍ[ℚ, a, b]) + g 1 • x + g 2 • y) :=
          eq_neg_of_add_eq_zero_right hg
        have e2 : x * y = (g 3)⁻¹ • (g 3 • (x * y)) := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
        rw [e2, e, hα', hβ', hγ']
        module
      set t : ℚ := trd x with ht
      set n : ℚ := nrd x with hn
      have hxx : x * x = t • x - n • (1 : ℍ[ℚ, a, b]) := sq_eq_trd_smul_sub x

      have e1 : x * (x * y) = (t * α') • (1 : ℍ[ℚ, a, b]) + (t * β') • x + (t * γ' - n) • y := by
        rw [← mul_assoc, hxx, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hxy']
        module
      have e2 : x * (x * y) =
          (γ' * α' - β' * n) • (1 : ℍ[ℚ, a, b]) + (α' + β' * t + γ' * β') • x + (γ' * γ') • y := by
        rw [hxy', mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_one, hxx, hxy']
        module
      have key : (t * α' - (γ' * α' - β' * n)) • (1 : ℍ[ℚ, a, b]) + (t * β' - (α' + β' * t + γ' * β')) • x +
          ((t * γ' - n) - γ' * γ') • y = 0 := by
        have : (t * α' - (γ' * α' - β' * n)) • (1 : ℍ[ℚ, a, b]) + (t * β' - (α' + β' * t + γ' * β')) • x +
            ((t * γ' - n) - γ' * γ') • y =
            ((t * α') • (1 : ℍ[ℚ, a, b]) + (t * β') • x + (t * γ' - n) • y) -
              ((γ' * α' - β' * n) • (1 : ℍ[ℚ, a, b]) + (α' + β' * t + γ' * β') • x + (γ' * γ') • y) := by
          module
        rw [this, ← e1, ← e2, sub_self]
      obtain ⟨-, -, c3⟩ := coeff_eq_zero_of_mul_ne hxy _ _ _ key

      have hprod : (x - γ' • (1 : ℍ[ℚ, a, b])) * (x - (t - γ') • (1 : ℍ[ℚ, a, b])) = 0 := by
        have hn' : n = t * γ' - γ' * γ' := by linarith
        simp only [mul_sub, sub_mul, hxx, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
        rw [hn']
        module
      rcases eq_zero_or_eq_zero_of_mul_eq_zero ha hb hprod with h | h
      · apply hxy
        rw [sub_eq_zero.1 h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      · apply hxy
        rw [sub_eq_zero.1 h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hg3, zero_smul, add_zero] at hg
    obtain ⟨c0, c1, c2⟩ := coeff_eq_zero_of_mul_ne hxy _ _ _ hg
    intro i
    fin_cases i <;> assumption
  · rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four]

end Quat

section Main

variable {a₁ b₁ : ℚ}

open QuaternionAlgebra CerednikDrinfeld

theorem main (ha : a₁ < 0) (hb : b₁ < 0) (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (v : HeightOneSpectrum (𝓞 ℚ))
    (hpair : ∃ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v, ∃ y ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v,
      (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ≠ (y : ℍ[ℚ, a₁, b₁]) * (x : ℍ[ℚ, a₁, b₁])) :
    Submodule.span ℚ (Units.val '' (CerednikDrinfeld.CosetGraph.awayUnits R₁ v : Set (ℍ[ℚ, a₁, b₁])ˣ)) =
      (⊤ : Submodule ℚ ℍ[ℚ, a₁, b₁]) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hpair
  rw [eq_top_iff, ← span_eq_top_of_mul_ne ha hb hxy]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨1, (CosetGraph.awayUnits R₁ v).one_mem, by simp⟩
  · exact ⟨x, hx, by simp⟩
  · exact ⟨y, hy, by simp⟩
  · exact ⟨x * y, (CosetGraph.awayUnits R₁ v).mul_mem hx hy, by simp⟩

end Main

end AwaySpanGlue

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain CerednikDrinfeld

theorem solution
    {rbar N : ℕ} [Fact rbar.Prime]
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsEichlerOrder R₁ N)
    (r : ℕ) [Fact r.Prime] (hrr : rbar ≠ r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Submodule.span ℚ (Units.val '' (CerednikDrinfeld.CosetGraph.awayUnits R₁ v : Set (ℍ[ℚ, a₁, b₁])ˣ)) =
      (⊤ : Submodule ℚ ℍ[ℚ, a₁, b₁]) := by
  exact AwaySpanGlue.main hdef.1 hdef.2.1 R₁ v
    (CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt hdef R₁ hR₁.isOrder r hrr v hv)

end S_CerednikDrinfeld_CosetGraph_span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt (solution)
