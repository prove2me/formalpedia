-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.integral_of_prime_local_multiples
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:03:32.013461+00:00
-- url     : https://prove2.me/submissions/81ea9a18-cc43-4d5e-81f4-014f64546813

import Mathlib
namespace EulerLocalGlobal
lemma integral_of_local_integer_multiples (x : ℝ)
    (h : ∀ p : ℕ, p.Prime → ∃ d : ℤ, ¬(p:ℤ) ∣ d ∧ IsIntegral ℤ ((d:ℝ)*x)) :
    IsIntegral ℤ x := by
  let I : Ideal ℤ :=
    { carrier := {d | IsIntegral ℤ ((d:ℝ)*x)}
      zero_mem' := by simp [isIntegral_zero]
      add_mem' := by
        intro a b ha hb
        simpa [Int.cast_add,add_mul] using ha.add hb
      smul_mem' := by
        intro a b hb
        change IsIntegral ℤ (((a*b:ℤ):ℝ)*x)
        rw [Int.cast_mul,mul_assoc]
        exact (isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := a)).mul hb }
  let g := Submodule.IsPrincipal.generator I
  have hg : g ∈ I := Submodule.IsPrincipal.generator_mem I
  by_cases hu : IsUnit g
  · have ht : I=⊤ := I.eq_top_of_isUnit_mem hg hu
    have h1 : (1:ℤ) ∈ I := by rw [ht]; trivial
    change IsIntegral ℤ ((1:ℤ)*x) at h1
    simpa using h1
  · have hn : g.natAbs ≠ 1 := by simpa only [Int.isUnit_iff_natAbs_eq] using hu
    obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hn
    obtain ⟨d,hd,hdi⟩ := h p hp
    have hgd : g ∣ d := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hdi
    exact False.elim (hd ((Int.natCast_dvd.mpr hpg).trans hgd))
end EulerLocalGlobal


theorem solution (x : ℝ)
    (h : ∀ p : ℕ, p.Prime → ∃ d : ℤ, ¬(p:ℤ) ∣ d ∧ IsIntegral ℤ ((d:ℝ)*x)) :
    IsIntegral ℤ x := by
  exact EulerLocalGlobal.integral_of_local_integer_multiples x h

#print axioms solution
