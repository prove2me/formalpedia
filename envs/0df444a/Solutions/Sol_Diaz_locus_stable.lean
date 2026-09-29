-- Prove2me | solution 1 for Diaz.locus_stable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:05:36.541983+00:00
-- url     : https://prove2.me/submissions/fc6ee23f-fa3a-4d00-a2fe-423b07b05e41

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

private theorem p21_mem_Qbar_iff {z : ℂ} : z ∈ Qbar ↔ IsAlgebraic ℚ z := by
  simp [Qbar, mem_algebraicClosure_iff]

private theorem p21_alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  have := (isAlgebraic_algHom_iff
      ((Complex.conjAe.restrictScalars ℚ).toAlgHom) (Complex.conjAe.injective)).mpr h
  simpa using this

open Diaz in
theorem solution {u : ℂ} (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) (hmod : IsAlgebraic ℚ (u * conj u)) :
    (conj u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp (conj u)) ∧
        IsAlgebraic ℚ (conj u * conj (conj u))) ∧
      ∀ q : ℚ, q ≠ 0 →
        ((q : ℂ) * u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp ((q : ℂ) * u)) ∧
          IsAlgebraic ℚ (((q : ℂ) * u) * conj ((q : ℂ) * u))) := by
  refine ⟨⟨by simpa using hu, ?_, ?_⟩, ?_⟩
  · rw [Complex.exp_conj]; exact p21_alg_conj hexp
  · have e : conj u * conj (conj u) = u * conj u := by rw [Complex.conj_conj]; ring
    rw [e]; exact hmod
  · intro q hq
    have hqc : ((q : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hq
    refine ⟨mul_ne_zero hqc hu, ?_, ?_⟩
    · have hd0 : ((q.den : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
      have hcast : ((q.den : ℕ) : ℂ) * ((q : ℚ) : ℂ) = ((q.num : ℤ) : ℂ) := by
        rw [Rat.cast_def]; field_simp
      have key : Complex.exp (((q : ℚ) : ℂ) * u) ^ (q.den : ℕ)
          = Complex.exp u ^ (q.num : ℤ) := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul]
        congr 1
        rw [← mul_assoc, hcast]
      have halg : IsAlgebraic ℚ (Complex.exp u ^ (q.num : ℤ)) :=
        p21_mem_Qbar_iff.mp (Qbar.zpow_mem (p21_mem_Qbar_iff.mpr hexp) q.num)
      rw [← key] at halg
      exact halg.of_pow q.pos
    · have hcq : conj ((q : ℚ) : ℂ) = ((q : ℚ) : ℂ) := by simp
      have e : (((q : ℚ) : ℂ) * u) * conj (((q : ℚ) : ℂ) * u)
          = ((q : ℚ) : ℂ) ^ 2 * (u * conj u) := by
        rw [map_mul, hcq]; ring
      rw [e]
      exact p21_mem_Qbar_iff.mp
        (Qbar.mul_mem (Qbar.pow_mem (p21_mem_Qbar_iff.mpr (isAlgebraic_ratCast (A := ℂ) ℚ q)) 2)
          (p21_mem_Qbar_iff.mpr hmod))
