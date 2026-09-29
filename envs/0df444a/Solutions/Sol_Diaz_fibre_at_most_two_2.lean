-- Prove2me | solution 2 for Diaz.fibre_at_most_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:20:57.822685+00:00
-- url     : https://prove2.me/submissions/fb14c05b-beeb-45eb-9232-62e39c1d1059

/-
`Diaz.fibre_at_most_two`, routed through the two published nodes it uses.

Three points of one exponential fibre differ by integer multiples of `c = 2πi`,
so `z z̄` is a quadratic in that integer with leading coefficient `-c²`.  Three
values of a quadratic in `Q̄` pin down the leading coefficient — that is exactly
`Diaz.second_difference_mem` — so `π²` is algebraic, and
`Diaz.transcendental_of_candidate` applied to `πi` (whose exponential is `-1`)
contradicts it.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_transcendental_of_candidate
import Theorems.Thm_Diaz_second_difference_mem

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {α u v w : ℂ}
    (heu : Complex.exp u = α) (hev : Complex.exp v = α) (hew : Complex.exp w = α)
    (hqu : IsAlgebraic ℚ (u * conj u)) (hqv : IsAlgebraic ℚ (v * conj v))
    (hqw : IsAlgebraic ℚ (w * conj w))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : False := by
  have hmem : ∀ z : ℂ, IsAlgebraic ℚ z ↔ z ∈ Qbar := by
    intro z
    rw [Qbar, IntermediateField.mem_toSubfield, mem_algebraicClosure_iff]
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hev.trans heu.symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hew.trans heu.symm)
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
  have hc2 : conj (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hcc : conj c = -c := by
    rw [hc]; simp [Complex.conj_I, hc2]
  have hnorm : ∀ (z : ℂ) (k : ℤ), z = u + (k : ℂ) * c →
      z * conj z = (u * conj u) + (c * (conj u - u)) * (k : ℂ) + (-(c ^ 2)) * (k : ℂ) ^ 2 := by
    intro z k hz
    subst hz
    rw [map_add, map_mul, hcc]
    have hk : conj ((k : ℂ)) = (k : ℂ) := by simp
    rw [hk]
    ring
  have hu0 : (0 : ℤ) ≠ m := by
    intro h
    apply huv
    rw [hm, ← h]; simp
  have hu0' : (0 : ℤ) ≠ n := by
    intro h
    apply huw
    rw [hn, ← h]; simp
  have hmn : m ≠ n := by
    intro h
    apply hvw
    rw [hm, hn, h]
  have e0 := hnorm u 0 (by simp)
  have em := hnorm v m hm
  have en := hnorm w n hn
  have hd : (-(c ^ 2)) ∈ Qbar := by
    refine Diaz.second_difference_mem (K := Qbar) (ρ := u * conj u) (c := c * (conj u - u))
      (d := -(c ^ 2)) hu0 hu0' hmn ?_ ?_ ?_
    · rw [← e0]; exact (hmem _).mp hqu
    · rw [← em]; exact (hmem _).mp hqv
    · rw [← en]; exact (hmem _).mp hqw
  have hpi2 : ((Real.pi : ℂ) * Complex.I) ^ 2 ∈ Qbar := by
    have e : ((Real.pi : ℂ) * Complex.I) ^ 2 = -((-(c ^ 2)) / 4) := by
      rw [hc]; ring
    rw [e]
    exact Qbar.neg_mem (Qbar.div_mem hd (by simpa using Qbar.natCast_mem 4))
  have halg : IsAlgebraic ℚ ((Real.pi : ℂ) * Complex.I) :=
    IsAlgebraic.of_pow (by norm_num) ((hmem _).mpr hpi2)
  have hne : ((Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  have hexpI : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) * Complex.I)) := by
    rw [Complex.exp_pi_mul_I]
    exact (hmem _).mpr (Qbar.neg_mem Qbar.one_mem)
  exact Diaz.transcendental_of_candidate hne hexpI halg
