-- Prove2me | solution 1 for DirichletUnitTheorem.torsion_units_eq_roots_of_unity_finite_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:21:32.845236+00:00
-- url     : https://prove2.me/submissions/ce8e282c-a375-40b4-bbfc-63a72fc5c7f8

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K] :
    (∀ x : K, (∃ u : (𝓞 K)ˣ, IsOfFinOrder u ∧ ((u : 𝓞 K) : K) = x) ↔
        ∃ n : ℕ, 0 < n ∧ x ^ n = 1) ∧
      Finite (CommGroup.torsion (𝓞 K)ˣ) ∧ IsCyclic (CommGroup.torsion (𝓞 K)ˣ) := by
  refine ⟨fun x => ⟨?_, ?_⟩, inferInstanceAs (Finite (Units.torsion K)),
    inferInstanceAs (IsCyclic (Units.torsion K))⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨n, hn, hun⟩ := hu.exists_pow_eq_one
    refine ⟨n, hn, ?_⟩
    have := congrArg (fun v : (𝓞 K)ˣ => ((v : 𝓞 K) : K)) hun
    simpa using this
  · rintro ⟨n, hn, hx⟩
    have hint : IsIntegral ℤ x := by
      refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', ?_⟩
      simp [hx]
    let y : 𝓞 K := ⟨x, hint⟩
    have hy : y ^ n = 1 := by
      apply RingOfIntegers.coe_injective
      rw [map_pow, map_one]
      exact hx
    let u : (𝓞 K)ˣ := Units.ofPowEqOne y n hy hn.ne'
    refine ⟨u, ?_, rfl⟩
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Units.pow_ofPowEqOne hy hn.ne'⟩
