-- Prove2me | solution 1 for FiniteIndexRep.forall_isSemisimple_iff_forall_mem_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T19:05:26.529854+00:00
-- url     : https://prove2.me/submissions/8110fcc9-e5de-4226-a0ad-f2459309f9a7

import Mathlib

open Polynomial

set_option autoImplicit false

private theorem separable_comp_X_pow {k : Type*} [Field k] [CharZero k]
    {p : k[X]} (hp : p.Separable) (hp0 : p.coeff 0 ≠ 0) {n : ℕ} (hn : 0 < n) :
    (p.comp (X ^ n)).Separable := by
  let q : k[X] := p.comp (X ^ n)
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa [q, coeff_zero_eq_eval_zero, eval_comp, Nat.ne_zero_of_lt hn] using hp0
  have hX : IsCoprime q (X : k[X]) :=
    ((irreducible_X : Irreducible (X : k[X])).coprime_iff_not_dvd.mpr
      (mt X_dvd_iff.mp hq0)).symm
  have hC : IsCoprime q (C (n : k)) := by
    have hn' : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨0, C (n : k)⁻¹, ?_⟩
    rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hn', C_1]
  have hD : IsCoprime q (p.derivative.comp (X ^ n)) :=
    IsCoprime.map hp (compRingHom (X ^ n))
  rw [separable_def, derivative_comp, derivative_X_pow]
  exact (hC.mul_right (hX.pow_right (n := n - 1))).mul_right hD

theorem solution {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) (H : Subgroup G)
    [H.FiniteIndex] :
    (∀ g : G, Module.End.IsSemisimple (ρ g)) ↔ ∀ h ∈ H, Module.End.IsSemisimple (ρ h) := by
  refine ⟨fun h g _ => h g, fun h g => ?_⟩
  obtain ⟨n, hn, _, hmem⟩ := H.exists_pow_mem_of_index_ne_zero
    Subgroup.FiniteIndex.index_ne_zero g
  have hs : Module.End.IsSemisimple ((ρ g) ^ n) := by simpa only [map_pow] using h _ hmem
  have hu : IsUnit ((ρ g) ^ n) := by
    rw [← map_pow, ← ρ.asGroupHom_apply]
    exact Units.isUnit _
  have hInj : Function.Injective ((ρ g) ^ n) :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hu)
  let p := minpoly k ((ρ g) ^ n)
  have hp : p.Separable := PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree
  have hp0 : p.coeff 0 ≠ 0 := LinearMap.minpoly_coeff_zero_of_injective hInj
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (separable_comp_X_pow hp hp0 hn).squarefree
  rw [aeval_comp, map_pow, aeval_X]
  exact minpoly.aeval _ _
