-- Prove2me | solution 1 for Dubey1986.Inefficiency.Nstar_codim
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:50:15.856935+00:00
-- url     : https://prove2.me/submissions/771043fc-7917-4c88-b5a9-0e536c3eb86c

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

set_option autoImplicit false
open Dubey1986.Inefficiency

theorem solution {n : ℕ} (k : Fin n → ℕ) :
    Module.finrank ℝ (Nstar k) + ∑ i, k i = n * ∑ i, k i := by
  -- the restriction map `A ↦ (A_i ∘ ι_i)_i`
  let Φ : (Fin n → (Strat k →L[ℝ] ℝ)) →ₗ[ℝ] (∀ i, (Fin (k i) → ℝ) →ₗ[ℝ] ℝ) :=
    { toFun := fun A i => (A i).toLinearMap.comp (LinearMap.single ℝ (fun i => Fin (k i) → ℝ) i)
      map_add' := by intro A B; funext i; ext v; simp
      map_smul' := by intro c A; funext i; ext v; simp }
  have hker : LinearMap.ker Φ = Nstar k := by
    ext A
    simp only [LinearMap.mem_ker, Φ, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · intro h i v
      have := LinearMap.congr_fun (congrFun h i) v
      simpa using this
    · intro h
      funext i
      refine LinearMap.ext fun v => ?_
      simpa using h i v
  have hsurj : Function.Surjective Φ := by
    intro ψ
    refine ⟨fun i => (ψ i).toContinuousLinearMap.comp (ContinuousLinearMap.proj i), ?_⟩
    funext i
    refine LinearMap.ext fun v => ?_
    simp [Φ]
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrn
  have h1 : Module.finrank ℝ (∀ i, (Fin (k i) → ℝ) →ₗ[ℝ] ℝ) = ∑ i, k i := by
    rw [Module.finrank_pi_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.finrank_linearMap_self, Module.finrank_fin_fun]
  have hE : Module.finrank ℝ (Strat k) = ∑ i, k i := by
    rw [Module.finrank_pi_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.finrank_fin_fun]
  have h2 : Module.finrank ℝ (Fin n → (Strat k →L[ℝ] ℝ)) = n * ∑ i, k i := by
    rw [Module.finrank_pi_fintype]
    have : ∀ i : Fin n, Module.finrank ℝ (Strat k →L[ℝ] ℝ) = ∑ i, k i := by
      intro _
      rw [← LinearMap.toContinuousLinearMap.finrank_eq, Module.finrank_linearMap_self, hE]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h1, h2] at hrn
  omega
