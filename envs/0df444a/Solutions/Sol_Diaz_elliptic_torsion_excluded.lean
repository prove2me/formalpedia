-- Prove2me | solution 1 for Diaz.elliptic_torsion_excluded
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:12:02.8018+00:00
-- url     : https://prove2.me/submissions/0102f922-b8ee-44a9-b6b8-209ff5fa0d18

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

private theorem alg_conj {x : ℂ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ (conj x) :=
  h.algHom ((starRingEnd ℂ).toRatAlgHom)

private theorem elliptic_axis_alignment {u : ℂ} (hu : ¬ IsAlgebraic ℚ u)
    (hn : IsAlgebraic ℚ (u * conj u)) :
    (conj u ≠ u ∧ conj u ≠ -u) ∧ ∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u := by
  have key : ∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u := by
    intro γ hγ hcon
    have hu0 : u ≠ 0 := by rintro rfl; exact hu (isAlgebraic_zero)
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      apply hu0
      have h0 : conj u = 0 := by rw [hcon]; ring
      have := congrArg (starRingEnd ℂ) h0
      simpa using this
    have h1 : u * conj u = γ * u ^ 2 := by rw [hcon]; ring
    have h2 : (u : ℂ) ^ 2 = (u * conj u) / γ := by rw [h1]; field_simp
    have h3 : IsAlgebraic ℚ ((u : ℂ) ^ 2) := by
      rw [h2]
      exact mem_algebraicClosure_iff.mp
        (div_mem (mem_algebraicClosure_iff.mpr hn) (mem_algebraicClosure_iff.mpr hγ))
    exact hu (h3.of_pow (by norm_num))
  refine ⟨⟨?_, ?_⟩, key⟩
  · intro h; exact key 1 isAlgebraic_one (by simpa using h)
  · intro h; exact key (-1) (isAlgebraic_one.neg) (by simpa using h)

theorem solution {ω lam α : ℂ} (hω : ¬ IsAlgebraic ℚ ω)
    (hlam : IsAlgebraic ℚ lam) (hcω : conj ω = lam * ω)
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) :
    ¬ IsAlgebraic ℚ ((α * ω) * conj (α * ω)) := by
  intro hcon
  have hu : ¬ IsAlgebraic ℚ (α * ω) := by
    intro h
    apply hω
    have : ω = (α * ω) / α := by field_simp
    rw [this]
    exact mem_algebraicClosure_iff.mp
      (div_mem (mem_algebraicClosure_iff.mpr h) (mem_algebraicClosure_iff.mpr hα))
  have hcu : conj (α * ω) = (conj α * lam / α) * (α * ω) := by
    rw [map_mul, hcω]; field_simp
  refine (elliptic_axis_alignment hu hcon).2 (conj α * lam / α) ?_ hcu
  exact mem_algebraicClosure_iff.mp
    (div_mem (mul_mem (mem_algebraicClosure_iff.mpr (alg_conj hα))
      (mem_algebraicClosure_iff.mpr hlam)) (mem_algebraicClosure_iff.mpr hα))
