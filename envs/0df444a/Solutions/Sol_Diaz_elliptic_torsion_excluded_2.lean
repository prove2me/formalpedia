-- Prove2me | solution 2 for Diaz.elliptic_torsion_excluded
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:16:30.909986+00:00
-- url     : https://prove2.me/submissions/38034568-2a5a-4c15-be32-81f8f741b39e

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_elliptic_axis_alignment

open ComplexConjugate
open Diaz

namespace S7W1_elliptic_torsion_excluded

theorem alg_conj {x : ℂ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ (conj x) :=
  h.algHom ((starRingEnd ℂ).toRatAlgHom)

end S7W1_elliptic_torsion_excluded

open S7W1_elliptic_torsion_excluded in
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
  refine (Diaz.elliptic_axis_alignment hu hcon).2 (conj α * lam / α) ?_ hcu
  exact mem_algebraicClosure_iff.mp
    (div_mem (mul_mem (mem_algebraicClosure_iff.mpr (alg_conj hα))
      (mem_algebraicClosure_iff.mpr hlam)) (mem_algebraicClosure_iff.mpr hα))

#print axioms solution
