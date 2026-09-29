-- Prove2me | solution 1 for DiazModulus.ringHom_preserves_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T06:19:42.760133+00:00
-- url     : https://prove2.me/submissions/dde08781-b373-4307-8907-46dac403dde7

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

private theorem map_smul' (Φ : ℂ →+* ℂ)
    (hfix : ∀ a : ↥DiazModulus.Qbar, Φ (a : ℂ) = (a : ℂ))
    (a : ↥DiazModulus.Qbar) (z : ℂ) : Φ (a • z) = a • Φ z := by
  show Φ ((a : ℂ) * z) = (a : ℂ) * Φ z
  rw [map_mul, hfix]

open DiazModulus in
theorem solution {n : ℕ} (Φ : ℂ →+* ℂ)
    (hfix : ∀ a : ↥Qbar, Φ (a : ℂ) = (a : ℂ)) (x : Fin n → ℂ) :
    LinearIndependent (↥Qbar) x ↔ LinearIndependent (↥Qbar) (fun i => Φ (x i)) := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h g hg i
    refine h g ?_ i
    apply Φ.injective
    rw [map_zero, map_sum, ← hg]
    exact Finset.sum_congr rfl fun j _ => map_smul' Φ hfix (g j) (x j)
  · intro h g hg i
    refine h g ?_ i
    rw [← map_zero Φ, ← hg, map_sum]
    exact (Finset.sum_congr rfl fun j _ => map_smul' Φ hfix (g j) (x j)).symm
