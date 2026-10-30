-- Prove2me | solution 1 for ExactPenGNEP.NonShared.proposition_3_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:42:38.179761+00:00
-- url     : https://prove2.me/submissions/d67deec0-d63b-4417-a0f0-131c35436707

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync ExactPenGNEP.NonShared

theorem solution {N : ℕ} {n : Fin N → ℕ} (C : ∀ ν, Set (Strat n ν))
    (X : ∀ ν, Profile n → Set (Strat n ν)) (θ r : Fin N → Profile n → ℝ) (ρ : ℝ) (x : Profile n)
    (hX : ∀ ν (z : Profile n) (y : Strat n ν), X ν (Function.update z ν y) = X ν z)
    (hC : IsClosed (Set.univ.pi C)) (hgraph : IsClosed {z : Profile n | inGraph X z})
    (hr : ∀ ν (z : Profile n), (∀ ν' ≠ ν, z ν' ∈ C ν') →
      IsResidual (fun y => r ν (Function.update z ν y)) (X ν z) (C ν))
    (hρ : 0 < ρ) (hx : IsNashEq C (fun ν y => θ ν y + ρ * r ν y) x) :
    IsGNE C X θ x ↔ inGraph X x := by
  obtain ⟨hxC, hmin⟩ := hx
  have hxC' : ∀ ν, x ν ∈ C ν := fun ν => hxC ν (Set.mem_univ _)
  constructor
  · intro hG ν
    exact (hG ν).1.2
  · intro hG ν
    refine ⟨⟨hxC' ν, hG ν⟩, fun y hy => ?_⟩
    have hres := hr ν x (fun ν' _ => hxC' ν')
    have h1 : r ν x = 0 := by
      have := (hres.2 (x ν) (hxC' ν)).2 (hG ν)
      simpa [Function.update_eq_self] using this
    have h2 : r ν (Function.update x ν y) = 0 := (hres.2 y hy.1).2 hy.2
    have := hmin ν y hy.1
    simp only [h1, h2, mul_zero, add_zero] at this
    exact this
