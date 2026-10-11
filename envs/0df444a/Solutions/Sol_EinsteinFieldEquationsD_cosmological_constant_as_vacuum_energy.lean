-- Prove2me | solution 1 for EinsteinFieldEquationsD.cosmological_constant_as_vacuum_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:07:57.361193+00:00
-- url     : https://prove2.me/submissions/c8a106ba-8948-4b6d-abd7-ea865eadd916

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_EinsteinFieldEquationsD_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open EinsteinFieldEquationsD

theorem solution {D : ℕ} (g T : Tensor2 D) (U : Set (Coord D))
    (Λ κ : ℝ) (hκ : κ ≠ 0) :
    EinsteinFieldEquationsOn g T Λ κ U ↔
      ∀ x ∈ U, ∀ a b : Fin D,
        einsteinTensor g x a b =
          κ * (T x a b + vacuumStressEnergy g Λ κ x a b) := by
  have hc : κ * (Λ / κ) = Λ := by field_simp [hκ]
  have halg (z w : ℝ) : κ * (z + -(Λ / κ) * w) = κ * z - Λ * w := by
    calc
      _ = κ * z - (κ * (Λ / κ)) * w := by ring
      _ = _ := by rw [hc]
  constructor
  · intro h x hx a b
    have he := h x hx a b
    change einsteinTensor g x a b + Λ * g x a b = κ * T x a b at he
    change einsteinTensor g x a b =
      κ * (T x a b + (-(Λ / κ) * g x a b))
    rw [halg]
    linarith
  · intro h x hx a b
    have he := h x hx a b
    change einsteinTensor g x a b =
      κ * (T x a b + (-(Λ / κ) * g x a b)) at he
    change einsteinTensor g x a b + Λ * g x a b =
      κ * T x a b
    rw [halg] at he
    linarith
