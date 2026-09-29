-- Prove2me | solution 1 for Diaz.elliptic_plane_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:12:03.682634+00:00
-- url     : https://prove2.me/submissions/2216a8e9-44c0-4d4f-8457-aeddb17bb162

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

private theorem alg_conj {x : ℂ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ (conj x) :=
  h.algHom ((starRingEnd ℂ).toRatAlgHom)

theorem solution {k : Subfield ℂ} (D : Set ℂ)
    (hkalg : ∀ γ ∈ k, IsAlgebraic ℚ γ)
    (hnorm : ∀ x ∈ D, IsAlgebraic ℚ (x * conj x))
    (hstab : ∀ x ∈ D, ∀ γ ∈ k, γ ≠ 0 → γ * x ∈ D)
    (hdist : ∀ x ∈ D, ∀ y ∈ D, x ≠ y →
      IsAlgebraic ℚ ((x - y) * conj (x - y)) → ∃ γ ∈ k, y = γ * x)
    {u v w : ℂ} (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D)
    (hind : ∀ γ ∈ k, v ≠ γ * u)
    {a b : ℂ} (ha : a ∈ k) (hb : b ∈ k) (hrep : w = a * u + b * v) :
    a = 0 ∨ b = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha0, hb0⟩ := hcon
  have hv0 : v ≠ 0 := by
    have := hind 0 k.zero_mem
    simpa using this
  have hau : a * u ∈ D := hstab u hu a ha ha0
  have hsub : w - a * u = b * v := by rw [hrep]; ring
  have hne : a * u ≠ w := by
    intro h
    have : b * v = 0 := by rw [← hsub, ← h]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hb0 h1
    · exact hv0 h1
  have halgd : IsAlgebraic ℚ ((a * u - w) * conj (a * u - w)) := by
    have he : (a * u - w) * conj (a * u - w)
        = (b * conj b) * (v * conj v) := by
      have h2 : a * u - w = -(b * v) := by rw [hsub.symm]; ring
      rw [h2, map_neg, map_mul]; ring
    rw [he]
    exact mem_algebraicClosure_iff.mp
      (mul_mem (mul_mem (mem_algebraicClosure_iff.mpr (hkalg b hb))
        (mem_algebraicClosure_iff.mpr (alg_conj (hkalg b hb))))
        (mem_algebraicClosure_iff.mpr (hnorm v hv)))
  obtain ⟨γ, hγk, hγ⟩ := hdist (a * u) hau w hw hne halgd
  apply hind ((γ - 1) * a / b) (by
    exact div_mem (mul_mem (sub_mem hγk k.one_mem) ha) hb)
  have : b * v = (γ - 1) * a * u := by
    rw [← hsub, hγ]; ring
  field_simp at this ⊢
  linear_combination this
