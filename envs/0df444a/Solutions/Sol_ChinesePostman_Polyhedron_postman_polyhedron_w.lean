-- Prove2me | solution 1 for ChinesePostman.Polyhedron.postman_polyhedron_w
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:08:55.211905+00:00
-- url     : https://prove2.me/submissions/9d54ccee-7a62-4f74-ad6b-87cb6b5535c3

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_ChinesePostman_Polyhedron_Setting
import Theorems.Thm_ChinesePostman_Polyhedron_postman_polyhedron
import Theorems.Thm_ChinesePostman_Polyhedron_w_nonneg_automatic

open Classical
open ChinesePostman.Polyhedron

private noncomputable def wLinear {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.Polyhedron.Graph V E) : (E → ℝ) →ₗ[ℝ] ((E → ℝ) × (V → ℝ)) where
  toFun v := (v, fun n => incidentSum G v n / 2)
  map_add' u v := by
    ext e
    · rfl
    · change incidentSum G (u + v) e / 2 = incidentSum G u e / 2 + incidentSum G v e / 2
      unfold incidentSum
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      ring
  map_smul' c v := by
    ext e
    · rfl
    · change incidentSum G (c • v) e / 2 = c * (incidentSum G v e / 2)
      unfold incidentSum
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring

private noncomputable def wAffine {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.Polyhedron.Graph V E) : (E → ℝ) →ᵃ[ℝ] ((E → ℝ) × (V → ℝ)) where
  toFun x := (x, fun n => (incidentSum G x n - (bParity G n : ℝ)) / 2)
  linear := wLinear G
  map_vadd' p v := by
    ext e
    · rfl
    · change (incidentSum G (v + p) e - (bParity G e : ℝ)) / 2 =
        incidentSum G v e / 2 + (incidentSum G p e - (bParity G e : ℝ)) / 2
      unfold incidentSum
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      ring

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.Polyhedron.Graph V E) :
    convexHull ℝ (wParityPoints G) = wPostmanPolyhedron G := by
  have hw_eq : wParityPoints G = wAffine G '' (parityPoints G) := by
    ext p
    constructor
    · rintro ⟨z, u, hz, _, h33, rfl⟩
      refine ⟨fun e => (z e : ℝ), ⟨z, hz, fun n => ?_, rfl⟩, ?_⟩
      · have h := h33 n
        change incidentSum G z n % 2 = bParity G n % 2
        omega
      · ext e
        · rfl
        · change (incidentSum G (fun e => (z e : ℝ)) e - (bParity G e : ℝ)) / 2 = (u e : ℝ)
          have hcast : incidentSum G (fun e => (z e : ℝ)) e = ((incidentSum G z e : ℤ) : ℝ) := by
            unfold incidentSum
            push_cast
            rfl
          have h33_real : ((incidentSum G z e : ℤ) : ℝ) - 2 * (u e : ℝ) = (bParity G e : ℝ) := by
            exact_mod_cast h33 e
          linarith
    · rintro ⟨x, ⟨z, hz, hpar, rfl⟩, rfl⟩
      let u : V → ℤ := fun n => (incidentSum G z n - bParity G n) / 2
      have h33 : ∀ n, incidentSum G z n - 2 * u n = bParity G n := by
        intro n
        have hmod : incidentSum G z n % 2 = bParity G n % 2 := hpar n
        dsimp [u]
        omega
      have hu : ∀ n, 0 ≤ u n := w_nonneg_automatic G z u hz h33
      refine ⟨z, u, hz, hu, h33, ?_⟩
      ext e
      · rfl
      · change (incidentSum G (fun e => (z e : ℝ)) e - (bParity G e : ℝ)) / 2 = (u e : ℝ)
        have hcast : incidentSum G (fun e => (z e : ℝ)) e = ((incidentSum G z e : ℤ) : ℝ) := by
          unfold incidentSum
          push_cast
          rfl
        have h33_real : ((incidentSum G z e : ℤ) : ℝ) - 2 * (u e : ℝ) = (bParity G e : ℝ) := by
          exact_mod_cast h33 e
        linarith
  have h_w_nonneg : ∀ p ∈ convexHull ℝ (wParityPoints G), ∀ n, 0 ≤ p.2 n := by
    have hsub : wParityPoints G ⊆ {p : (E → ℝ) × (V → ℝ) | ∀ n, 0 ≤ p.2 n} := by
      rintro p ⟨z, u, _, hu, _, rfl⟩ n
      change (0 : ℝ) ≤ (u n : ℝ)
      exact_mod_cast hu n
    have hconv : Convex ℝ {p : (E → ℝ) × (V → ℝ) | ∀ n, 0 ≤ p.2 n} := by
      intro p hp q hq a b ha hb _ n
      exact add_nonneg (mul_nonneg ha (hp n)) (mul_nonneg hb (hq n))
    exact convexHull_min hsub hconv
  have h_hull : convexHull ℝ (wParityPoints G) = wAffine G '' (postmanPolyhedron G) := by
    rw [hw_eq, ← AffineMap.image_convexHull, postman_polyhedron G]
  ext p
  constructor
  · intro hp
    have hp2 : ∀ n, 0 ≤ p.2 n := h_w_nonneg p hp
    rw [h_hull] at hp
    rcases hp with ⟨x, ⟨hx1, hx_cut⟩, rfl⟩
    refine ⟨hx1, hp2, fun n => ?_, hx_cut⟩
    change incidentSum G x n - 2 * ((incidentSum G x n - (bParity G n : ℝ)) / 2) = (bParity G n : ℝ)
    ring
  · rintro ⟨hp1, _, hp33, hp_cut⟩
    rw [h_hull]
    refine ⟨p.1, ⟨hp1, hp_cut⟩, ?_⟩
    ext e
    · rfl
    · change (incidentSum G p.1 e - (bParity G e : ℝ)) / 2 = p.2 e
      have := hp33 e
      linarith
