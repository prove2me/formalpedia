-- Prove2me | solution 1 for CompOT.Metric.prop_2_2_symm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:20:24.66197+00:00
-- url     : https://prove2.me/submissions/204e4901-0361-461d-9aa4-19abdea2f896

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

set_option autoImplicit false
open Matrix CompOT.Metric

theorem solution {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a b : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) :
    W D p a b = W D p b a := by
  have hsymm : ∀ i j, powCost D p i j = powCost D p j i := by
    intro i j; simp [powCost, hD_symm i j]
  have key : ∀ (x y : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ),
      P ∈ CompOT.Assignment.couplings x y → Pᵀ ∈ CompOT.Assignment.couplings y x := by
    rintro x y P ⟨h0, hr, hc⟩
    exact ⟨fun i j => h0 j i, fun i => by simpa using hc i, fun j => by simpa using hr j⟩
  have hf : ∀ P : Matrix (Fin n) (Fin n) ℝ,
      CompOT.Assignment.frob (powCost D p) Pᵀ = CompOT.Assignment.frob (powCost D p) P := by
    intro P
    unfold CompOT.Assignment.frob
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.transpose_apply, hsymm j i]
  have hset : (Set.range fun P : CompOT.Assignment.couplings a b =>
        CompOT.Assignment.frob (powCost D p) (P : Matrix (Fin n) (Fin n) ℝ)) =
      Set.range fun P : CompOT.Assignment.couplings b a =>
        CompOT.Assignment.frob (powCost D p) (P : Matrix (Fin n) (Fin n) ℝ) := by
    ext v
    constructor
    · rintro ⟨⟨P, hP⟩, rfl⟩
      exact ⟨⟨Pᵀ, key a b P hP⟩, hf P⟩
    · rintro ⟨⟨P, hP⟩, rfl⟩
      exact ⟨⟨Pᵀ, key b a P hP⟩, hf P⟩
  unfold W otCost
  congr 1
  change sInf _ = sInf _
  rw [hset]
