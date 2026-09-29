-- Prove2me | solution 1 for ClarkeGradients.MaxFunctions.maxFunction_lipschitzOnBounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:42:56.703062+00:00
-- url     : https://prove2.me/submissions/596ae73a-f780-4dc3-b0c3-bc63c601dfca

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction

namespace ClarkeGradients.MaxFunctions

open Filter Topology in
theorem aux_mfl_bddAbove {U : Type*} [TopologicalSpace U] [SeqCompactSpace U]
    (h : U → ℝ) (hh : UpperSemicontinuous h) : BddAbove (Set.range h) := by
  by_contra hne
  rw [not_bddAbove_iff] at hne
  have hk : ∀ k : ℕ, ∃ u : U, (k : ℝ) < h u := by
    intro k
    obtain ⟨y, ⟨u, rfl⟩, hy⟩ := hne (k : ℝ)
    exact ⟨u, hy⟩
  choose u hu using hk
  obtain ⟨a, φ, hφ, hlim⟩ := SeqCompactSpace.tendsto_subseq u
  have h1 : ∀ᶠ k in atTop, h (u (φ k)) < h a + 1 :=
    hlim.eventually (hh a (h a + 1) (lt_add_one _))
  obtain ⟨N, hN⟩ := exists_nat_gt (h a + 1)
  obtain ⟨k, hk1, hk2⟩ := (h1.and (eventually_ge_atTop N)).exists
  have hφk : N ≤ φ k := le_trans hk2 (hφ.id_le k)
  have : (N : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφk
  have := hu (φ k)
  linarith

open Filter Topology in
theorem aux_mfl_usc_slice {n : ℕ} {U : Type*} [TopologicalSpace U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (x : EuclideanSpace ℝ (Fin n)) : UpperSemicontinuous (g x) := by
  intro u c hc
  have hcont : Continuous (fun v : U => (x, v)) := Continuous.prodMk_right x
  exact hcont.tendsto u |>.eventually (ha (x, u) c hc)

end ClarkeGradients.MaxFunctions

open ClarkeGradients ClarkeGradients.MaxFunctions

theorem solution
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B) :
    Shared.LipschitzOnBounded (maxFunction g) := by
  intro B hB
  obtain ⟨K, hK⟩ := hb B hB
  refine ⟨K, LipschitzOnWith.of_le_add_mul K ?_⟩
  intro x hx y hy
  have hbdd : BddAbove (Set.range (g y)) :=
    aux_mfl_bddAbove (g y) (aux_mfl_usc_slice g ha y)
  unfold maxFunction
  refine ciSup_le fun u => ?_
  have h1 : dist (g x u) (g y u) ≤ K * dist x y := (hK u).dist_le_mul x hx y hy
  rw [Real.dist_eq] at h1
  have h2 : g y u ≤ ⨆ v, g y v := le_ciSup hbdd u
  have h3 := le_abs_self (g x u - g y u)
  linarith
