-- Prove2me | solution 1 for ConvexOptimization.newton_elimination_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-15T14:35:55.055021+00:00
-- url     : https://prove2.me/submissions/ac06426a-8e8e-4a87-86ed-9420ebb09281

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n q p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (a : Fin p → EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin n))
    -- F parametrizes the constraint null space: ran F = {v | Av = 0}
    (hF : ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ j, ⟪a j, v⟫ = 0) ↔ v ∈ Set.range F)
    (xhat : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin q))
    (Δz : EuclideanSpace ℝ (Fin q))
    -- Δz solves the reduced Newton system Fᵀ H F Δz = −Fᵀ g at x = F z + x̂:
    (hΔz : ∀ w : EuclideanSpace ℝ (Fin q),
      ⟪H (F z + xhat) (F Δz), F w⟫ = -⟪g (F z + xhat), F w⟫) :
    -- then Δx = F Δz solves the KKT system (10.12): stationarity with some ν,
    -- and primal feasibility of the step direction (A Δx = 0):
    (∃ ν : Fin p → ℝ,
      g (F z + xhat) + H (F z + xhat) (F Δz) + ∑ j, ν j • a j = 0) ∧
    ∀ j, ⟪a j, F Δz⟫ = 0 := by
  -- Feasibility of the step direction is immediate: `F Δz` lies in `ran F`,
  -- which by hypothesis is exactly the null space of the constraint map.
  have hfeas : ∀ j, ⟪a j, F Δz⟫ = 0 := (hF (F Δz)).mpr ⟨Δz, rfl⟩
  refine ⟨?_, hfeas⟩
  set x := F z + xhat with hxdef
  set r := g x + H x (F Δz) with hrdef
  -- The reduced Newton equation says exactly that the residual `r` is
  -- orthogonal to the range of `F`.
  have hperp : ∀ w : EuclideanSpace ℝ (Fin q), ⟪r, F w⟫ = 0 := by
    intro w
    have h := hΔz w
    rw [hrdef, inner_add_left, h]
    ring
  -- Hence `r` is orthogonal to the orthogonal complement of `span {a j}`,
  -- so `r` itself lies in that span.
  set V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.range a) with hVdef
  have haV : ∀ j, a j ∈ V := fun j => Submodule.subset_span (Set.mem_range_self j)
  have hrV : r ∈ V := by
    rw [← Submodule.orthogonal_orthogonal V]
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu0 : ∀ j, ⟪a j, u⟫ = 0 := fun j =>
      (Submodule.mem_orthogonal V u).mp hu (a j) (haV j)
    obtain ⟨w, hw⟩ := (hF u).mp hu0
    rw [real_inner_comm, ← hw]
    exact hperp w
  -- Write `r` as a nonnegative-index linear combination of the `a j`.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hrV
  refine ⟨fun j => -c j, ?_⟩
  have hsum : ∑ j, (-c j) • a j = -r := by
    rw [← hc, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [neg_smul]
  rw [hsum, add_neg_cancel]
