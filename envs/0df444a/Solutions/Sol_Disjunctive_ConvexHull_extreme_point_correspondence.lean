-- Prove2me | solution 1 for Disjunctive.ConvexHull.extreme_point_correspondence
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:00:38.318221+00:00
-- url     : https://prove2.me/submissions/c35db0b0-1abe-442b-8375-2e767c09a19e

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

set_option autoImplicit false

namespace Cex64ed

open Disjunctive.ConvexHull

/-- Two disjuncts in `ℝ¹`, each with two rows. -/
abbrev mC : Fin 2 → ℕ := fun _ => 2

/-- Both disjuncts use the rows `x ≥ ·` and `-x ≥ ·`. -/
def AC : (h : Fin 2) → Matrix (Fin (mC h)) (Fin 1) ℝ := fun _ => !![1; -1]

/-- `P₀ = {0}` (rows `x ≥ 0`, `-x ≥ 0`), `P₁ = [-1, 1]` (rows `x ≥ -1`, `-x ≥ -1`). -/
def bC : (h : Fin 2) → Fin (mC h) → ℝ := fun h => if h = 0 then (fun _ => 0) else (fun _ => -1)

theorem mv_AC (h : Fin 2) (v : Fin 1 → ℝ) (i : Fin 2) :
    (AC h).mulVec v i = (if i = 0 then v 0 else -v 0) := by
  fin_cases i <;> simp [AC, Matrix.mulVec, dotProduct]

theorem bC_val (h : Fin 2) (i : Fin 2) : bC h i = (if h = 0 then 0 else -1) := by
  fin_cases h <;> simp [bC]

theorem feasible_all (h : Fin 2) : h ∈ FeasibleIndices mC AC bC := by
  refine ⟨0, fun i => ?_⟩
  rw [mv_AC, bC_val]
  fin_cases h <;> fin_cases i <;> simp

/-- The constraint for disjunct `h` in coordinates. -/
theorem cons_iff (h : Fin 2) (v : Fin 1 → ℝ) (t : ℝ) :
    0 ≤ (AC h).mulVec v - t • bC h ↔
      (0 ≤ v 0 + (if h = 0 then 0 else t) ∧ 0 ≤ -v 0 + (if h = 0 then 0 else t)) := by
  constructor
  · intro H
    have h0 := H 0
    have h1 := H 1
    simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mv_AC, bC_val] at h0 h1
    fin_cases h <;> simp at h0 h1 ⊢ <;> constructor <;> linarith
  · rintro ⟨H0, H1⟩ i
    simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mv_AC, bC_val]
    fin_cases h <;> fin_cases i <;> simp at H0 H1 ⊢ <;> linarith

/-- The lifted point `x = 0`, `y = 0`, `y₀ = (1, 0)`. -/
def ptC : (Fin 1 → ℝ) × ((Fin 2 → Fin 1 → ℝ) × (Fin 2 → ℝ)) := (0, (0, Pi.single 0 1))

/-- Every lifted point with `y₀ 1 = 0` is `ptC`. -/
theorem eq_of_t1 (p : (Fin 1 → ℝ) × ((Fin 2 → Fin 1 → ℝ) × (Fin 2 → ℝ)))
    (hp : p ∈ LiftedPolyhedron mC AC bC (FeasibleIndices mC AC bC)) (ht : p.2.2 1 = 0) :
    p = ptC := by
  obtain ⟨hx, hc, -, hs⟩ := hp
  obtain ⟨c0, -⟩ := hc 0 (feasible_all 0)
  obtain ⟨c1, -⟩ := hc 1 (feasible_all 1)
  rw [cons_iff] at c0 c1
  simp only [ht] at c1
  simp at c0 c1
  have hy0 : p.2.1 0 = 0 := by
    funext j; fin_cases j; simp; linarith [c0.1, c0.2]
  have hy1 : p.2.1 1 = 0 := by
    funext j; fin_cases j; simp; linarith [c1.1, c1.2]
  have hy : p.2.1 = 0 := by
    funext h; fin_cases h
    · simpa using hy0
    · simpa using hy1
  have ht0 : p.2.2 0 = 1 := by
    rw [Fin.sum_univ_two, ht] at hs; simpa using hs
  have htt : p.2.2 = Pi.single 0 1 := by
    funext h; fin_cases h
    · simpa using ht0
    · simpa using ht
  obtain ⟨x, y, t⟩ := p
  simp only at hx hy htt
  subst hy htt
  simp only [Pi.zero_apply, Finset.sum_const_zero] at hx
  subst hx
  rfl

theorem ptC_mem : ptC ∈ LiftedPolyhedron mC AC bC (FeasibleIndices mC AC bC) := by
  refine ⟨?_, fun h _ => ⟨?_, ?_⟩, fun h hh => absurd (feasible_all h) hh, ?_⟩
  · simp [ptC]
  · rw [cons_iff]; fin_cases h <;> simp [ptC]
  · fin_cases h <;> simp [ptC]
  · simp [ptC, Fin.sum_univ_two]

theorem ptC_extreme :
    ptC ∈ Set.extremePoints ℝ (LiftedPolyhedron mC AC bC (FeasibleIndices mC AC bC)) := by
  rw [mem_extremePoints]
  refine ⟨ptC_mem, fun p1 hp1 p2 hp2 hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have nn1 : 0 ≤ p1.2.2 1 := (hp1.2.1 1 (feasible_all 1)).2
  have nn2 : 0 ≤ p2.2.2 1 := (hp2.2.1 1 (feasible_all 1)).2
  have hz : a * p1.2.2 1 + b * p2.2.2 1 = 0 := by
    have := congrArg (fun q => q.2.2 1) he
    simpa [ptC] using this
  have h1 : p1.2.2 1 = 0 := by nlinarith [mul_nonneg ha.le nn1, mul_nonneg hb.le nn2]
  have h2 : p2.2.2 1 = 0 := by nlinarith [mul_nonneg ha.le nn1, mul_nonneg hb.le nn2]
  exact ⟨eq_of_t1 p1 hp1 h1, eq_of_t1 p2 hp2 h2⟩

theorem zero_not_extreme :
    (0 : Fin 1 → ℝ) ∉ Set.extremePoints ℝ (closure (convexHull ℝ (DisjunctiveSet mC AC bC))) := by
  intro hz
  rw [mem_extremePoints] at hz
  have hm : (fun _ => (-1 : ℝ)) ∈ DisjunctiveSet mC AC bC := by
    refine Set.mem_iUnion.2 ⟨1, fun i => ?_⟩
    rw [mv_AC, bC_val]; fin_cases i <;> simp
  have hp : (fun _ => (1 : ℝ)) ∈ DisjunctiveSet mC AC bC := by
    refine Set.mem_iUnion.2 ⟨1, fun i => ?_⟩
    rw [mv_AC, bC_val]; fin_cases i <;> simp
  have := hz.2 _ (subset_closure (subset_convexHull ℝ _ hm))
    _ (subset_closure (subset_convexHull ℝ _ hp))
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by funext i; simp⟩
  have := congrFun this.1 0
  norm_num at this

end Cex64ed

theorem solution : ¬ (∀ {n : ℕ} {Q : Type} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ),
    (∀ xstar ∈ Set.extremePoints ℝ (closure (convexHull ℝ (Disjunctive.ConvexHull.DisjunctiveSet m A b))),
      ∃ k ∈ Disjunctive.ConvexHull.FeasibleIndices m A b, ∃ y : Q → Fin n → ℝ, ∃ y0 : Q → ℝ,
        (xstar, (y, y0)) ∈ Set.extremePoints ℝ (Disjunctive.ConvexHull.LiftedPolyhedron m A b (Disjunctive.ConvexHull.FeasibleIndices m A b)) ∧
        y k = xstar ∧ y0 k = 1 ∧ ∀ h, h ≠ k → y h = 0 ∧ y0 h = 0)
    ∧
    (∀ (xbar : Fin n → ℝ) (y : Q → Fin n → ℝ) (y0 : Q → ℝ),
      (xbar, (y, y0)) ∈ Set.extremePoints ℝ (Disjunctive.ConvexHull.LiftedPolyhedron m A b (Disjunctive.ConvexHull.FeasibleIndices m A b)) →
      ∃ k ∈ Disjunctive.ConvexHull.FeasibleIndices m A b, y k = xbar ∧ y0 k = 1 ∧ (∀ h, h ≠ k → y h = 0 ∧ y0 h = 0) ∧
        xbar ∈ Set.extremePoints ℝ (closure (convexHull ℝ (Disjunctive.ConvexHull.DisjunctiveSet m A b))))) := by
  intro H
  obtain ⟨k, -, -, -, -, hx⟩ :=
    (H Cex64ed.mC Cex64ed.AC Cex64ed.bC).2 0 0 (Pi.single 0 1) Cex64ed.ptC_extreme
  exact Cex64ed.zero_not_extreme hx
