-- Prove2me | solution 1 for Disjunctive.NormalForms.convex_hull_intersection_subset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:19:22.434081+00:00
-- url     : https://prove2.me/submissions/7c7d9fe2-6424-494f-8e75-8de2c1b5999e

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

set_option autoImplicit false

open Disjunctive.NormalForms in
theorem solution {n : ℕ} {Q1 Q2 : Type*} [Fintype Q1] [Fintype Q2]
    (m1 : Q1 → ℕ) (A1 : (i : Q1) → Matrix (Fin (m1 i)) (Fin n) ℝ) (b1 : (i : Q1) → Fin (m1 i) → ℝ)
    (m2 : Q2 → ℕ) (A2 : (i : Q2) → Matrix (Fin (m2 i)) (Fin n) ℝ) (b2 : (i : Q2) → Fin (m2 i) → ℝ) :
    closure (convexHull ℝ
        ((⋃ i : Q1, Poly (A1 i) (b1 i)) ∩ (⋃ i : Q2, Poly (A2 i) (b2 i)))) ⊆
      closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
        closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i))) := by
  exact Set.subset_inter (closure_mono (convexHull_mono Set.inter_subset_left))
    (closure_mono (convexHull_mono Set.inter_subset_right))
