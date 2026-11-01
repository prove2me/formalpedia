-- Prove2me | solution 1 for CombOpt.ShortestPath.theorem_2_14
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:31:33.925882+00:00
-- url     : https://prove2.me/submissions/ab1695d2-846a-4108-887a-472aa5b4322f

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsLeastCostDipath
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsFeasiblePotential
import Definitions.Def_CombOpt_ShortestPath_pathCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open CombOpt.ShortestPath

theorem solution {V E : Type*} [Fintype V] [Fintype E] (G : Digraph V E) (c : E → ℝ)
    (r s : V) (h : ∀ v : V, ∃ P : List E, G.IsLeastCostDipath c r v P) :
    ∃ m : ℝ,
      IsLeast {x : ℝ | ∃ P : List E, G.IsDipath r P s ∧ x = pathCost c P} m ∧
      IsGreatest {x : ℝ | ∃ y : V → ℝ, G.IsFeasiblePotential c r y ∧ x = y s} m := by
  classical
  let Q : V → List E := fun v => Classical.choose (h v)
  have hQ (v : V) : G.IsLeastCostDipath c r v (Q v) :=
    Classical.choose_spec (h v)
  let y : V → ℝ := fun v => pathCost c (Q v)
  have hcost (A B : List E) :
      pathCost c (A ++ B) = pathCost c A + pathCost c B := by
    simp [pathCost, List.map_append, List.sum_append]
  have hconcat {u v w : V} {A B : List E}
      (hA : G.IsDipath u A v) (hB : G.IsDipath v B w) :
      G.IsDipath u (A ++ B) w := by
    induction hA with
    | nil a =>
        simpa using hB
    | @cons u v e A he hA ih =>
        exact Digraph.IsDipath.cons e (A ++ B) he (ih hB)
  have hupper (z : V → ℝ) (hz : G.IsFeasiblePotential c r z)
      {u v : V} {L : List E} (hL : G.IsDipath u L v) :
      z v ≤ z u + pathCost c L := by
    obtain ⟨hzpot, _⟩ := hz
    induction hL with
    | nil a =>
        simp [pathCost]
    | @cons u v e L he hL ih =>
        have hedge := hzpot e
        rw [he] at hedge
        have hcons : pathCost c (e :: L) = c e + pathCost c L := by
          simp [pathCost]
        rw [hcons]
        linarith
  have hroot_le : y r ≤ 0 := by
    have hh := (hQ r).2 [] (Digraph.IsDipath.nil r)
    simpa [y, pathCost] using hh
  have hroot_ge : 0 ≤ y r := by
    have hh := (hQ r).2 (Q r ++ Q r)
      (hconcat (hQ r).1 (hQ r).1)
    have hdouble : y r ≤ y r + y r := by
      simpa [y, hcost] using hh
    linarith
  have hroot : y r = 0 := le_antisymm hroot_le hroot_ge
  have hfeas : G.IsFeasiblePotential c r y := by
    refine ⟨?_, hroot⟩
    intro e
    have hh := (hQ (G.head e)).2 (Q (G.tail e) ++ [e])
      (hconcat (hQ (G.tail e)).1
        (Digraph.IsDipath.cons e [] rfl (Digraph.IsDipath.nil (G.head e))))
    have hedge : y (G.head e) ≤ y (G.tail e) + c e := by
      simpa [y, hcost, pathCost] using hh
    exact hedge
  refine ⟨y s, ?_, ?_⟩
  · constructor
    · exact ⟨Q s, (hQ s).1, rfl⟩
    · rintro a ⟨A, hA, rfl⟩
      exact (hQ s).2 A hA
  · constructor
    · exact ⟨y, hfeas, rfl⟩
    · rintro a ⟨z, hz, rfl⟩
      have hb := hupper z hz (hQ s).1
      rcases hz with ⟨_, hzroot⟩
      simpa [hzroot, y] using hb
