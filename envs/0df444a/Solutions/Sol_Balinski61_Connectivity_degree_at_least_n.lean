-- Prove2me | solution 1 for Balinski61.Connectivity.degree_at_least_n
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T07:46:26.030995+00:00
-- url     : https://prove2.me/submissions/ff829665-6565-4afc-ba9b-cdf56a033fba

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Set.Card
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Theorems.Thm_Balinski61_Connectivity_graph_n_tuply_connected

open scoped RealInnerProductSpace
open Balinski61.Connectivity

theorem solution (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b)
    (v : Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    (n : ℕ∞) ≤ ((polyGraph (Hirsch.Hpoly a b)).neighborSet v).encard := by
  set G := polyGraph (Hirsch.Hpoly a b)
  obtain ⟨hcard, hconn⟩ := graph_n_tuply_connected n m a b hS
  by_contra hlt
  rw [not_le] at hlt
  set X : Set (Set.extremePoints ℝ (Hirsch.Hpoly a b)) := G.neighborSet v
  have hvX : v ∈ Xᶜ := by
    simp [X, SimpleGraph.mem_neighborSet]
  have hX_add : X.encard + 1 ≤ (n : ℕ∞) := Order.add_one_le_of_lt hlt
  have hins_lt : (insert v X).encard < (Set.univ : Set (Set.extremePoints ℝ (Hirsch.Hpoly a b))).encard := by
    calc (insert v X).encard ≤ X.encard + 1 := Set.encard_insert_le X v
      _ ≤ (n : ℕ∞) := hX_add
      _ < (n : ℕ∞) + 1 := by exact_mod_cast Nat.lt_succ_self n
      _ ≤ (Set.univ : Set (Set.extremePoints ℝ (Hirsch.Hpoly a b))).encard := hcard
  have hne_univ : insert v X ≠ Set.univ := fun heq => (ne_of_lt hins_lt) (congrArg Set.encard heq)
  have hex : ∃ w, w ∉ insert v X := by
    by_contra! hall
    exact hne_univ (Set.eq_univ_of_forall hall)
  rcases hex with ⟨w, hw⟩
  rw [Set.mem_insert_iff, not_or] at hw
  rcases hw with ⟨hwv, hwX⟩
  have hGconn := hconn X hlt
  obtain ⟨p⟩ := hGconn.preconnected ⟨v, hvX⟩ ⟨w, hwX⟩
  cases p with
  | nil =>
    exact hwv rfl
  | @cons _ u _ hadj _ =>
    exact u.2 hadj
