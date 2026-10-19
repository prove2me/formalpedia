-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_maximal_separated_palette_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/b8d6efbd-fc78-4ab8-bef8-785402b20488

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteSeparated_insert

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {α : Type*} [DecidableEq α]
    (ambient : Finset (Finset α)) (s : ℕ) (hs : 0 < s)
    (hequal : ∀ P ∈ ambient, ∀ Q ∈ ambient, P.card = Q.card) :
    ∃ family : Finset (Finset α),
      family ⊆ ambient ∧ IsPaletteSeparated s family ∧
        ∀ P ∈ ambient, ∃ Q ∈ family, (P \ Q).card < s := by
  classical
  let candidates := ambient.powerset.filter (IsPaletteSeparated s)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, IsPaletteSeparated]
  obtain ⟨family, hfamily, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hfamily' : family ⊆ ambient ∧ IsPaletteSeparated s family := by
    simpa [candidates] using hfamily
  refine ⟨family, hfamily'.1, hfamily'.2, ?_⟩
  intro P hP
  by_contra hnot
  have hfar : ∀ Q ∈ family, s ≤ (P \ Q).card := by
    intro Q hQ
    exact Nat.le_of_not_gt (fun hclose => hnot ⟨Q, hQ, hclose⟩)
  have hPnot : P ∉ family := by
    intro hPF
    apply hnot
    refine ⟨P, hPF, ?_⟩
    simpa using hs
  have hcards : ∀ Q ∈ family, Q.card = P.card := by
    intro Q hQ
    exact hequal Q (hfamily'.1 hQ) P hP
  have hinsert_separated : IsPaletteSeparated s (insert P family) :=
    paletteSeparated_insert hfamily'.2 hcards hfar
  have hinsert : insert P family ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hP hfamily'.1, hinsert_separated⟩
  have hmaxcard := hmax (insert P family) hinsert
  rw [Finset.card_insert_of_notMem hPnot] at hmaxcard
  omega
end ErdosProblems.MulticolourTriangleRamsey
