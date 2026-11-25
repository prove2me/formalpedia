-- Prove2me | solution 1 for CliqueMinors.isMinor_lift_cone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:48.930411+00:00
-- url     : https://prove2.me/submissions/29d7fe4f-d188-4471-bdc2-0bee50df445c

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_induce_connected_mono
public import Theorems.Thm_CliqueMinors_singleton_connected
public import Theorems.Thm_CliqueMinors_MinorModel_exists_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution {G G' : SimpleGraph V} {x : V}
    (hG' : ∀ u v, G'.Adj u v → G.Adj u v ∧ G.Adj x u ∧ G.Adj x v)
    {r : ℕ} (hr : 2 ≤ r) (h : IsMinor (⊤ : SimpleGraph (Fin r)) G') :
    IsMinor (⊤ : SimpleGraph (Fin (r + 1))) G := by
  obtain ⟨M⟩ := h
  have hle : G' ≤ G := fun u v huv => (hG' u v huv).1
  have hmem : ∀ i, ∀ v ∈ M.branch i, G.Adj x v := fun i v hv => by
    obtain ⟨u, hu⟩ := M.exists_adj hr i hv; exact (hG' _ _ hu).2.1
  have hx : ∀ i, x ∉ M.branch i := fun i hxi => (hmem i x hxi).ne rfl
  let B : Fin (r + 1) → Finset V := Fin.lastCases {x} M.branch
  have hBl : B (Fin.last r) = {x} := Fin.lastCases_last
  have hBc : ∀ i, B i.castSucc = M.branch i := fun i => Fin.lastCases_castSucc i
  refine ⟨⟨B, fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩⟩
  · induction i using Fin.lastCases with
    | last => simp [hBl]
    | cast i => simpa [hBl, hBc] using M.branch_nonempty i
  · induction i using Fin.lastCases with
    | last => rw [hBl]; exact singleton_connected G x
    | cast i => rw [hBc]; exact induce_connected_mono hle (M.branch_connected i)
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => simpa [hBl, hBc] using hx j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [hBl, hBc] using hx i
      | cast j => simpa [hBl, hBc] using M.branch_disjoint i j (fun h => hij (by rw [h]))
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        obtain ⟨v, hv⟩ := M.branch_nonempty j
        exact ⟨x, by simp [hBl], v, by simpa [hBl, hBc] using hv, hmem j v hv⟩
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        obtain ⟨v, hv⟩ := M.branch_nonempty i
        exact ⟨v, by simpa [hBl, hBc] using hv, x, by simp [hBl], (hmem i v hv).symm⟩
      | cast j =>
        obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j (by simpa using hij)
        exact ⟨u, by simpa [hBl, hBc] using hu, v, by simpa [hBl, hBc] using hv, hle huv⟩
end CliqueMinors
