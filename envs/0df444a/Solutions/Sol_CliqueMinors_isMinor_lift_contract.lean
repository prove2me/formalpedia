-- Prove2me | solution 1 for CliqueMinors.isMinor_lift_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:38.760805+00:00
-- url     : https://prove2.me/submissions/ffd8174b-2cd7-4fb4-8b38-c7101a1838ce

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_reflTransGen_of_step
public import Theorems.Thm_CliqueMinors_induce_connected_of_root
public import Theorems.Thm_CliqueMinors_reflTransGen_of_connected
public import Theorems.Thm_CliqueMinors_MinorModel_exists_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution {G G' : SimpleGraph V} {x y : V} (hxy : G.Adj x y)
    (hG' : ∀ u v, G'.Adj u v →
      u ≠ y ∧ v ≠ y ∧ (G.Adj u v ∨ (u = x ∧ G.Adj y v) ∨ (v = x ∧ G.Adj y u)))
    {r : ℕ} (hr : 2 ≤ r) (h : IsMinor (⊤ : SimpleGraph (Fin r)) G') :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  classical
  obtain ⟨M⟩ := h
  have hy : ∀ i, y ∉ M.branch i := fun i hyi => by
    obtain ⟨u, hu⟩ := M.exists_adj hr i hyi
    exact (hG' _ _ hu).1 rfl
  let B : Fin r → Finset V := fun i =>
    if x ∈ M.branch i then insert y (M.branch i) else M.branch i
  have hsub : ∀ i, M.branch i ⊆ B i := fun i => by
    simp only [B]; split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl
  refine ⟨⟨B, fun i => (M.branch_nonempty i).mono (hsub i), fun i => ?_, fun i j hij => ?_,
    fun i j hij => ?_⟩⟩
  · by_cases hx : x ∈ M.branch i
    · have hB : B i = insert y (M.branch i) := by simp [B, hx]
      have hyB : y ∈ B i := by rw [hB]; exact Finset.mem_insert_self _ _
      apply induce_connected_of_root G _ x (hsub i hx)
      have step : ∀ v ∈ M.branch i, ReflTransGen (InAdj G (B i)) x v := by
        intro v hv
        refine reflTransGen_of_step (fun a b hab => ?_)
          (reflTransGen_of_connected (M.branch_connected i) hx hv)
        obtain ⟨ha, hb, hab⟩ := hab
        rcases (hG' a b hab).2.2 with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
        · exact ReflTransGen.single ⟨hsub i ha, hsub i hb, h⟩
        · exact (ReflTransGen.single ⟨hsub i ha, hyB, hxy⟩).tail ⟨hyB, hsub i hb, h⟩
        · exact (ReflTransGen.single ⟨hsub i ha, hyB, h.symm⟩).tail ⟨hyB, hsub i hb, hxy.symm⟩
      intro v hv
      rw [hB, Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact ReflTransGen.single ⟨hsub i hx, hyB, hxy⟩
      · exact step v hv
    · have hB : B i = M.branch i := by simp [B, hx]
      rw [hB]
      obtain ⟨v₀, hv₀⟩ := M.branch_nonempty i
      apply induce_connected_of_root G _ v₀ hv₀
      intro v hv
      refine reflTransGen_of_step (fun a b hab => ?_)
        (reflTransGen_of_connected (M.branch_connected i) hv₀ hv)
      obtain ⟨ha, hb, hab⟩ := hab
      rcases (hG' a b hab).2.2 with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · exact ReflTransGen.single ⟨ha, hb, h⟩
      · exact absurd ha hx
      · exact absurd hb hx
  · have hd := M.branch_disjoint i j hij
    simp only [B]
    split_ifs with hi hj hj
    · exact absurd (Finset.disjoint_left.1 hd hi) (by simpa using hj)
    · rw [Finset.disjoint_insert_left]; exact ⟨hy j, hd⟩
    · rw [Finset.disjoint_insert_right]; exact ⟨hy i, hd⟩
    · exact hd
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
    rcases (hG' u v huv).2.2 with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact ⟨u, hsub i hu, v, hsub j hv, h⟩
    · refine ⟨y, ?_, v, hsub j hv, h⟩
      simp [B, hu]
    · refine ⟨u, hsub i hu, y, ?_, h.symm⟩
      simp [B, hv]
end CliqueMinors
