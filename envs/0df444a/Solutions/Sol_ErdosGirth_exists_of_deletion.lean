-- Prove2me | solution 1 for ErdosGirth.exists_of_deletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:25.118174+00:00
-- url     : https://prove2.me/submissions/6f7b233b-8712-420f-9627-2e80240ce29d

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (n g t : ℕ) (G : SimpleGraph (Fin (2 * n))) (D : Finset (Fin (2 * n)))
    (hD : 2 * D.card < 2 * n) (hcyc : ∀ u (c : G.Walk u u), c.IsCycle → c.length ≤ g → u ∈ D)
    (hind : ∀ T : Finset (Fin (2 * n)), T.card = t → ¬ G.IsIndepSet (T : Set (Fin (2 * n)))) :
    ∃ H : SimpleGraph (Fin n), (g : ℕ∞) < H.egirth ∧
      ∀ s : Finset (Fin n), H.IsIndepSet (s : Set (Fin n)) → s.card < t := by
  have hR : n ≤ (univ \ D).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]; omega
  obtain ⟨R, hRsub, hRcard⟩ := exists_subset_card_eq hR
  set f : Fin n ↪ Fin (2 * n) := (R.orderEmbOfFin hRcard).toEmbedding with hf
  have hfR : ∀ i, f i ∉ D := fun i => by
    have := hRsub (R.orderEmbOfFin_mem hRcard i)
    exact (mem_sdiff.mp this).2
  refine ⟨G.comap f, ?_, fun s hs => ?_⟩
  · rw [← ENat.add_one_le_iff (ENat.natCast_ne_top g), le_egirth]
    intro a w hw
    by_contra hlt
    have hl : w.length ≤ g := by
      have : (w.length : ℕ∞) < g + 1 := lt_of_not_ge hlt
      have h' : w.length < g + 1 := by exact_mod_cast this
      omega
    have hinj : Function.Injective (Embedding.comap f G) := (Embedding.comap f G).injective
    have := hcyc _ (w.map (Embedding.comap f G).toHom) (hw.map hinj)
      (by rw [Walk.length_map]; exact hl)
    exact hfR a this
  · by_contra hst
    push Not at hst
    have hmap : G.IsIndepSet ((s.map f : Finset (Fin (2 * n))) : Set (Fin (2 * n))) := by
      intro x hx y hy hxy hadj
      simp only [coe_map, Set.mem_image, mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hs ha hb (fun h => hxy (by rw [h])) (by simpa using hadj)
    obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq (s := s.map f) (n := t)
      (by rw [card_map]; exact hst)
    exact hind T hTcard (hmap.mono (by exact_mod_cast hTsub))
end ErdosGirth
