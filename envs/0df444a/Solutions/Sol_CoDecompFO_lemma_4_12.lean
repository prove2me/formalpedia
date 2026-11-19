-- Prove2me | solution 1 for CoDecompFO.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:41:57.164453+00:00
-- url     : https://prove2.me/submissions/58b4099f-84fa-4b17-adcc-44fc5a69b780

import Definitions.Def_CoDecompFO_Lim
import Definitions.Def_CoDecompFO_AltSat

namespace CoDecompFO.L412Aux
open CoDecompFO FirstOrder

theorem atoms_hom {σ : Sig} {k : ℕ} {A B : Type} [σ.lang.Structure A] [σ.lang.Structure B]
    (f : A → B) (hf : IsHom σ f) (l : List A) :
    atomsOf σ k l ⊆ atomsOf σ k (l.map f) := by
  rintro ⟨i, pos⟩ ⟨args, hargs, hh⟩
  refine ⟨f ∘ args, fun j => ?_, hf i args hh⟩
  simp [List.getElem?_map, hargs j]

end CoDecompFO.L412Aux

open CoDecompFO CoDecompFO.L412Aux FirstOrder in
theorem solution {σ : Sig} (T : CoDecomp σ) {k : ℕ} (l : List T.Lim) (hl : l.length = k) :
    (∀ e, l.map (CoDecomp.Lim.edgeProj e) = (l.map fun x => x.val (T.ends e).1).map (T.gl e)) ∧
    (∀ e, l.map (CoDecomp.Lim.edgeProj e) = (l.map fun x => x.val (T.ends e).2).map (T.gr e)) ∧
    (∀ e, atomsOf σ k (l.map fun x => x.val (T.ends e).1) ⊆
      atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e))) ∧
    (∀ e, atomsOf σ k (l.map fun x => x.val (T.ends e).2) ⊆
      atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e))) ∧
    atomsOf σ k l = ⋂ t, atomsOf σ k (l.map fun x => x.val t) ∧
    atomsOf σ k l = (⋂ t, atomsOf σ k (l.map fun x => x.val t)) ∩
      ⋂ e, atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e)) := by
  have h1 : ∀ e, l.map (CoDecomp.Lim.edgeProj e) =
      (l.map fun x => x.val (T.ends e).1).map (T.gl e) := by
    intro e; rw [List.map_map]; rfl
  have h2 : ∀ e, l.map (CoDecomp.Lim.edgeProj e) =
      (l.map fun x => x.val (T.ends e).2).map (T.gr e) := by
    intro e; rw [List.map_map]; apply List.map_congr_left; intro x _
    exact x.compat e
  have h3 : ∀ e, atomsOf σ k (l.map fun x => x.val (T.ends e).1) ⊆
      atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e)) := by
    intro e; rw [h1 e]; exact atoms_hom _ (T.gl_hom e) _
  have h4 : ∀ e, atomsOf σ k (l.map fun x => x.val (T.ends e).2) ⊆
      atomsOf σ k (l.map (CoDecomp.Lim.edgeProj e)) := by
    intro e; rw [h2 e]; exact atoms_hom _ (T.gr_hom e) _
  have h5 : atomsOf σ k l = ⋂ t, atomsOf σ k (l.map fun x => x.val t) := by
    ext ⟨i, pos⟩
    simp only [Set.mem_iInter]
    constructor
    · rintro ⟨args, hargs, hh⟩ t
      refine ⟨fun j => (args j).val t, fun j => ?_, hh t⟩
      simp [List.getElem?_map, hargs j]
    · intro h
      have hpos : ∀ j, (pos j).val < l.length := fun j => by rw [hl]; exact (pos j).2
      refine ⟨fun j => l[(pos j).val]'(hpos j), fun j => by simp [hpos j], ?_⟩
      intro t
      obtain ⟨args, hargs, hh⟩ := h t
      have : (fun j => (l[(pos j).val]'(hpos j)).val t) = args := by
        funext j
        have := hargs j
        simp [List.getElem?_map, hpos j] at this
        exact this
      show σ.holds i (fun j => (l[(pos j).val]'(hpos j)).val t)
      rw [this]; exact hh
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rw [h5]
  apply Set.Subset.antisymm
  · intro A hA
    refine ⟨hA, ?_⟩
    simp only [Set.mem_iInter] at hA ⊢
    intro e; exact h3 e (hA _)
  · exact Set.inter_subset_left
