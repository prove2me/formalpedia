-- Prove2me | solution 1 for BhangaleHypergraph.Main.simple_conversion
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:57:25.066941+00:00
-- url     : https://prove2.me/submissions/9ec75ac6-1227-4f9c-9df7-bd6c1723b978

import Definitions.Def_BhangaleHypergraph_Main_Relational

open BhangaleHypergraph.Main

theorem solution {V : Type} [Fintype V] (I : RelInstance V) (C n : ℕ)
    (hC : 2 ≤ C) (numbering : Fin n ≃ V × Fin (2 * C + 1)) :
    (RelColorable I 2 → (Cluster I C n numbering).Colorable 2) ∧
    ((Cluster I C n numbering).Colorable C → RelColorable I C) := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun a => f (numbering a).1, ?_⟩
    have hp : ∀ E : Finset (Fin n), E ∈ (Cluster I C n numbering).edges →
        ¬ (Cluster I C n numbering).Monochromatic (fun a => f (numbering a).1) E := by
      intro E hE hmono
      rcases (Finset.mem_filter.mp hE).2 with
        ⟨hcard, a, b, c, rfl, hab, hac, hbc, htriple⟩
      apply hf _ _ _ htriple
      have ha : a ∈ ({a, b, c} : Finset (Fin n)) := Finset.mem_insert_self _ _
      have hb : b ∈ ({a, b, c} : Finset (Fin n)) :=
        Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
      have hc : c ∈ ({a, b, c} : Finset (Fin n)) :=
        Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton_self _))))
      exact ⟨hmono a ha b hb, hmono b hb c hc⟩
    exact hp
  · rintro ⟨χ, hχ⟩
    have hthree (v : V) : ∃ d : Fin C,
        3 ≤ (Finset.univ.filter fun i : Fin (2 * C + 1) =>
          χ (numbering.symm (v, i)) = d).card := by
      by_contra h
      push_neg at h
      have hle : ∀ d ∈ (Finset.univ : Finset (Fin C)),
          (Finset.univ.filter fun i : Fin (2 * C + 1) =>
            χ (numbering.symm (v, i)) = d).card ≤ 2 := by
        intro d hd
        have := h d
        omega
      have hsum := Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin (2 * C + 1))))
        (t := (Finset.univ : Finset (Fin C)))
        (f := fun i => χ (numbering.symm (v, i))) (by intro i hi; simp)
      have hbound :
          (∑ d : Fin C, (Finset.univ.filter fun i : Fin (2 * C + 1) =>
            χ (numbering.symm (v, i)) = d).card) ≤ ∑ _d : Fin C, 2 := by
        exact Finset.sum_le_sum hle
      simp only [Finset.card_univ, Fintype.card_fin] at hsum
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
      omega
    choose col hcol using hthree
    let S : V → Finset (Fin (2 * C + 1)) := fun v =>
      Finset.univ.filter fun i => χ (numbering.symm (v, i)) = col v
    have hS (v : V) : 3 ≤ (S v).card := hcol v
    choose T hTsub hTcard using fun v => Finset.exists_subset_card_eq (hS v)
    let repr (v : V) (j : Fin 3) : Fin (2 * C + 1) :=
      ((T v).equivFin.symm (Fin.cast (hTcard v).symm j) : Fin (2 * C + 1))
    have hrepr_mem (v : V) (j : Fin 3) : repr v j ∈ T v := by
      exact ((T v).equivFin.symm (Fin.cast (hTcard v).symm j)).property
    have hrepr_color (v : V) (j : Fin 3) : χ (numbering.symm (v, repr v j)) = col v := by
      have hm := hTsub v (hrepr_mem v j)
      exact (Finset.mem_filter.mp hm).2
    have hrepr_inj (v : V) : Function.Injective (repr v) := by
      intro i j hij
      have hh : Fin.cast (hTcard v).symm i = Fin.cast (hTcard v).symm j := by
        apply (T v).equivFin.symm.injective
        apply Subtype.ext
        exact hij
      simpa using hh
    have hdistinct {x y : V} {i j : Fin 3} (hij : i ≠ j)
        (h : numbering.symm (x, repr x i) = numbering.symm (y, repr y j)) : False := by
      have hp := congrArg numbering h
      simp only [Equiv.apply_symm_apply] at hp
      injection hp with hxy hrep
      subst y
      exact hij (hrepr_inj x hrep)
    refine ⟨col, ?_⟩
    intro u v w htriple hmono
    let a : Fin n := numbering.symm (u, repr u 0)
    let b : Fin n := numbering.symm (v, repr v 1)
    let c : Fin n := numbering.symm (w, repr w 2)
    have hab : a ≠ b := fun h => hdistinct (by decide : (0 : Fin 3) ≠ 1) h
    have hac : a ≠ c := fun h => hdistinct (by decide : (0 : Fin 3) ≠ 2) h
    have hbc : b ≠ c := fun h => hdistinct (by decide : (1 : Fin 3) ≠ 2) h
    have hEdge : ({a, b, c} : Finset (Fin n)) ∈ (Cluster I C n numbering).edges := by
      dsimp only [Cluster]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, by simp [hab, hac, hbc], a, b, c, rfl, hab, hac, hbc, ?_⟩
      simpa [a, b, c] using htriple
    have ha : χ a = col u := hrepr_color u 0
    have hb : χ b = col v := hrepr_color v 1
    have hc : χ c = col w := hrepr_color w 2
    have habc : χ a = χ b ∧ χ b = χ c := by
      rw [ha, hb, hc]
      exact hmono
    apply hχ {a, b, c} hEdge
    have hall : ∀ z ∈ ({a, b, c} : Finset (Fin n)), χ z = χ a := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · rfl
      · exact habc.1.symm
      · exact (habc.1.trans habc.2).symm
    intro x hx y hy
    exact (hall x hx).trans (hall y hy).symm
