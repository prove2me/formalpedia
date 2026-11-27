-- Prove2me | solution 1 for BicliqueSDP.Chain.Supplement.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:20.174215+00:00
-- url     : https://prove2.me/submissions/df076d97-4038-4641-9df6-eea54429e33c

import Definitions.Def_BicliqueSDP_Chain_Supplement_Gadget
set_option autoImplicit false

open BicliqueSDP
open BicliqueSDP.Chain
open BicliqueSDP.Chain.Supplement

/-- Lemma 2.6, corrected: the chosen left edge set F may contain additional edges
not incident to A. No graph or independent set is excluded. The other clauses are unchanged. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    alpha (HGEdge G) = (Fintype.card V : ℝ) +
      (Nat.card G.edgeSet : ℝ) * (Fintype.card V + 1) ∧
    (∀ L R : Finset (HGSide G), IsMaximalPair (HGEdge G) L R →
      (∃ (A : Finset V) (F : Finset (Edge G)),
        incidentEdges G A ⊆ F ∧ L = formLeft G A F ∧ R = formRight G A F) ∧
      IsMaximumPair (HGEdge G) L R) ∧
    (∀ (A : Finset V) (F : Finset (Edge G)), incidentEdges G A ⊆ F →
      IsMaximumPair (HGEdge G) (formLeft G A F) (formRight G A F)) := by
        classical
        have hrefl : ∀ x : HGSide G, HGEdge G x x := by
          intro x; rcases x with v | ⟨e, i⟩
          · show v = v; rfl
          · show e = e; rfl
        have hshift : ∀ (a : HGSide G) (e : Edge G) (i j : Fin (Fintype.card V + 1)),
            HGEdge G a (Sum.inr (e, i)) → HGEdge G a (Sum.inr (e, j)) := by
          intro a e i j h
          rcases a with w | ⟨f, k⟩
          · exact h
          · exact h
        have hdisj : ∀ L R : Finset (HGSide G), IsBiindep (HGEdge G) L R → Disjoint L R := by
          intro L R h
          rw [Finset.disjoint_left]
          intro x hxL hxR
          exact h x hxL x hxR (hrefl x)
        have hcard_le : ∀ L R : Finset (HGSide G), IsBiindep (HGEdge G) L R →
            L.card + R.card ≤ Fintype.card (HGSide G) := by
          intro L R h
          rw [← Finset.card_union_of_disjoint (hdisj L R h)]
          exact Finset.card_le_univ _
        have hcard_eq : ∀ L R : Finset (HGSide G), IsBiindep (HGEdge G) L R →
            (∀ x, x ∈ L ∨ x ∈ R) → L.card + R.card = Fintype.card (HGSide G) := by
          intro L R h hcov
          rw [← Finset.card_union_of_disjoint (hdisj L R h)]
          have hU : L ∪ R = Finset.univ := by
            ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hcov x
          rw [hU]; exact Finset.card_univ
        have halpha : alpha (HGEdge G) = (Fintype.card (HGSide G) : ℝ) := by
          unfold alpha
          apply le_antisymm
          · apply Finset.sup'_le
            intro p hp
            have hb : IsBiindep (HGEdge G) p.1 p.2 := (Finset.mem_filter.mp hp).2
            exact_mod_cast hcard_le p.1 p.2 hb
          · have hb : IsBiindep (HGEdge G) (∅ : Finset (HGSide G)) Finset.univ := by
              intro i hi; simp at hi
            have hmem : ((∅ : Finset (HGSide G)), (Finset.univ : Finset (HGSide G))) ∈
                pairs (HGEdge G) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
            refine le_trans ?_ (Finset.le_sup' _ hmem)
            simp
        have hcardS : (Fintype.card (HGSide G) : ℝ) = (Fintype.card V : ℝ) +
            (Nat.card G.edgeSet : ℝ) * (Fintype.card V + 1) := by
          simp [HGSide, Edge, Fintype.card_sum, Fintype.card_prod, Nat.card_eq_fintype_card]
        have hmaxOfCover : ∀ L R : Finset (HGSide G), IsBiindep (HGEdge G) L R →
            (∀ x, x ∈ L ∨ x ∈ R) → IsMaximumPair (HGEdge G) L R := by
          intro L R h hcov
          refine ⟨h, ?_⟩
          rw [halpha]; exact_mod_cast hcard_eq L R h hcov
        have hL1 : ∀ (A : Finset V) (F : Finset (Edge G)) (v : V),
            (Sum.inl v : HGSide G) ∈ formLeft G A F ↔ v ∈ A := by
          intro A F v; simp [formLeft]
        have hL2 : ∀ (A : Finset V) (F : Finset (Edge G)) (p : Edge G × Fin (Fintype.card V + 1)),
            (Sum.inr p : HGSide G) ∈ formLeft G A F ↔ p.1 ∈ F := by
          intro A F p; simp [formLeft]
        have hR1 : ∀ (A : Finset V) (F : Finset (Edge G)) (v : V),
            (Sum.inl v : HGSide G) ∈ formRight G A F ↔ v ∉ A := by
          intro A F v; simp [formRight]
        have hR2 : ∀ (A : Finset V) (F : Finset (Edge G)) (p : Edge G × Fin (Fintype.card V + 1)),
            (Sum.inr p : HGSide G) ∈ formRight G A F ↔ p.1 ∉ F := by
          intro A F p; simp [formRight]
        have hform : ∀ (A : Finset V) (F : Finset (Edge G)), incidentEdges G A ⊆ F →
            IsMaximumPair (HGEdge G) (formLeft G A F) (formRight G A F) := by
          intro A F hAF
          apply hmaxOfCover
          · intro x hx y hy hxy
            rcases x with v | ⟨e, i⟩ <;> rcases y with w | ⟨f, j⟩
            · rw [hL1] at hx; rw [hR1] at hy
              have hvw : v = w := hxy
              subst hvw; exact hy hx
            · rw [hL1] at hx; rw [hR2] at hy
              have hvf : v ∈ f.val := hxy
              apply hy; apply hAF
              simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨v, hx, hvf⟩
            · exact hxy
            · rw [hL2] at hx; rw [hR2] at hy
              have hef : e = f := hxy
              subst hef; exact hy hx
          · intro x; rcases x with v | p
            · by_cases hv : v ∈ A
              · left; exact (hL1 A F v).2 hv
              · right; exact (hR1 A F v).2 hv
            · by_cases hp : p.1 ∈ F
              · left; exact (hL2 A F p).2 hp
              · right; exact (hR2 A F p).2 hp
        have hstep : ∀ L R : Finset (HGSide G), IsBiindep (HGEdge G) L R → ∀ x, x ∉ L →
            IsBiindep (HGEdge G) (insert x L) R ∨ IsBiindep (HGEdge G) L (insert x R) := by
          intro L R h x hxL
          rcases x with v | ⟨e, i⟩
          · right
            intro a ha b hb hab
            rw [Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · rcases a with w | ⟨f, j⟩
              · have hwv : w = v := hab
                subst hwv; exact hxL ha
              · exact hab
            · exact h a ha b hb hab
          · by_cases hA : IsBiindep (HGEdge G) (insert (Sum.inr (e, i)) L) R
            · left; exact hA
            · right
              intro a ha b hb hab
              rw [Finset.mem_insert] at hb
              rcases hb with rfl | hb
              · apply hA
                intro a' ha' b' hb' hab'
                rw [Finset.mem_insert] at ha'
                rcases ha' with rfl | ha'
                · rcases b' with w | ⟨f, j⟩
                  · exact hab'
                  · have hef : e = f := hab'
                    subst hef
                    exact h a ha _ hb' (hshift a e i j hab)
                · exact h a' ha' b' hb' hab'
              · exact h a ha b hb hab
        have hcover : ∀ L R : Finset (HGSide G), IsMaximalPair (HGEdge G) L R →
            ∀ x, x ∈ L ∨ x ∈ R := by
          intro L R hLR x
          obtain ⟨h, hmax⟩ := hLR
          by_contra hx
          push Not at hx
          rcases hstep L R h x hx.1 with h1 | h1
          · have := (hmax _ _ h1 (Finset.subset_insert _ _) subset_rfl).1
            exact hx.1 (this ▸ Finset.mem_insert_self x L)
          · have := (hmax _ _ h1 subset_rfl (Finset.subset_insert _ _)).2
            exact hx.2 (this ▸ Finset.mem_insert_self x R)
        refine ⟨halpha.trans hcardS, ?_, hform⟩
        intro L R hLR
        have hcov := hcover L R hLR
        have h := hLR.1
        refine ⟨?_, hmaxOfCover L R h hcov⟩
        have hRiff : ∀ x, x ∈ R ↔ x ∉ L := by
          intro x
          constructor
          · intro hR hL; exact h x hL x hR (hrefl x)
          · intro hL; exact (hcov x).resolve_left hL
        have hgad : ∀ (e : Edge G) (i j : Fin (Fintype.card V + 1)),
            (Sum.inr (e, i) : HGSide G) ∈ L → (Sum.inr (e, j) : HGSide G) ∈ L := by
          intro e i j hi
          by_contra hj
          have hjR := (hRiff _).2 hj
          exact h _ hi _ hjR (show e = e from rfl)
        refine ⟨Finset.univ.filter (fun v => (Sum.inl v : HGSide G) ∈ L),
          Finset.univ.filter (fun e => (Sum.inr (e, 0) : HGSide G) ∈ L), ?_, ?_, ?_⟩
        · intro e he
          simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
          obtain ⟨v, hv, hve⟩ := he
          by_contra hn
          exact h _ hv _ ((hRiff _).2 hn) hve
        · ext x
          rcases x with v | ⟨e, i⟩
          · rw [hL1]; simp
          · rw [hL2]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hgad e i 0, hgad e 0 i⟩
        · ext x
          rw [hRiff]
          rcases x with v | ⟨e, i⟩
          · rw [hR1]; simp
          · rw [hR2]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun h1 h2 => h1 (hgad e 0 i h2), fun h1 h2 => h1 (hgad e i 0 h2)⟩
