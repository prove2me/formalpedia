-- Prove2me | solution 1 for C6BipartiteDomination.lemma_2_4_component_additivity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:40:49.010334+00:00
-- url     : https://prove2.me/submissions/231db1c4-883a-42e1-b505-2896690692e3

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
section
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
private theorem lemma_2_4_left_minimum
    {A B D : Finset V}
    (hparts : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B)
    (hcross : ∀ ⦃a b⦄, a ∈ A → b ∈ B → ¬ G.Adj a b)
    (hD : MinimumBipartiteDominatingSet G D) :
    MinimumBipartiteDominatingOn G A (D ∩ A) ∧
      D.card = (D ∩ A).card + (D ∩ B).card := by
  classical
  have hDsub : D ⊆ A ∪ B := by rw [hparts]; exact Finset.subset_univ _
  have hDA : D ∩ A ⊆ D := Finset.inter_subset_left
  have hDB : D ∩ B ⊆ D := Finset.inter_subset_left
  have hDAA : D ∩ A ⊆ A := Finset.inter_subset_right
  have hDBB : D ∩ B ⊆ B := Finset.inter_subset_right
  have hDBip : IsBipartiteOn G (D ∩ A) := by
    rcases hD.1.2 with ⟨c, hc⟩
    exact ⟨c, fun hu hv huD hvD hadj => hc (hDA huD) (hDA hvD) hadj⟩
  have hDomA : ∀ ⦃v⦄, v ∈ A → v ∉ D ∩ A →
      ∃ y ∈ D ∩ A, G.Adj y v := by
    intro v hvA hvNot
    have hvD : v ∉ D := by
      intro hvD
      exact hvNot (Finset.mem_inter.mpr ⟨hvD, hvA⟩)
    obtain ⟨d, hdD, hdv⟩ := hD.1.1 hvD
    have hdParts : d ∈ A ∪ B := hDsub hdD
    rcases Finset.mem_union.mp hdParts with hdA | hdB
    · exact ⟨d, Finset.mem_inter.mpr ⟨hdD, hdA⟩, hdv⟩
    · have hcross' := hcross hvA hdB
      exact (hcross' hdv.symm).elim
  have hLocA : BipartiteDominatingOn G A (D ∩ A) :=
    ⟨hDAA, hDomA, hDBip⟩
  have hLocMinA : ∀ E, BipartiteDominatingOn G A E → (D ∩ A).card ≤ E.card := by
    intro E hE
    let D' := E ∪ (D ∩ B)
    have hEdisj : Disjoint E (D ∩ B) := by
      rw [Finset.disjoint_left]
      intro v hvE hvDB
      have hvA := hE.1 hvE
      have hvB := hDBB hvDB
      exact (Finset.disjoint_left.mp hdisj hvA hvB).elim
    have hDom' : Dominates G D' := by
      intro v hvD'
      by_cases hvA : v ∈ A
      · have hvE : v ∉ E := by
          intro hvE
          exact hvD' (Finset.mem_union_left _ hvE)
        obtain ⟨e, heE, hev⟩ := hE.2.1 hvA hvE
        exact ⟨e, Finset.mem_union_left _ heE, hev⟩
      · have hvB : v ∈ B := by
          have hvParts : v ∈ A ∪ B := by rw [hparts]; exact Finset.mem_univ _
          rcases Finset.mem_union.mp hvParts with h | h
          · exact (hvA h).elim
          · exact h
        have hvD : v ∉ D := by
          intro hvD
          have hvDB : v ∈ D ∩ B := Finset.mem_inter.mpr ⟨hvD, hvB⟩
          exact hvD' (Finset.mem_union_right E hvDB)
        obtain ⟨d, hdD, hdv⟩ := hD.1.1 hvD
        have hdParts : d ∈ A ∪ B := hDsub hdD
        rcases Finset.mem_union.mp hdParts with hdA | hdB
        · have hcross' := hcross hdA hvB
          exact (hcross' hdv).elim
        · exact ⟨d, Finset.mem_union_right E
            (Finset.mem_inter.mpr ⟨hdD, hdB⟩), hdv⟩
    have hBip' : IsBipartiteOn G D' := by
      rcases hE.2.2 with ⟨eColor, heColor⟩
      rcases hD.1.2 with ⟨dColor, hdColor⟩
      refine ⟨fun v => if v ∈ E then eColor v else dColor v, ?_⟩
      intro u v hu hv hadj
      rcases Finset.mem_union.mp hu with huE | huDB
      · rcases Finset.mem_union.mp hv with hvE | hvDB
        · simpa [huE, hvE] using heColor huE hvE hadj
        · have hcross' := hcross (hE.1 huE) (hDBB hvDB)
          exact (hcross' hadj).elim
      · rcases Finset.mem_union.mp hv with hvE | hvDB
        · have hcross' := hcross (hE.1 hvE) (hDBB huDB)
          exact (hcross' hadj.symm).elim
        · have huNotE : u ∉ E := by
            intro huE
            exact (Finset.disjoint_left.mp hEdisj huE huDB).elim
          have hvNotE : v ∉ E := by
            intro hvE
            exact (Finset.disjoint_left.mp hEdisj hvE hvDB).elim
          simpa [huNotE, hvNotE] using hdColor (hDB huDB) (hDB hvDB) hadj
    have hDdom' : IsBipartiteDominatingSet G D' := ⟨hDom', hBip'⟩
    have hmin := hD.2 D' hDdom'
    have hDpart : D.card = (D ∩ A).card + (D ∩ B).card := by
      have hDdisj : Disjoint (D ∩ A) (D ∩ B) := by
        rw [Finset.disjoint_left]
        intro v hvA hvB
        exact (Finset.disjoint_left.mp hdisj (hDAA hvA) (hDBB hvB)).elim
      have hDeq : (D ∩ A) ∪ (D ∩ B) = D := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_union.mp hv with h | h
          · exact (Finset.mem_inter.mp h).1
          · exact (Finset.mem_inter.mp h).1
        · intro hvD
          have hvParts : v ∈ A ∪ B := hDsub hvD
          rcases Finset.mem_union.mp hvParts with hvA | hvB
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvD, hvA⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvD, hvB⟩)
      calc
        D.card = ((D ∩ A) ∪ (D ∩ B)).card := congrArg Finset.card hDeq.symm
        _ = (D ∩ A).card + (D ∩ B).card :=
          Finset.card_union_of_disjoint hDdisj
    have hD'card : D'.card = E.card + (D ∩ B).card := by
      dsimp [D']
      rw [Finset.card_union_of_disjoint hEdisj]
    rw [hDpart, hD'card] at hmin
    omega
  have hDcard : D.card = (D ∩ A).card + (D ∩ B).card := by
    have hDdisj : Disjoint (D ∩ A) (D ∩ B) := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      exact (Finset.disjoint_left.mp hdisj (hDAA hvA) (hDBB hvB)).elim
    have hDeq : (D ∩ A) ∪ (D ∩ B) = D := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_union.mp hv with h | h
        · exact (Finset.mem_inter.mp h).1
        · exact (Finset.mem_inter.mp h).1
      · intro hvD
        have hvParts : v ∈ A ∪ B := hDsub hvD
        rcases Finset.mem_union.mp hvParts with hvA | hvB
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvD, hvA⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvD, hvB⟩)
    calc
      D.card = ((D ∩ A) ∪ (D ∩ B)).card := congrArg Finset.card hDeq.symm
      _ = (D ∩ A).card + (D ∩ B).card := Finset.card_union_of_disjoint hDdisj
  exact ⟨⟨hLocA, hLocMinA⟩, hDcard⟩
end C6BipartiteDomination
end

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {A B D : Finset V}
    (hparts : A ∪ B = Finset.univ)
    (hdisj : Disjoint A B)
    (hcross : ∀ ⦃a b⦄, a ∈ A → b ∈ B → ¬ G.Adj a b)
    (hD : MinimumBipartiteDominatingSet G D) :
    MinimumBipartiteDominatingOn G A (D ∩ A) ∧
      MinimumBipartiteDominatingOn G B (D ∩ B) ∧
      D.card = (D ∩ A).card + (D ∩ B).card := by
  classical
  have hswapCross : ∀ ⦃b a⦄, b ∈ B → a ∈ A → ¬ G.Adj b a := by
    intro b a hb ha hAdj
    exact hcross ha hb hAdj.symm
  have hswapParts : B ∪ A = Finset.univ := by
    rw [Finset.union_comm, hparts]
  have hswapDisj : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    exact (Finset.disjoint_left.mp hdisj hxA hxB).elim
  have hleft := lemma_2_4_left_minimum G hparts hdisj hcross hD
  have hright := lemma_2_4_left_minimum G hswapParts hswapDisj hswapCross hD
  exact ⟨hleft.1, hright.1, hleft.2⟩
end C6BipartiteDomination
