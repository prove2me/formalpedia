-- Prove2me | solution 1 for C6BipartiteDomination.lemma_8_5_independent_set_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:53:00.247796+00:00
-- url     : https://prove2.me/submissions/a9519519-cc80-4dea-9da3-a48c9368da03

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_ZPart_disjoint_BPart
import Theorems.Thm_C6BipartiteDomination_compensation_vertex_properties
import Theorems.Thm_C6BipartiteDomination_bipartite_add_independent_set_at_vertex
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_collective_exchange
import Theorems.Thm_C6BipartiteDomination_exists_maximal_independent_subset
import Theorems.Thm_C6BipartiteDomination_lemma_5_1_responsibility_eq
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_WBPart
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion
import Theorems.Thm_C6BipartiteDomination_mem_supportX
import Theorems.Thm_C6BipartiteDomination_selected_Z_isolated
import Theorems.Thm_C6BipartiteDomination_supportB_card
import Theorems.Thm_C6BipartiteDomination_supportX_card


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    ∃ J : Finset V,
      J ⊆ compensationRegion G D (supportX G D w) u w ∧
      Independent G J ∧ kCharge G D w ≤ J.card := by
  classical
  let X := supportX G D w
  let Q := compensationRegion G D X u w
  let T := X ∪ {u}
  have hXsub : X ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have huB : u ∈ BPart G D := hChosen.2.1
  have huD : u ∈ D := (mem_BPart G D u).mp huB |>.1
  have hwu : G.Adj w u := hChosen.2.2.1
  have hClass := lemma_7_2_negative_charge_classification G hCan hmax hw ha
  have hk : 3 ≤ kCharge G D w := by
    rcases hClass with ⟨hk, _⟩ | ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega
  have hbeta : 2 ≤ betaCharge G D w := by
    rcases hClass with ⟨_, hβ⟩ | ⟨_, hβ⟩ | ⟨_, hβ⟩ <;> omega
  have hDom : Dominates G D := hCan.1.1
  have hProps : ∀ q ∈ Q,
      q ∉ D ∧ G.Adj q u ∧ neighborhoodIn G D q ⊆ X ∪ {u} ∧
        (neighborhoodIn G D q).Nonempty := by
    intro q hq
    exact compensation_vertex_properties G hDom hXsub huB hq
  obtain ⟨J, hJQ, hJind, hJmax⟩ := exists_maximal_independent_subset G Q
  have hJQ' : J ⊆ compensationRegion G D (supportX G D w) u w := by
    simpa [Q, X] using hJQ
  refine ⟨J, hJQ', hJind, ?_⟩
  by_contra hsmall
  have hJsmall : J.card < kCharge G D w := by omega
  have hsupportCard : 2 ≤ (supportB G D w).card := by
    rw [supportB_card]
    exact hbeta
  have huSupport : u ∈ supportB G D w := by
    change u ∈ (BPart G D).filter (fun b => G.Adj w b)
    exact Finset.mem_filter.mpr ⟨huB, hwu⟩
  have hErasePos : 0 < ((supportB G D w).erase u).card := by
    rw [Finset.card_erase_of_mem huSupport]
    omega
  obtain ⟨v, hvErase⟩ := Finset.card_pos.mp hErasePos
  have hvNeU : v ≠ u := (Finset.mem_erase.mp hvErase).1
  have hvSupport : v ∈ supportB G D w := (Finset.mem_erase.mp hvErase).2
  have hvB : v ∈ BPart G D := (Finset.mem_filter.mp hvSupport).1
  have hvw : G.Adj w v := (Finset.mem_filter.mp hvSupport).2
  have hvNotX : v ∉ X := by
    intro hvX
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hvX) hvB).elim
  have hvRet : v ∈ D \ T := by
    refine Finset.mem_sdiff.mpr ⟨(mem_BPart G D v).mp hvB |>.1, ?_⟩
    intro hvT
    rcases Finset.mem_union.mp hvT with hvX | hvU
    · exact hvNotX hvX
    · exact hvNeU (Finset.mem_singleton.mp hvU)
  have hwNotR : w ∉ responsibilityRegion G D T := by
    intro hwR
    exact ((mem_responsibilityRegion G D T w).mp hwR).2 v hvRet hvw.symm
  have hwNotQ : w ∉ Q := by
    intro hwQ
    exact hwNotR (Finset.mem_sdiff.mp hwQ).1
  have hwNotD : w ∉ D := (mem_WBPart G D w).mp
    ((mem_SPart G D w).mp hw |>.1) |>.1
  let K := D \ T
  let S := (BPart G D).erase u ∪ {w}
  let Zret := ZPart G D ∩ K
  let U := Zret ∪ J
  have mem_Zret (z : V) : z ∈ Zret ↔ z ∈ ZPart G D ∧ z ∈ K := by
    simp [Zret]
  have hBase : IsBipartiteOn G S := hChosen.2.2.2
  have hwS : w ∈ S := by simp [S]
  have hwU : w ∉ U := by
    intro hwU
    rcases Finset.mem_union.mp hwU with hwZ | hwJ
    · have hwZ' : w ∈ ZPart G D ∧ w ∈ K := (mem_Zret w).mp hwZ
      exact hwNotD ((mem_ZPart G D w).mp hwZ'.1 |>.1)
    · exact hwNotQ (hJQ hwJ)
  have hZretD : Zret ⊆ D := by
    intro z hz
    exact (mem_ZPart G D z).mp (mem_Zret z |>.mp hz |>.1) |>.1
  have hZretK : Zret ⊆ K := Finset.inter_subset_right
  have hJoutside : ∀ q ∈ J, q ∉ D ∧ q ∈ responsibilityRegion G D T := by
    intro q hqJ
    have hqQ := hJQ hqJ
    have hqProps := hProps q hqQ
    exact ⟨hqProps.1, (Finset.mem_sdiff.mp hqQ).1⟩
  have hUind : Independent G U := by
    intro a b ha hb hab
    rcases Finset.mem_union.mp ha with haZ | haJ
    · rcases Finset.mem_union.mp hb with hbZ | hbJ
      · have haZpart := (mem_Zret a).mp haZ |>.1
        exact selected_Z_isolated G haZpart (hZretD hbZ) hab
      · have hbinfo := hJoutside b hbJ
        exact ((mem_responsibilityRegion G D T b).mp hbinfo.2).2 a
          (by simpa [K] using (mem_Zret a).mp haZ |>.2) hab
    · rcases Finset.mem_union.mp hb with hbZ | hbJ
      · have hainfo := hJoutside a haJ
        exact ((mem_responsibilityRegion G D T a).mp hainfo.2).2 b
          (by simpa [K] using (mem_Zret b).mp hbZ |>.2) hab.symm
      · exact hJind haJ hbJ hab
  have hBoundary : ∀ ⦃a b⦄, a ∈ U → b ∈ S → G.Adj a b → b = w := by
    intro a b ha hb hab
    rcases Finset.mem_union.mp ha with haZ | haJ
    · rcases Finset.mem_union.mp hb with hbB | hbW
      · have hbB' : b ∈ BPart G D := Finset.mem_erase.mp hbB |>.2
        exact (selected_Z_isolated G (mem_Zret a |>.mp haZ |>.1)
          (mem_BPart G D b |>.mp hbB' |>.1) hab).elim
      · exact Finset.mem_singleton.mp hbW
    · have haInfo := hJoutside a haJ
      rcases Finset.mem_union.mp hb with hbB | hbW
      · have hbRet : b ∈ K := by
          refine Finset.mem_sdiff.mpr ⟨(mem_BPart G D b |>.mp
            (Finset.mem_erase.mp hbB |>.2)).1, ?_⟩
          intro hbT
          rcases Finset.mem_union.mp hbT with hbX | hbU
          · exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hbX)
              (Finset.mem_erase.mp hbB |>.2)).elim
          · exact (Finset.mem_erase.mp hbB).1
              (Finset.mem_singleton.mp hbU)
        exact False.elim (((mem_responsibilityRegion G D T a).mp haInfo.2).2
          b hbRet hab.symm)
      · exact Finset.mem_singleton.mp hbW
  have hSdisjU : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro z hzS hzU
    rcases Finset.mem_union.mp hzS with hzB | hzw
    · have hzB' := (Finset.mem_erase.mp hzB).2
      rcases Finset.mem_union.mp hzU with hzZ | hzJ
      · exact (Finset.disjoint_left.mp (ZPart_disjoint_BPart G D)
          ((mem_Zret z).mp hzZ |>.1) hzB').elim
      · exact (hJoutside z hzJ).1 ((mem_BPart G D z).mp hzB' |>.1)
    · have hzEq : z = w := Finset.mem_singleton.mp hzw
      subst z
      rcases Finset.mem_union.mp hzU with hzZ | hzJ
      · exact hwNotD ((mem_ZPart G D w).mp ((mem_Zret w).mp hzZ |>.1) |>.1)
      · exact hwNotQ (hJQ hzJ)
  have hbipExpanded : IsBipartiteOn G (S ∪ U) :=
    bipartite_add_independent_set_at_vertex G hBase (by simp [S]) hUind hwU
      hSdisjU hBoundary
  have hDnewEq : (D \ T ∪ {w}) ∪ J = S ∪ U := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hzK | hzJ
      · rcases Finset.mem_union.mp hzK with hzK | hzw
        · by_cases hzZ : z ∈ ZPart G D
          · exact Finset.mem_union_right S (Finset.mem_union_left J
              (Finset.mem_inter.mpr ⟨hzZ, hzK⟩))
          · have hzB : z ∈ BPart G D := by
              rw [mem_BPart]
              exact ⟨(Finset.mem_sdiff.mp hzK).1, hzZ⟩
            have hzNe : z ≠ u := by
              intro hEq
              subst z
              exact (Finset.mem_sdiff.mp hzK).2
                (Finset.mem_union_right X (by simp))
            exact Finset.mem_union_left U (Finset.mem_union_left _
              (Finset.mem_erase.mpr ⟨hzNe, hzB⟩))
        · exact Finset.mem_union_left U (Finset.mem_union_right _ (by simpa using hzw))
      · exact Finset.mem_union_right S (Finset.mem_union_right Zret hzJ)
    · intro hz
      rcases Finset.mem_union.mp hz with hzS | hzU
      · rcases Finset.mem_union.mp hzS with hzB | hzw
        · have hzB' := Finset.mem_erase.mp hzB |>.2
          exact Finset.mem_union_left J (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨(mem_BPart G D z).mp hzB' |>.1, by
              intro hzT
              rcases Finset.mem_union.mp hzT with hzX | hzU
              · exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hzX) hzB').elim
              · exact (Finset.mem_erase.mp hzB).1 (Finset.mem_singleton.mp hzU)⟩))
        · exact Finset.mem_union_left J (Finset.mem_union_right _ hzw)
      · rcases Finset.mem_union.mp hzU with hzZ | hzJ
        · exact Finset.mem_union_left J (Finset.mem_union_left _
            (by simpa [K] using (mem_Zret z).mp hzZ |>.2))
        · exact Finset.mem_union_right _ hzJ
  have hDnewEq' : K ∪ ({w} ∪ J) = S ∪ U := by
    calc
      K ∪ ({w} ∪ J) = (K ∪ {w}) ∪ J := (Finset.union_assoc K {w} J).symm
      _ = S ∪ U := by simpa [K] using hDnewEq
  have hbipNew : IsBipartiteOn G (K ∪ ({w} ∪ J)) := by
    rw [hDnewEq']
    exact hbipExpanded
  have hRegionX : responsibilityRegion G D X = X :=
    lemma_5_1_responsibility_eq G hCan.1 hXsub
  have hCover : ∀ ⦃v⦄, Responsible G D T v →
      v ∈ ({w} ∪ J) ∨ ∃ z ∈ ({w} ∪ J), G.Adj z v := by
    intro z hz
    have hzR : z ∈ responsibilityRegion G D T :=
      (mem_responsibilityRegion G D T z).mpr hz
    by_cases hzX : z ∈ X
    · have hzw : G.Adj w z := (mem_supportX G D w z).mp hzX |>.2
      exact Or.inr ⟨w, Finset.mem_union_left _ (by simp), hzw⟩
    · have hzQ : z ∈ Q := Finset.mem_sdiff.mpr ⟨hzR, hzX⟩
      by_cases hzJ : z ∈ J
      · exact Or.inl (Finset.mem_union_right _ hzJ)
      · obtain ⟨j, hj, hjz⟩ := hJmax hzQ hzJ
        exact Or.inr ⟨j, Finset.mem_union_right _ hj, hjz⟩
  have hnew : IsBipartiteDominatingSet G (K ∪ ({w} ∪ J)) :=
    collective_exchange G hCover hbipNew
  have hXsubsetD : X ⊆ D := by
    intro z hz
    exact (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp (hXsub hz) |>.1) |>.1
  have hTsubD : T ⊆ D := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzU
    · exact hXsubsetD hzX
    · have hzEq : z = u := Finset.mem_singleton.mp hzU
      simpa [hzEq] using huD
  have hTDcard : T.card = kCharge G D w + 1 := by
    have hdisj : Disjoint X ({u} : Finset V) := by
      rw [Finset.disjoint_singleton_right]
      intro huX
      exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub huX) huB).elim
    rw [show T = X ∪ ({u} : Finset V) by rfl, Finset.card_union_of_disjoint hdisj]
    have hXcard' : X.card = kCharge G D w := by
      simpa [X] using supportX_card G D w
    simp [hXcard']
  have hKcard : K.card + T.card = D.card := Finset.card_sdiff_add_card_eq_card hTsubD
  have hwNotD : w ∉ D := (mem_WBPart G D w).mp
    ((mem_SPart G D w).mp hw |>.1) |>.1
  have hKdisjW : Disjoint K ({w} : Finset V) := by
    rw [Finset.disjoint_singleton_right]
    intro hwK
    exact hwNotD (Finset.mem_sdiff.mp hwK).1
  have hKdisjJ : Disjoint K J := by
    rw [Finset.disjoint_left]
    intro z hzK hzJ
    have hzQ := hJQ hzJ
    exact ((mem_responsibilityRegion G D T z).mp
      (Finset.mem_sdiff.mp hzQ).1).1 hzK
  have hWdisjJ : Disjoint ({w} : Finset V) J := by
    rw [Finset.disjoint_singleton_left]
    intro hwJ
    exact hwNotQ (hJQ hwJ)
  have hKWdisjJ : Disjoint (K ∪ {w}) J := by
    rw [Finset.disjoint_left]
    intro z hz hzJ
    rcases Finset.mem_union.mp hz with hzK | hzw
    · exact (Finset.disjoint_left.mp hKdisjJ hzK hzJ).elim
    · exact (Finset.disjoint_left.mp hWdisjJ hzw hzJ).elim
  have hNewcard : ((K ∪ {w}) ∪ J).card + T.card = D.card + 1 + J.card := by
    rw [Finset.card_union_of_disjoint hKWdisjJ,
      Finset.card_union_of_disjoint hKdisjW]
    simp only [Finset.card_singleton]
    omega
  have hNewcard' : (K ∪ ({w} ∪ J)).card + T.card = D.card + 1 + J.card := by
    simpa [Finset.union_assoc] using hNewcard
  have hmin := hCan.2.1 (K ∪ ({w} ∪ J)) hnew
  have hsmaller : (K ∪ ({w} ∪ J)).card < D.card := by
    rw [← hKcard, hTDcard] at hNewcard'
    omega
  exact (Nat.not_lt_of_ge hmin) hsmaller
end C6BipartiteDomination
