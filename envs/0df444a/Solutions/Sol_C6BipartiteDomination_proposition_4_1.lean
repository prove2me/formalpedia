-- Prove2me | solution 1 for C6BipartiteDomination.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:44:42.69427+00:00
-- url     : https://prove2.me/submissions/8ab00c50-cdca-4b6f-87ab-91a8bd4539a1

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_mem_neighborsIn
import Theorems.Thm_C6BipartiteDomination_neighborsIn_self_subset
import Theorems.Thm_C6BipartiteDomination_neighborsIn_eq_of_dominates
import Theorems.Thm_C6BipartiteDomination_exists_minimal_deficient_subset
import Theorems.Thm_C6BipartiteDomination_minimal_deficient_card_ge_two
import Theorems.Thm_C6BipartiteDomination_minimal_deficient_neighbor_card
import Theorems.Thm_C6BipartiteDomination_exists_maximal_independent_subset
import Theorems.Thm_C6BipartiteDomination_minimal_deficient_subset_bound

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V}
    (hD : IsBipartiteDominatingSet G D)
    (hmin : ∀ E, IsBipartiteDominatingSet G E → D.card ≤ E.card)
    (hDind : Independent G D)
    (hNoIso : HasNoIsolatedVertices G) :
    D.card ≤ (Finset.univ \ D).card := by
  classical
  by_contra hnot
  have hlarge : (Finset.univ \ D).card < D.card := by omega
  let W := Finset.univ \ D
  have hcover : neighborsIn G D W = W := by
    apply neighborsIn_eq_of_dominates G
    intro w hw
    have hwD : w ∉ D := (Finset.mem_sdiff.mp (show w ∈ Finset.univ \ D from hw)).2
    exact hD.1 hwD
  obtain ⟨X, hXsub, hXdef, hXmin⟩ :=
    exists_minimal_deficient_subset G D W hcover (by simpa [W] using hlarge)
  have hXD : X ⊆ D := Finset.mem_powerset.mp hXsub
  have hXcard : 2 ≤ X.card := by
    apply minimal_deficient_card_ge_two G hXD hDind hNoIso
    simpa [W] using hXdef
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hAcard : (neighborsIn G X W).card + 1 = X.card :=
    minimal_deficient_neighbor_card G hXne hXdef hXmin
  let A := neighborsIn G X W
  obtain ⟨I, hIA, hIind, hImax⟩ := exists_maximal_independent_subset G A
  have hAne : A.Nonempty := Finset.card_pos.mp (by dsimp [A]; omega)
  have hIne : I.Nonempty := by
    by_contra h
    push Not at h
    have hIeq : I = ∅ := h
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨i, hi, _⟩ := hImax ha (by simp [hIeq])
    simp [hIeq] at hi
  have hNbound : (neighborsIn G I X).card ≥ I.card + 1 := by
    apply minimal_deficient_subset_bound G hAcard hXmin
    · intro i hi
      simpa [A] using hIA hi
    · exact hIne
  let NXI := neighborsIn G I X
  let D' := (D \ NXI) ∪ I
  have hI_W : I ⊆ W := by
    intro i hi
    have hiA : i ∈ A := hIA hi
    have hiA' : i ∈ neighborsIn G X W := by simpa [A] using hiA
    exact (mem_neighborsIn G X W i).mp hiA' |>.1
  have hI_Ddisj : Disjoint (D \ NXI) I := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvD' hvI
    have hvD : v ∈ D := (Finset.mem_sdiff.mp hvD').1
    have hvW : v ∈ W := hI_W hvI
    exact (Finset.mem_sdiff.mp hvW).2 hvD
  have hD'dom : Dominates G D' := by
    intro v hvD'
    by_cases hvD : v ∈ D
    · have hvN : v ∈ NXI := by
        by_contra hn
        apply hvD'
        exact Finset.mem_union_left I (Finset.mem_sdiff.mpr ⟨hvD, hn⟩)
      obtain ⟨i, hi, hadj⟩ := (mem_neighborsIn G I X v).mp (by simpa [NXI] using hvN) |>.2
      exact ⟨i, Finset.mem_union_right (D \ NXI) hi, hadj⟩
    · obtain ⟨d, hd, hAdj⟩ := hD.1 hvD
      by_cases hvA : v ∈ A
      · have hvI : v ∉ I := by
          intro hvI
          exact hvD' (Finset.mem_union_right (D \ NXI) hvI)
        obtain ⟨i, hi, hiv⟩ := hImax hvA hvI
        exact ⟨i, Finset.mem_union_right (D \ NXI) hi, hiv⟩
      · have hdX : d ∉ NXI := by
          intro hdN
          have hdX' : d ∈ X := neighborsIn_self_subset G I X (by simpa [NXI] using hdN)
          have hvW : v ∈ W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvD⟩
          have hvA' : v ∈ neighborsIn G X W := (mem_neighborsIn G X W v).mpr ⟨hvW, d, hdX', hAdj⟩
          exact hvA (by simpa [A] using hvA')
        exact ⟨d, Finset.mem_union_left I (Finset.mem_sdiff.mpr ⟨hd, hdX⟩), hAdj⟩
  have hD'bip : IsBipartiteOn G D' := by
    refine ⟨fun v => v ∈ I, ?_⟩
    intro u v hu hv hAdj
    rcases Finset.mem_union.mp hu with huD | huI
    · rcases Finset.mem_union.mp hv with hvD | hvI
      · exact (hDind (Finset.mem_sdiff.mp huD).1 (Finset.mem_sdiff.mp hvD).1 hAdj).elim
      ·
        have huW : u ∉ I := by
          intro huI
          have huD' := (Finset.mem_sdiff.mp huD).1
          exact (Finset.mem_sdiff.mp (hI_W huI)).2 huD'
        simp [huW, hvI]
    · rcases Finset.mem_union.mp hv with hvD | hvI
      · have hvW : v ∉ I := by
          intro hvI
          exact (Finset.mem_sdiff.mp (hI_W hvI)).2 (Finset.mem_sdiff.mp hvD).1
        simp [huI, hvW]
      · exact (hIind huI hvI hAdj).elim
  have hD' : IsBipartiteDominatingSet G D' := ⟨hD'dom, hD'bip⟩
  have hmin' := hmin D' hD'
  have hcardD' : D'.card = D.card - NXI.card + I.card := by
    dsimp [D']
    rw [Finset.card_union_of_disjoint hI_Ddisj,
      Finset.card_sdiff_of_subset (show NXI ⊆ D from fun x hx =>
        hXD (neighborsIn_self_subset G I X (by simpa [NXI] using hx)))]
  rw [hcardD'] at hmin'
  have hNXIle : NXI.card ≤ D.card := Finset.card_le_card (show NXI ⊆ D from fun x hx =>
    hXD (neighborsIn_self_subset G I X (by simpa [NXI] using hx)))
  have hsubadd : D.card - NXI.card + NXI.card = D.card := Nat.sub_add_cancel hNXIle
  have hNbound' : I.card + 1 ≤ NXI.card := by simpa [NXI] using hNbound
  have hstrict : D.card - NXI.card + I.card < D.card := by omega
  omega
end C6BipartiteDomination
