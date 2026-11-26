-- Prove2me | solution 1 for C6BipartiteDomination.lemma_5_2_inductive_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:07.076477+00:00
-- url     : https://prove2.me/submissions/aa829e51-8176-4f37-bcf9-fa1853467f31

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_Z1Part
import Theorems.Thm_C6BipartiteDomination_ZPart_eq_Z0_union_Z1
import Theorems.Thm_C6BipartiteDomination_Z0_Z1_disjoint
import Theorems.Thm_C6BipartiteDomination_responsibilityRegion_ZPart
import Theorems.Thm_C6BipartiteDomination_responsibilityRegion_irreducible


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hBne : (BPart G D).Nonempty)
    (hmax : ∀ v, degreeWithinSet G Finset.univ v ≤ 6)
    (hInd : ProperInducedMainBound G) :
    8 * (W0Part G D).card ≥ 7 * (Z1Part G D).card := by
  classical
  let Z := ZPart G D
  let Z0 := Z0Part G D
  let Z1 := Z1Part G D
  let W0 := W0Part G D
  let S := Z1 ∪ W0
  have hZ1D : Z1 ⊆ D := by
    intro z hz
    exact (mem_ZPart G D z).mp ((mem_Z1Part G D z).mp hz |>.1) |>.1
  have hSsubR : S ⊆ responsibilityRegion G D Z := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvZ1 | hvW0
    · rw [responsibilityRegion_ZPart]
      exact Finset.mem_union_left _ ((mem_Z1Part G D v).mp hvZ1 |>.1)
    · rw [responsibilityRegion_ZPart]
      exact Finset.mem_union_right _ hvW0
  have hZ0Sdisj : Disjoint Z0 S := by
    rw [Finset.disjoint_left]
    intro z hz0 hzS
    rcases Finset.mem_union.mp hzS with hz1 | hw0
    · exact (Finset.disjoint_left.mp (Z0_Z1_disjoint G D) hz0 hz1).elim
    · have hzD : z ∈ D := (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp hz0 |>.1) |>.1
      exact ((mem_W0Part G D z).mp hw0).1 hzD
  have hZ0NoAdjR : ∀ ⦃z v⦄, z ∈ Z0 →
      v ∈ responsibilityRegion G D Z → ¬ G.Adj z v := by
    intro z v hz0 hvR hadj
    rw [responsibilityRegion_ZPart] at hvR
    rcases Finset.mem_union.mp hvR with hvZ | hvW
    · have hzIso := (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp hz0 |>.1)
      have hvD := (mem_ZPart G D v).mp hvZ |>.1
      exact hzIso.2 v hvD hadj
    · exact (mem_Z0Part G D z).mp hz0 |>.2 v hvW hadj
  have hZisolated : IsolatedSubset G D Z := by
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (mem_ZPart G D z).mp hz |>.1
    · intro z u hz hu hadj
      exact (mem_ZPart G D z).mp hz |>.2 u hu hadj
  have hMinD : MinimumBipartiteDominatingSet G D := ⟨hCan.1, hCan.2.1⟩
  have hZ1Local : BipartiteDominatingOn G S Z1 := by
    refine ⟨Finset.subset_union_left, ?_, ?_⟩
    · intro v hvS hvNotZ1
      rcases Finset.mem_union.mp hvS with hvZ1 | hvW0
      · exact (hvNotZ1 hvZ1).elim
      · have hvNotD := (mem_W0Part G D v).mp hvW0 |>.1
        obtain ⟨d, hdD, hdv⟩ := hCan.1.1 hvNotD
        have hdZ : d ∈ ZPart G D := by
          by_contra hdZ
          have hdB : d ∈ BPart G D :=
            (mem_BPart G D d).mpr ⟨hdD, hdZ⟩
          exact (mem_W0Part G D v).mp hvW0 |>.2 d hdB hdv
        have hdZ1 : d ∈ Z1 := (mem_Z1Part G D d).mpr
          ⟨hdZ, v, hvW0, hdv⟩
        exact ⟨d, hdZ1, hdv⟩
    · refine ⟨fun _ => false, ?_⟩
      intro a b ha hb hadj
      have haZ : a ∈ ZPart G D := (mem_Z1Part G D a).mp ha |>.1
      have hbD : b ∈ D := (mem_ZPart G D b).mp
        ((mem_Z1Part G D b).mp hb |>.1) |>.1
      exact (((mem_ZPart G D a).mp haZ).2 b hbD hadj).elim
  have hZ1Min : ∀ E, BipartiteDominatingOn G S E → Z1.card ≤ E.card := by
    intro E hE
    let Y := Z0 ∪ E
    have hYsub : Y ⊆ responsibilityRegion G D Z := by
      intro v hv
      rcases Finset.mem_union.mp hv with hvZ0 | hvE
      · rw [responsibilityRegion_ZPart]
        exact Finset.mem_union_left _ ((mem_Z0Part G D v).mp hvZ0 |>.1)
      · exact hSsubR (hE.1 hvE)
    have hYdom : ∀ ⦃v⦄, v ∈ responsibilityRegion G D Z → v ∉ Y →
        ∃ y ∈ Y, G.Adj y v := by
      intro v hvR hvNotY
      rw [responsibilityRegion_ZPart] at hvR
      rcases Finset.mem_union.mp hvR with hvZ | hvW0
      · have hvZ1 : v ∈ Z1 := by
          have hvZ0orZ1 : v ∈ Z0 ∪ Z1 := by
            rw [← ZPart_eq_Z0_union_Z1 G D]
            exact hvZ
          rcases Finset.mem_union.mp hvZ0orZ1 with h0 | h1
          · exact (hvNotY (Finset.mem_union_left E h0)).elim
          · exact h1
        have hvS : v ∈ S := Finset.mem_union_left _ hvZ1
        have hvNotE : v ∉ E := by
          intro hvE
          exact hvNotY (Finset.mem_union_right Z0 hvE)
        obtain ⟨y, hyE, hadj⟩ := hE.2.1 hvS hvNotE
        exact ⟨y, Finset.mem_union_right Z0 hyE, hadj⟩
      · have hvS : v ∈ S := Finset.mem_union_right Z1 hvW0
        have hvNotE : v ∉ E := by
          intro hvE
          exact hvNotY (Finset.mem_union_right Z0 hvE)
        obtain ⟨y, hyE, hadj⟩ := hE.2.1 hvS hvNotE
        exact ⟨y, Finset.mem_union_right Z0 hyE, hadj⟩
    have hYbip : IsBipartiteOn G Y := by
      rcases hE.2.2 with ⟨c, hc⟩
      refine ⟨fun v => if v ∈ Z0 then false else c v, ?_⟩
      intro a b ha hb hadj
      rcases Finset.mem_union.mp ha with haZ0 | haE
      · rcases Finset.mem_union.mp hb with hbZ0 | hbE
        · have haZ := (mem_Z0Part G D a).mp haZ0 |>.1
          have hbD := (mem_ZPart G D b).mp
            ((mem_Z0Part G D b).mp hbZ0 |>.1) |>.1
          exact ((mem_ZPart G D a).mp ((mem_Z0Part G D a).mp haZ0 |>.1)).2
            b hbD hadj |>.elim
        · have hbR : b ∈ responsibilityRegion G D Z := hSsubR (hE.1 hbE)
          exact (hZ0NoAdjR haZ0 hbR hadj).elim
      · rcases Finset.mem_union.mp hb with hbZ0 | hbE
        · have haR : a ∈ responsibilityRegion G D Z := hSsubR (hE.1 haE)
          exact (hZ0NoAdjR hbZ0 haR hadj.symm).elim
        · have haZ0 : a ∉ Z0 := by
            intro haZ0
            exact (Finset.disjoint_left.mp hZ0Sdisj haZ0 (hE.1 haE)).elim
          have hbZ0 : b ∉ Z0 := by
            intro hbZ0
            exact (Finset.disjoint_left.mp hZ0Sdisj hbZ0 (hE.1 hbE)).elim
          simpa [haZ0, hbZ0] using hc haE hbE hadj
    have hYlocal : BipartiteDominatingOn G (responsibilityRegion G D Z) Y :=
      ⟨hYsub, hYdom, hYbip⟩
    have hIrred := responsibilityRegion_irreducible G hMinD hZisolated hYlocal
    have hYcard : Y.card = Z0.card + E.card := by
      dsimp [Y]
      have hdisj : Disjoint Z0 E := hZ0Sdisj.mono_right hE.1
      rw [Finset.card_union_of_disjoint hdisj]
    have hZcard : Z.card = Z0.card + Z1.card := by
      dsimp [Z, Z0, Z1]
      rw [ZPart_eq_Z0_union_Z1 G D, Finset.card_union_of_disjoint
        (Z0_Z1_disjoint G D)]
    rw [hYcard, hZcard] at hIrred
    omega
  have hSnoIso : ∀ v ∈ S, ∃ u ∈ S, G.Adj v u := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvZ1 | hvW0
    · obtain ⟨u, huW0, hadj⟩ := (mem_Z1Part G D v).mp hvZ1 |>.2
      exact ⟨u, Finset.mem_union_right Z1 huW0, hadj⟩
    · have hvNotD := (mem_W0Part G D v).mp hvW0 |>.1
      obtain ⟨d, hdD, hadj⟩ := hCan.1.1 hvNotD
      have hdZ : d ∈ ZPart G D := by
        by_contra hdZ
        have hdB : d ∈ BPart G D :=
          (mem_BPart G D d).mpr ⟨hdD, hdZ⟩
        exact (mem_W0Part G D v).mp hvW0 |>.2 d hdB hadj
      have hdZ1 : d ∈ Z1 := (mem_Z1Part G D d).mpr
        ⟨hdZ, v, hvW0, hadj⟩
      exact ⟨d, Finset.mem_union_left _ hdZ1, hadj.symm⟩
  have hSdeg : ∀ v ∈ S, degreeWithinSet G S v ≤ 6 := by
    intro v hv
    have hsub : (S.filter fun u => G.Adj v u) ⊆
        (Finset.univ.filter fun u => G.Adj v u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hu).2⟩
    exact (Finset.card_le_card hsub).trans (hmax v)
  have hSproper : S.card < (Finset.univ : Finset V).card := by
    obtain ⟨b, hb⟩ := hBne
    have hbNotS : b ∉ S := by
      intro hbS
      rcases Finset.mem_union.mp hbS with hbZ1 | hbW0
      · have hbZ := (mem_Z1Part G D b).mp hbZ1 |>.1
        exact (mem_BPart G D b).mp hb |>.2 hbZ
      · have hbD := (mem_BPart G D b).mp hb |>.1
        exact ((mem_W0Part G D b).mp hbW0).1 hbD
    apply Finset.card_lt_card
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hUnivSub
    exact hbNotS (hUnivSub (Finset.mem_univ b))
  have hIndBound := hInd S hSproper hSnoIso hSdeg Z1 ⟨hZ1Local, hZ1Min⟩
  have hScard : S.card = Z1.card + W0.card := by
    have hdisj : Disjoint Z1 W0 := by
      rw [Finset.disjoint_left]
      intro v hvZ1 hvW0
      have hvD := hZ1D hvZ1
      exact ((mem_W0Part G D v).mp hvW0).1 hvD
    dsimp [S]
    rw [Finset.card_union_of_disjoint hdisj]
  rw [hScard] at hIndBound
  change 8 * W0.card ≥ 7 * Z1.card
  omega
end C6BipartiteDomination
