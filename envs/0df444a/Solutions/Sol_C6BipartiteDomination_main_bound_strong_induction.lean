-- Prove2me | solution 1 for C6BipartiteDomination.main_bound_strong_induction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:33.431726+00:00
-- url     : https://prove2.me/submissions/9a3ec8f1-f8de-428a-a254-b5548ca8a28e

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
import Theorems.Thm_C6BipartiteDomination_card_liftFinsetToSubtype
import Theorems.Thm_C6BipartiteDomination_degreeTo_induce_eq_degreeWithinSet
import Theorems.Thm_C6BipartiteDomination_minimumOn_lift_toSubtype
import Theorems.Thm_C6BipartiteDomination_selected_partition_card
import Theorems.Thm_C6BipartiteDomination_outside_partition_card
import Theorems.Thm_C6BipartiteDomination_exists_canonical_two_level_optimum
import Theorems.Thm_C6BipartiteDomination_lemma_5_2_inductive_step
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_paper11_lemma_11_2_global_inequality
import Theorems.Thm_C6BipartiteDomination_proposition_4_1
import Theorems.Thm_C6BipartiteDomination_ratio_from_complement_bound


set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution :
    ∀ n : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), Fintype.card V = n →
      HasNoIsolatedVertices G →
      (∀ v, degreeTo G Finset.univ v ≤ 6) →
      ∀ D, MinimumBipartiteDominatingSet G D → 15 * D.card ≤ 8 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V instF instD G hcard hNoIso hmax D hmin
      classical
      obtain ⟨D₀, hCan⟩ := exists_canonical_two_level_optimum G
      have hmin₀ : MinimumBipartiteDominatingSet G D₀ :=
        ⟨hCan.1, hCan.2.1⟩
      have hsame : D.card = D₀.card := by
        exact le_antisymm (hmin.2 D₀ hmin₀.1) (hmin₀.2 D hmin.1)
      have hmaxWithin : ∀ v, degreeWithinSet G Finset.univ v ≤ 6 := by
        intro v
        simpa [degreeWithinSet, degreeTo] using hmax v
      by_cases hBne : (BPart G D₀).Nonempty
      · have hInd : ProperInducedMainBound G := by
          intro S hSproper hSno hSdeg E hE
          let H : SimpleGraph {v // v ∈ S} := G.induce (S : Set V)
          let E' := liftFinsetToSubtype S E hE.1.1
          have hcardS : Fintype.card {v // v ∈ S} = S.card := by
            classical
            simpa using Finset.card_attach S
          have hNoIsoH : HasNoIsolatedVertices H := by
            intro x
            obtain ⟨y, hyS, hadj⟩ := hSno x.1 x.2
            exact ⟨⟨y, hyS⟩, by simpa [H, SimpleGraph.induce] using hadj⟩
          have hmaxH : ∀ x, degreeTo H Finset.univ x ≤ 6 := by
            intro x
            rw [degreeTo_induce_eq_degreeWithinSet G S x]
            exact hSdeg x x.2
          have hE' : MinimumBipartiteDominatingSet H E' :=
            minimumOn_lift_toSubtype G hE
          have hsmall : S.card < n := by
            simpa [hcard] using hSproper
          have hIH := ih S.card hsmall H hcardS hNoIsoH hmaxH E' hE'
          have hEcard : E'.card = E.card :=
            card_liftFinsetToSubtype hE.1.1
          calc
            15 * E.card = 15 * E'.card := by rw [hEcard]
            _ ≤ 8 * S.card := by simpa [hcardS] using hIH
        have h5 : 8 * (W0Part G D₀).card ≥ 7 * (Z1Part G D₀).card :=
          lemma_5_2_inductive_step G hCan hBne hmaxWithin hInd
        have h11 : 8 * (WBPart G D₀).card ≥
            7 * ((BPart G D₀).card + (Z0Part G D₀).card) :=
          paper11_lemma_11_2_global_inequality G hCan hmax hNoIso
        have hDebt : 8 * (Finset.univ \ D₀).card ≥ 7 * D₀.card := by
          rw [outside_partition_card G D₀, selected_partition_card G D₀]
          omega
        have hratio := ratio_from_complement_bound hDebt
        have htotal : (Finset.univ \ D₀).card + D₀.card = n := by
          have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D₀)
          simpa [hcard] using h
        omega
      · have hDind : Independent G D₀ := by
          intro u v hu hv hadj
          have huZ : u ∈ ZPart G D₀ := by
            by_contra huZ
            have huB : u ∈ BPart G D₀ := by
              simpa [BPart] using (Finset.mem_sdiff.mpr ⟨hu, huZ⟩)
            exact hBne ⟨u, huB⟩
          have huZinfo := (mem_ZPart G D₀ u).mp huZ
          exact huZinfo.2 v hv hadj
        have hHall := proposition_4_1 G hCan.1 hCan.2.1 hDind hNoIso
        have hDebt : 8 * (Finset.univ \ D₀).card ≥ 7 * D₀.card := by
          omega
        have hratio := ratio_from_complement_bound hDebt
        have htotal : (Finset.univ \ D₀).card + D₀.card = n := by
          have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D₀)
          simpa [hcard] using h
        omega
end C6BipartiteDomination
