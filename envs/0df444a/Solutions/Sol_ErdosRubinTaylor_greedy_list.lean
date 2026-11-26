-- Prove2me | solution 1 for ErdosRubinTaylor.greedy_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:08.809545+00:00
-- url     : https://prove2.me/submissions/34b3f075-1f68-4808-86c4-5b3f38ae0227

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
open Classical
namespace ErdosRubinTaylor
theorem _root_.solution {C : Type*} [Nonempty C] (G : SimpleGraph V)
    (L : V → Finset C) (r : V → ℕ) (U : Finset V)
    (hU : ∀ w ∈ U, (univ.filter (fun u => u ∈ U ∧ G.Adj w u ∧ r w ≤ r u)).card < (L w).card) :
    ∃ g : V → C, (∀ v ∈ U, g v ∈ L v) ∧ ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → g u ≠ g v := by
  classical
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => Classical.arbitrary C, by simp, by simp⟩
    obtain ⟨w, hwU, hwmin⟩ := exists_min_image U r hne
    obtain ⟨g, hg1, hg2⟩ := ih (U.erase w) (erase_ssubset hwU) (by
      intro x hx
      refine lt_of_le_of_lt (card_le_card ?_) (hU x (mem_of_mem_erase hx))
      intro u hu
      simp only [mem_filter, mem_univ, true_and, mem_erase] at hu ⊢
      exact ⟨hu.1.2, hu.2⟩)
    set N := (univ.filter (fun u => u ∈ U.erase w ∧ G.Adj w u)).image g
    have hN : N.card < (L w).card := by
      refine lt_of_le_of_lt card_image_le (lt_of_le_of_lt (card_le_card ?_) (hU w hwU))
      intro u hu
      simp only [mem_filter, mem_univ, true_and, mem_erase] at hu ⊢
      exact ⟨hu.1.2, hu.2, hwmin u hu.1.2⟩
    obtain ⟨c, hcL, hcN⟩ := exists_mem_notMem_of_card_lt_card hN
    refine ⟨Function.update g w c, ?_, ?_⟩
    · intro v hv
      by_cases hvw : v = w
      · subst hvw; simpa using hcL
      · rw [Function.update_of_ne hvw]; exact hg1 v (mem_erase.2 ⟨hvw, hv⟩)
    · have hgood : ∀ u ∈ U, u ≠ w → G.Adj w u → c ≠ g u := by
        intro u hu huw hadj h
        apply hcN
        rw [h]
        exact mem_image_of_mem g (by simp [hu, huw, hadj])
      intro u hu v hv huv
      by_cases huw : u = w
      · subst huw
        have hvw : v ≠ u := fun h => G.loopless.irrefl _ (h ▸ huv)
        rw [Function.update_self, Function.update_of_ne hvw]
        exact hgood v hv hvw huv
      · by_cases hvw : v = w
        · subst hvw
          rw [Function.update_self, Function.update_of_ne huw]
          exact (hgood u hu huw huv.symm).symm
        · rw [Function.update_of_ne huw, Function.update_of_ne hvw]
          exact hg2 u (mem_erase.2 ⟨huw, hu⟩) v (mem_erase.2 ⟨hvw, hv⟩) huv
end ErdosRubinTaylor
