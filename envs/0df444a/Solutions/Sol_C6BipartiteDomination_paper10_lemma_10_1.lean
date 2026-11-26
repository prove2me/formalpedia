-- Prove2me | solution 1 for C6BipartiteDomination.paper10_lemma_10_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:43.527799+00:00
-- url     : https://prove2.me/submissions/e0f26725-3253-4a7c-bd7e-103cb04a6bc6

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
import Theorems.Thm_C6BipartiteDomination_mem_paper10SpecialQSet
import Theorems.Thm_C6BipartiteDomination_paper10SpecialEndpoint_mem
import Theorems.Thm_C6BipartiteDomination_paper10_z0_has_S_neighbor
import Theorems.Thm_C6BipartiteDomination_paper10_fiber_plus_one_le_degree
import Theorems.Thm_C6BipartiteDomination_sum_degreeTo_symm


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    (paper10SpecialQSet G hCan hmax).card ≤
      incidenceTotal G D - (Z0Part G D).card := by
  classical
  let Q := paper10SpecialQSet G hCan hmax
  have hQ : ∀ q ∈ Q, IsPaper10SpecialQ G hCan hmax q := by
    intro q hq
    exact (mem_paper10SpecialQSet G hCan hmax q).mp hq
  by_cases hQempty : Q = ∅
  · have hlocal : ∀ z ∈ Z0Part G D, 1 ≤ degreeTo G (SPart G D) z := by
      intro z hz
      obtain ⟨q, hqS, hqAdj⟩ := paper10_z0_has_S_neighbor G hNoIso hz
      unfold degreeTo
      have hmem : q ∈ (SPart G D).filter (fun v => G.Adj z v) :=
        Finset.mem_filter.mpr ⟨hqS, hqAdj⟩
      have := Finset.card_pos.mpr ⟨q, hmem⟩
      omega
    have hsum := Finset.sum_le_sum hlocal
    have hinc := sum_degreeTo_symm G (Z0Part G D) (SPart G D)
    have hinc' : (∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z) =
        incidenceTotal G D := by
      rw [hinc]
      simp [incidenceTotal, kCharge]
    have hzbound : (Z0Part G D).card ≤ incidenceTotal G D := by
      calc
        (Z0Part G D).card = ∑ z ∈ Z0Part G D, (1 : ℕ) := by simp
        _ ≤ ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := hsum
        _ = incidenceTotal G D := hinc'
    simp only [Q, hQempty, Finset.card_empty]
    omega
  · obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hQempty
    let zOf := fun q : V => (paper10SpecialEndpoint G hCan hmax q).getD q₀
    have hmap : ∀ q ∈ Q, zOf q ∈ Z0Part G D := by
      intro q hq
      obtain ⟨z, hz, he⟩ := paper10SpecialEndpoint_mem G hCan hmax (hQ q hq)
      change (paper10SpecialEndpoint G hCan hmax q).getD q₀ ∈ Z0Part G D
      rw [he]
      simpa using hz
    have hmapSet : (Q : Set V).MapsTo zOf (Z0Part G D : Set V) := by
      intro q hq
      exact hmap q hq
    let fiber := fun z => Q.filter (fun q => zOf q = z)
    have hget : ∀ q ∈ Q, ∀ z,
        (zOf q = z ↔ paper10SpecialEndpoint G hCan hmax q = some z) := by
      intro q hq z
      obtain ⟨z', hz', he'⟩ := paper10SpecialEndpoint_mem G hCan hmax (hQ q hq)
      change (paper10SpecialEndpoint G hCan hmax q).getD q₀ = z ↔
        paper10SpecialEndpoint G hCan hmax q = some z
      rw [he']
      simp
    have hfiber : ∀ z, fiber z = paper10SpecialFiber G hCan hmax Q hQ z := by
      intro z
      ext q
      simp only [fiber, paper10SpecialFiber, Finset.mem_filter]
      constructor
      · rintro ⟨hqQ, hqz⟩
        exact ⟨hqQ, (hget q hqQ z).mp hqz⟩
      · rintro ⟨hqQ, he⟩
        exact ⟨hqQ, (hget q hqQ z).mpr he⟩
    have hcard := Finset.card_eq_sum_card_fiberwise (s := Q)
      (t := Z0Part G D) (f := zOf) hmapSet
    have hsumLocal :
        (∑ z ∈ Z0Part G D, ((fiber z).card + 1)) ≤
          ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := by
      apply Finset.sum_le_sum
      intro z hz
      rw [hfiber z]
      exact paper10_fiber_plus_one_le_degree G hCan hmax hNoIso hQ hz
    have hinc := sum_degreeTo_symm G (Z0Part G D) (SPart G D)
    have hinc' : (∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z) =
        incidenceTotal G D := by
      rw [hinc]
      simp [incidenceTotal, kCharge]
    have hbound : Q.card + (Z0Part G D).card ≤ incidenceTotal G D := by
      calc
        Q.card + (Z0Part G D).card =
            (∑ z ∈ Z0Part G D, (fiber z).card) + (Z0Part G D).card := by rw [hcard]
        _ = ∑ z ∈ Z0Part G D, ((fiber z).card + 1) := by simp [Finset.sum_add_distrib]
        _ ≤ ∑ z ∈ Z0Part G D, degreeTo G (SPart G D) z := hsumLocal
        _ = incidenceTotal G D := hinc'
    change Q.card ≤ incidenceTotal G D - (Z0Part G D).card
    omega
end C6BipartiteDomination
