-- Prove2me | solution 1 for Formalism.UG.P.satake_qbinom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:05.036587+00:00
-- url     : https://prove2.me/submissions/fad161d7-cbdb-480f-9afa-bdaba9d5cfff

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Theorems.Thm_Formalism_UG_P_satakeInv_insert_not_mem
import Theorems.Thm_Formalism_UG_P_satakeInv_insert_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Finset
namespace Formalism.UG.P
theorem _root_.solution (q : ℤ) {α : Type} [LinearOrder α] (s : Finset α) :
    ∀ j : ℕ, (∑ S ∈ s.powersetCard j, q ^ satakeInv s S) * ∏ i ∈ range j, (q ^ (i + 1) - 1) =
      ∏ i ∈ range j, (q ^ (s.card - i) - 1) := by
  induction s using Finset.induction_on_max
  next =>
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have h1 : powersetCard (k + 1) (∅ : Finset α) = ∅ := powersetCard_eq_empty.2 (by simp)
      rw [h1, sum_empty, zero_mul, prod_range_succ']
      simp
  next m s' hm ih =>
    have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have hdisj : Disjoint (powersetCard (k + 1) s') ((powersetCard k s').image (insert m)) := by
        rw [disjoint_left]
        intro S hS hS'
        obtain ⟨T, -, rfl⟩ := mem_image.1 hS'
        exact hmS' ((mem_powersetCard.1 hS).1 (mem_insert_self m T))
      have hinj : Set.InjOn (insert m) (powersetCard k s' : Set (Finset α)) := by
        intro T1 h1 T2 h2 h
        have h1' : m ∉ T1 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h1)).1 h')
        have h2' : m ∉ T2 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h2)).1 h')
        calc T1 = (insert m T1).erase m := (erase_insert h1').symm
          _ = (insert m T2).erase m := by rw [h]
          _ = T2 := erase_insert h2'
      rw [powersetCard_succ_insert hmS', sum_union hdisj, sum_image hinj]
      have e1 : ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv (insert m s') S
          = q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S hS
        obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 hS
        rw [satakeInv_insert_not_mem s' S m hm hsub, hcard, pow_add]
        ring
      have e2 : ∑ T ∈ powersetCard k s', q ^ satakeInv (insert m s') (insert m T)
          = ∑ T ∈ powersetCard k s', q ^ satakeInv s' T :=
        sum_congr rfl (fun T hT => by
          rw [satakeInv_insert_mem s' T m hm (mem_powersetCard.1 hT).1])
      rw [e1, e2]
      have hP : ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
          = (∏ i ∈ range k, (q ^ (i + 1) - 1)) * (q ^ (k + 1) - 1) := prod_range_succ _ _
      have hR : ∏ i ∈ range (k + 1), (q ^ (s'.card + 1 - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card + 1) - 1) := by
        rw [prod_range_succ']
        simp only [Nat.add_sub_add_right, Nat.sub_zero]
      have hRk : ∏ i ∈ range (k + 1), (q ^ (s'.card - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card - k) - 1) :=
        prod_range_succ _ _
      have hsplit :
          (q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S
              + ∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
            = q ^ (k + 1) * ((∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S)
                * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1))
              + ((∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range k, (q ^ (i + 1) - 1))
                * (q ^ (k + 1) - 1) := by
        rw [hP]; ring
      rw [card_insert_of_notMem hmS', hR, hsplit, ih (k + 1), ih k, hRk]
      by_cases hk : k ≤ s'.card
      · have hpow : q ^ (k + 1) * q ^ (s'.card - k) = q ^ (s'.card + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * hpow
      · have hz : ∏ i ∈ range k, (q ^ (s'.card - i) - 1) = 0 :=
          prod_eq_zero (i := s'.card) (mem_range.2 (by omega)) (by simp)
        rw [hz]; ring
end Formalism.UG.P
