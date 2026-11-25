-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cross_factor_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:24.600441+00:00
-- url     : https://prove2.me/submissions/87a46d11-b2c5-4843-974f-889e8a5dd0e8

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_conj__aca6ea8d7fad
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_samePart_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_le_of_root_mem
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_lpow_le_rpow_quarter
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_to_part_eq_iff
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_frob
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_pow_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CrossFactorCount := by
  intro K L _ _ _ _ _ δ l P' hl hδ hP' hP'0 hBB
  classical
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hn : Fintype.card K ^ δ - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq)
  have hfin : ∀ (z : L) (m : ℕ), 0 < m → z ^ m = 1 → IsOfFinOrder z := fun z m hm h =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, h⟩
  rcases (P'.rootSet L).eq_empty_or_nonempty with h0 | ⟨y0, hy0⟩
  · convert (by positivity : (0 : ℝ) ≤ (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4))
    norm_cast
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨-, -, x, -, y, hy, -⟩
    rw [h0] at hy
    exact hy
  have hy0r : aeval y0 P' = 0 := (mem_rootSet.mp hy0).2
  have hm' : 0 < Fintype.card K ^ P'.natDegree - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Irreducible.natDegree_pos hP').ne' hq)
  let S := (nthRootsFinset (Fintype.card K ^ δ - 1) (1 : L)).filter
    (fun x => primeToPart l x = primeToPart l y0)
  have hSprop : ∀ x ∈ S, x ^ (Fintype.card K ^ δ - 1) = 1 ∧ primeToPart l x = primeToPart l y0 := by
    intro x hx
    rw [Finset.mem_filter, mem_nthRootsFinset (Nat.pos_of_ne_zero hn)] at hx
    exact hx
  refine le_trans (Nat.cast_le.mpr (card_le_of_root_mem _ ?_ S ?_)) ?_
  · intro c hc
    exact (Finset.mem_filter.mp hc).2.1
  · intro c hc
    obtain ⟨hirr, hc0, x, hx, y, hy, hxy⟩ := (Finset.mem_filter.mp hc).2
    have hxr : aeval x (monicOf c) = 0 := (mem_rootSet.mp hx).2
    have hyr : aeval y P' = 0 := (mem_rootSet.mp hy).2
    obtain ⟨k, hk⟩ := root_conj' hP' hyr hy0r
    have hx'r := root_frob (f := monicOf c) k hxr
    refine ⟨x ^ Fintype.card K ^ k, ?_, hx'r⟩
    have hpow : ∀ {z : L}, aeval z (monicOf c) = 0 → z ^ (Fintype.card K ^ δ - 1) = 1 := by
      intro z hz
      have := root_pow_sub_one hirr hc0 hz
      rwa [monicOf_natDegree] at this
    have hyn : y ^ (Fintype.card K ^ P'.natDegree - 1) = 1 := root_pow_sub_one hP' hP'0 hyr
    have hyk : (y ^ Fintype.card K ^ k) ^ (Fintype.card K ^ P'.natDegree - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hyn, one_pow]
    rw [Finset.mem_filter, mem_nthRootsFinset (Nat.pos_of_ne_zero hn)]
    refine ⟨hpow hx'r, ?_⟩
    obtain ⟨a, ha⟩ := (prime_to_part_eq_iff L l x y hl
      (hfin x _ (Nat.pos_of_ne_zero hn) (hpow hxr)) (hfin y _ hm' hyn)).mp hxy
    rw [hk]
    refine (prime_to_part_eq_iff L l _ _ hl
      (hfin _ _ (Nat.pos_of_ne_zero hn) (hpow hx'r)) (hfin _ _ hm' hyk)).mpr ⟨a, ?_⟩
    have hsw : ∀ z : L, (z ^ Fintype.card K ^ k) ^ l ^ a = (z ^ l ^ a) ^ Fintype.card K ^ k :=
      fun z => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hsw, hsw, ha]
  · exact le_trans (Nat.cast_le.mpr (card_samePart_le hl hn _ S hSprop)) (lpow_le_rpow_quarter hBB)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
