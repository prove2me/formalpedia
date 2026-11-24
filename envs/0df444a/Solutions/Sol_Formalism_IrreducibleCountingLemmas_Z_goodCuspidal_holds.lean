-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.goodCuspidal_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:47.242154+00:00
-- url     : https://prove2.me/submissions/03af8f6e-5537-47d9-8f0c-8cdaf18261bf

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : GoodCuspidal := by
  intro k _ P _ r f I _ n d h hdeg hsq hprod hhdeg hn hd hno
  obtain ⟨v0⟩ := ‹Nonempty P›

  have hdvd : ∀ v i, h v i ∣ f v := by
    intro v i
    rw [hprod v]
    exact (dvd_pow_self (h v i) (by have := hd i; omega)).trans
      (Finset.dvd_prod_of_mem (fun j => h v j ^ d j) (Finset.mem_univ i))

  have hd1 : ∀ i, d i = 1 := by
    intro i
    by_contra hne
    have h2 : 2 ≤ d i := by have := hd i; omega
    have hsq' : h v0 i * h v0 i ∣ f v0 := by
      rw [hprod v0]
      refine (?_ : h v0 i * h v0 i ∣ h v0 i ^ d i).trans
        (Finset.dvd_prod_of_mem (fun j => h v0 j ^ d j) (Finset.mem_univ i))
      rw [← pow_two]
      exact pow_dvd_pow _ h2
    have hu := hsq v0 _ hsq'
    have e1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have e2 := hhdeg v0 i
    have e3 := hn i
    omega
  refine ⟨hd1, ?_⟩
  by_contra hcard
  push_neg at hcard
  haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  have hf0 : f v0 ≠ 0 := (hsq v0).ne_zero
  have hne : ∀ l, h v0 l ≠ 0 := by
    intro l hl
    have := hdvd v0 l
    rw [hl, zero_dvd_iff] at this
    exact hf0 this

  have hr : r = ∑ l, n l := by
    rw [← hdeg v0, hprod v0, Polynomial.natDegree_prod _ _ (fun l _ => pow_ne_zero _ (hne l))]
    simp [Polynomial.natDegree_pow, hd1, hhdeg]
  have hle : n i + n j ≤ ∑ l, n l := by
    classical
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rcases le_total (n i) (n j) with hij' | hji'
  · exact hno ⟨n i, hn i, by omega, fun v => ⟨h v i, hdvd v i, hhdeg v i⟩⟩
  · exact hno ⟨n j, hn j, by omega, fun v => ⟨h v j, hdvd v j, hhdeg v j⟩⟩
end Formalism.IrreducibleCountingLemmas.Z
