-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.exists_prime_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:45.645476+00:00
-- url     : https://prove2.me/submissions/ee11a248-dab8-4262-948a-829f100eb42d

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
theorem _root_.solution {M : Type} [Monoid M] (n : ℕ) (hn : 2 ≤ n) (u : M) (hu : u ^ n = 1)
    (l a : ℕ) (hl : l.Prime) (hla : u ^ (l ^ a) = 1) :
    ∃ l' ∈ n.primeFactors, u ^ (l' ^ padicValNat l' n) = 1 := by
  have hd1 : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hu
  have hd2 : orderOf u ∣ l ^ a := orderOf_dvd_of_pow_eq_one hla
  obtain ⟨k, _, hk'⟩ := (Nat.dvd_prime_pow hl).mp hd2
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hk'
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩, by rw [hk', one_pow]⟩
  · have hln : l ^ k ∣ n := by
      rw [← hk']
      exact hd1
    have hl_n : l ∣ n := (dvd_pow_self l hpos.ne').trans hln
    refine ⟨l, Nat.mem_primeFactors.mpr ⟨hl, hl_n, by omega⟩, ?_⟩
    rw [← orderOf_dvd_iff_pow_eq_one, hk']
    apply pow_dvd_pow
    haveI := Fact.mk hl
    exact (padicValNat_dvd_iff_le (by omega)).mp hln
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
