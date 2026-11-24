-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:00.104813+00:00
-- url     : https://prove2.me/submissions/27a66db1-c433-4ddc-9ce2-f096b55e4adf

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {M : Type} [Monoid M] {l : ℕ} (hl : l.Prime) {x z : M}
    (hx : IsOfFinOrder x) (hz : IsOfFinOrder z) (hc : Nat.Coprime l (orderOf z)) {a : ℕ}
    (h : x ^ (l ^ a) = z ^ (l ^ a)) : primeToPart l x = z := by
  unfold primeToPart
  set m := orderOf x with hm
  have hm0 : m ≠ 0 := hx.orderOf_pos.ne'
  have hmpos : 0 < m := hx.orderOf_pos
  set v := m.factorization l with hv
  set m' := m / l ^ v with hm'
  have hcl : Nat.Coprime l m' := Nat.coprime_ordCompl hl hm0
  have hcop' : Nat.Coprime (l ^ v) m' := Nat.Coprime.pow_left v hcl
  have hm'pos : 0 < m' := Nat.ordCompl_pos l hm0
  have hsplit : l ^ v * m' = m := Nat.ordProj_mul_ordCompl_eq_self m l
  set N := (l ^ v) ^ Nat.totient m' with hN
  set oz := orderOf z with hoz
  have hoz0 : 0 < oz := hz.orderOf_pos
  have hcz : Nat.Coprime (l ^ a) oz := Nat.Coprime.pow_left a hc
  have hφz : 0 < Nat.totient oz := by
    first
    | exact Nat.totient_pos.2 hoz0
    | exact Nat.totient_pos hoz0
  have hφm : 0 < Nat.totient m' := by
    first
    | exact Nat.totient_pos.2 hm'pos
    | exact Nat.totient_pos hm'pos
  set j := (l ^ a) ^ Nat.totient oz with hj
  have hjz : j % oz = 1 % oz := Nat.ModEq.pow_totient hcz
  have hzj : z ^ j = z := by
    rw [← pow_mod_orderOf z j, ← hoz, hjz, pow_mod_orderOf, pow_one]
  have hjr : j = l ^ a * (l ^ a) ^ (Nat.totient oz - 1) := by
    rw [hj, ← pow_succ', Nat.sub_add_cancel hφz]
  have hzx : z = x ^ j := by
    calc z = z ^ j := hzj.symm
      _ = x ^ j := by rw [hjr, pow_mul z, ← h, ← pow_mul]
  have hxj1 : x ^ (j * oz) = 1 := by rw [pow_mul, ← hzx, hoz, pow_orderOf_eq_one]
  have hmj : m ∣ j * oz := orderOf_dvd_of_pow_eq_one hxj1
  have hlvj : l ^ v ∣ j :=
    (Nat.Coprime.pow_left v hc).dvd_of_dvd_mul_right (dvd_trans ⟨m', hsplit.symm⟩ hmj)
  have hlvN : l ^ v ∣ N := dvd_pow_self _ hφm.ne'
  have hj1 : 1 ≤ j := Nat.one_le_pow _ _ (pow_pos hl.pos a)
  obtain ⟨j0, hj0⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m0, hm0'⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
  have hA : x ^ (j * l ^ a) = x ^ (l ^ a) := by rw [pow_mul, ← hzx, ← h]
  have hB : x ^ (l ^ a) * x ^ (m0 * l ^ a) = 1 := by
    rw [← pow_add, show l ^ a + m0 * l ^ a = m * l ^ a by rw [hm0']; ring, pow_mul, hm,
      pow_orderOf_eq_one, one_pow]
  have hx1 : x ^ (j0 * l ^ a) = 1 := by
    calc x ^ (j0 * l ^ a) = x ^ (j0 * l ^ a) * (x ^ (l ^ a) * x ^ (m0 * l ^ a)) := by
          rw [hB, mul_one]
      _ = x ^ (j * l ^ a) * x ^ (m0 * l ^ a) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          rw [hj0]
          ring
      _ = 1 := by rw [hA, hB]
  have hmdvd1 : m ∣ j0 * l ^ a := orderOf_dvd_of_pow_eq_one hx1
  have hm'dvd : m' ∣ j0 :=
    (Nat.Coprime.pow_right a hcl.symm).dvd_of_dvd_mul_right
      (dvd_trans ⟨l ^ v, by rw [mul_comm]; exact hsplit.symm⟩ hmdvd1)
  have hN1 : N ≡ 1 [MOD m'] := Nat.ModEq.pow_totient hcop'
  have hj1' : j ≡ 1 [MOD m'] := by
    rw [hj0]
    have := (Nat.modEq_zero_iff_dvd.2 hm'dvd).add_right 1
    simpa using this
  have hNj1 : N ≡ j [MOD m'] := hN1.trans hj1'.symm
  have hNj2 : N ≡ j [MOD l ^ v] :=
    (Nat.modEq_zero_iff_dvd.2 hlvN).trans (Nat.modEq_zero_iff_dvd.2 hlvj).symm
  have hNj : N ≡ j [MOD m] := by
    rw [← hsplit]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨hNj2, hNj1⟩
  rw [hzx, ← pow_mod_orderOf x N, ← pow_mod_orderOf x j, ← hm]
  rw [show N % m = j % m from hNj]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
