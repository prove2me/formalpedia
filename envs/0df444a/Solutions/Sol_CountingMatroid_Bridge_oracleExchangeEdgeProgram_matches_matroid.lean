-- Prove2me | solution 1 for CountingMatroid.Bridge.oracleExchangeEdgeProgram_matches_matroid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T15:49:11.511118+00:00
-- url     : https://prove2.me/submissions/986e0017-b499-4a60-b71c-572d0cdf1494

import Definitions.Def_CountingMatroid_Bridge_ExchangeEdgeInterface
import Theorems.Thm_CountingMatroid_Bridge_oracleExchangeEdgeProgram_correct

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Classical

open CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Under exact independence oracles, the fixed two-query machine's result
is exactly the directed exchange-edge test for matroid intersection. -/
theorem solution {n : ℕ}
    (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n)) (u v : Fin n)
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 16)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = [decide (u ∈ I ∧ v ∉ I)])
    (h7 : c.registers 7 = [decide (u ∉ I ∧ v ∈ I)])
    (h8 : c.registers 8 = List.ofFn (fun j : Fin n =>
      decide (j ∈ insert v (I.erase u))))
    (h9 : c.registers 9 = List.ofFn (fun j : Fin n =>
      decide (j ∈ insert u (I.erase v))))
    (hExact : OAI.CommonBasesFPRAS.ExactOracles M₁ M₂ O) :
    let out := execution oracleExchangeEdgeProgram O c bits 4
    out.control.val = (if matroidExchangeEdge M₁ M₂ I u v then 12 else 10) ∧
    out.registers 6 = [] ∧ out.registers 7 = [] ∧
    out.registers 8 = List.ofFn (fun j : Fin n => decide (j ∈ insert v (I.erase u))) ∧
    out.registers 9 = List.ofFn (fun j : Fin n => decide (j ∈ insert u (I.erase v))) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls + 2 ∧
    out.bitOperations = c.bitOperations + (4 * n + 4) := by
  let qForward : Fin n → Bool := fun j => decide (j ∈ insert v (I.erase u))
  let qReverse : Fin n → Bool := fun j => decide (j ∈ insert u (I.erase v))
  have hsetForward : {j : Fin n | qForward j = true} =
      insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)) := by
    ext j
    simp [qForward, Finset.mem_insert, Finset.mem_erase]
    tauto
  have hsetReverse : {j : Fin n | qReverse j = true} =
      insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)) := by
    ext j
    simp [qReverse, Finset.mem_insert, Finset.mem_erase]
    tauto
  have hForward : O false qForward = true ↔
      M₁.Indep (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n))) := by
    simpa [OAI.CommonBasesFPRAS.ExactOracles, hsetForward] using hExact false qForward
  have hReverse : O true qReverse = true ↔
      M₂.Indep (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n))) := by
    simpa [OAI.CommonBasesFPRAS.ExactOracles, hsetReverse] using hExact true qReverse
  have hForwardBool : O false qForward =
      decide (M₁.Indep (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))) := by
    by_cases hi : M₁.Indep (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))
    · have hq : O false qForward = true := hForward.mpr hi
      rw [hq]
      simp only [hi, decide_true]
    · have hq : O false qForward = false := by
        cases h : O false qForward
        · rfl
        · exact (hi (hForward.mp h)).elim
      rw [hq]
      simp only [hi, decide_false]
  have hReverseBool : O true qReverse =
      decide (M₂.Indep (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)))) := by
    by_cases hi : M₂.Indep (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)))
    · have hq : O true qReverse = true := hReverse.mpr hi
      rw [hq]
      simp only [hi, decide_true]
    · have hq : O true qReverse = false := by
        cases h : O true qReverse
        · rfl
        · exact (hi (hReverse.mp h)).elim
      rw [hq]
      simp only [hi, decide_false]
  rcases oracleExchangeEdgeProgram_correct O bits c
      (decide (u ∈ I ∧ v ∉ I)) (decide (u ∉ I ∧ v ∈ I))
      qForward qReverse hc ho h6 h7 (by simpa [qForward] using h8)
      (by simpa [qReverse] using h9) with
    ⟨hcontrol, h6', h7', h8', h9', hout, hcalls, hcost⟩
  refine ⟨?_, h6', h7', h8', h9', hout, hcalls, hcost⟩
  rw [hForwardBool, hReverseBool] at hcontrol
  simpa [matroidExchangeEdge, and_assoc] using hcontrol

#print axioms solution

