-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.qgModeHamiltonian_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:15:22.70219+00:00
-- url     : https://prove2.me/submissions/291b3fd0-e8d5-4387-bec4-b84418332188

import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore

set_option autoImplicit false

open Filter Topology BookProof.FarisLavine BookProof.QuantumGravityDensitized in
theorem qg_defTriv_9a04 (a b V : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (mulSymbolDomain (qgModeSymbol a b V)) (qgModeHamiltonian a b V) z := by
  intro w hw
  ext n
  have h := hw (mulBasis (qgModeSymbol a b V) n)
  have hT : ((qgModeHamiltonian a b V (mulBasis (qgModeSymbol a b V) n)) : L2Nat)
      = (lp.single 2 n (qgModeSymbol a b V n : ℂ) : L2Nat) := by
    ext m
    by_cases hmn : m = n
    · subst hmn
      simp [qgModeHamiltonian, mulHamiltonian, mulSymbolOp, mulBasis, mulSymbolFun,
        lp.single_apply]
    · simp [qgModeHamiltonian, mulHamiltonian, mulSymbolOp, mulBasis, mulSymbolFun,
        lp.single_apply, Pi.single_eq_of_ne hmn]
  have hv : ((mulBasis (qgModeSymbol a b V) n : mulSymbolDomain (qgModeSymbol a b V)) : L2Nat)
      = lp.single 2 n (1 : ℂ) := rfl
  rw [hT, hv, lp.inner_single_left, lp.inner_single_left] at h
  have h' : (qgModeSymbol a b V n : ℂ) * (w : ℕ → ℂ) n = z * (w : ℕ → ℂ) n := by
    simp only [RCLike.inner_apply, Complex.conj_ofReal, map_one] at h
    simp only [one_mul] at h ⊢
    rw [mul_comm]
    simpa [mul_comm] using h
  have hne : (qgModeSymbol a b V n : ℂ) - z ≠ 0 := by
    intro h0
    apply hz
    have := congrArg Complex.im h0
    simpa using this.symm
  have h2 : ((qgModeSymbol a b V n : ℂ) - z) * (w : ℕ → ℂ) n = 0 := by
    rw [sub_mul, h', sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hne
  · simpa using h3

open Filter Topology BookProof.FarisLavine BookProof.QuantumGravityDensitized in
theorem solution (a b V : ℕ → ℝ) :
    EssentiallySelfAdjointOn (mulSymbolDomain (qgModeSymbol a b V)) (qgModeHamiltonian a b V) := by
  exact ⟨qg_defTriv_9a04 a b V (by simp), qg_defTriv_9a04 a b V (by simp)⟩
