-- Prove2me | solution 1 for BookProof.Starobinsky.qgR2Mode_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:11:50.584397+00:00
-- url     : https://prove2.me/submissions/486b7c46-d9cd-482c-9c96-dbe72d06f9e0

/- Supporting proof adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0. -/
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
noncomputable section
set_option maxHeartbeats 800000
namespace BookProof.QuantumGravityDensitized
open BookProof.FarisLavine BookProof.NavierStokesFlow
theorem mulHamiltonian_mulBasis (lam : ℕ → ℝ) (n : ℕ) :
    (mulHamiltonian lam (mulBasis lam n) : L2Nat) = lp.single 2 n ((lam n : ℂ)) := by
  ext m
  by_cases hmn : m = n
  · subst hmn
    simp [mulHamiltonian, mulSymbolOp, mulBasis, mulSymbolFun, lp.single_apply]
  · simp [mulHamiltonian, mulSymbolOp, mulBasis, mulSymbolFun, lp.single_apply,
      Pi.single_eq_of_ne hmn]

theorem mulHamiltonian_deficiencyTrivialAt (lam : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (mulSymbolDomain lam) (mulHamiltonian lam) z := by
  intro w hw
  have hcoe : ∀ n : ℕ, ((w : L2Nat) : ℕ → ℂ) n = 0 := by
    intro n
    have h := hw (mulBasis lam n)
    rw [mulHamiltonian_mulBasis lam n] at h
    have hL : (inner ℂ (lp.single 2 n ((lam n : ℂ))) w : ℂ)
        = ((lam n : ℂ)) * ((w : L2Nat) : ℕ → ℂ) n := by
      rw [lp.inner_single_left]
      simp [mul_comm]
    have hR : (inner ℂ ((mulBasis lam n : L2Nat)) w : ℂ) = ((w : L2Nat) : ℕ → ℂ) n := by
      change (inner ℂ (lp.single 2 n (1 : ℂ)) w : ℂ) = _
      rw [lp.inner_single_left]
      simp
    rw [hL, hR] at h
    have hne : ((lam n : ℂ)) - z ≠ 0 := by
      intro hc
      have : z = ((lam n : ℝ) : ℂ) := by linear_combination -hc
      rw [this] at hz
      simp at hz
    have : (((lam n : ℂ)) - z) * ((w : L2Nat) : ℕ → ℂ) n = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left hne
  exact lp.ext (funext hcoe)

theorem qgModeHamiltonian_deficiencyTrivialAt (a b V : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (mulSymbolDomain (qgModeSymbol a b V)) (qgModeHamiltonian a b V) z :=
  mulHamiltonian_deficiencyTrivialAt _ hz
end BookProof.QuantumGravityDensitized
-- Generated from ChapterStarobinskyPotential.lean — theorem BookProof.Starobinsky.qgR2Mode_deficiencyTrivialAt
open BookProof.Starobinsky











open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure






















variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)
theorem solution {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (mulSymbolDomain (qgModeSymbol a b (qgR2ModePotential M alpha Rc)))
      (qgR2ModeHamiltonian a b M alpha Rc) z := by
  exact qgModeHamiltonian_deficiencyTrivialAt a b (qgR2ModePotential M alpha Rc) hz
#print axioms solution
