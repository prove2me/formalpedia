-- Prove2me | solution 1 for FairSelling.exists_TPS_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:47.56783+00:00
-- url     : https://prove2.me/submissions/70b83e42-5dab-47b8-b47c-949f4bddaa0e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Theorems.Thm_FairSelling_servable_of_invariant
import Theorems.Thm_FairSelling_TPS_nonneg
import Theorems.Thm_FairSelling_TPS_truncSum
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      ∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i := by
  classical
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  set τ : Fin n → ℝ := fun i => ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p with hτdef
  set t : Fin n → ℝ := fun i => TPS n (v i) p with htdef
  have hTPS0 : ∀ i, 0 ≤ TPS n (v i) p := fun i => TPS_nonneg (v i) p hp
  have hτ0 : ∀ i, 0 ≤ τ i := by
    intro i
    exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hden)) (hTPS0 i)
  have htτ : ∀ i, t i ≤ 2 * τ i := by
    intro i
    simp only [hτdef, htdef]
    rw [show (2:ℝ) * (((n : ℝ) / (2 * n - 1)) * TPS n (v i) p)
        = ((2 * n) / (2 * n - 1)) * TPS n (v i) p by field_simp]
    have h1 : (1:ℝ) ≤ (2 * n) / (2 * n - 1) := by
      rw [le_div_iff₀ hden]; linarith
    nlinarith [hTPS0 i]
  -- the initial invariant
  have hinit : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (2 * ((n : ℝ)) - 1) * τ i ≤ truncBundle (v i) p (t i) Finset.univ + 0 := by
    intro i _
    have hfix : truncSum n (v i) p (TPS n (v i) p) = TPS n (v i) p := TPS_truncSum (v i) p hp
    have hsum : truncBundle (v i) p (t i) Finset.univ = (n : ℝ) * TPS n (v i) p := by
      unfold truncBundle trunc
      unfold truncSum at hfix
      rw [htdef]
      field_simp at hfix
      linarith [hfix]
    rw [hsum, add_zero, hτdef]
    field_simp
    exact le_rfl
  obtain ⟨A, F, q, hAR, hFR, hAdisj, hFdisj, hq0, hqsum, hserve, _⟩ :=
    servable_of_invariant v p τ t hτ0 htτ n Finset.univ Finset.univ 0 (by simp) (le_refl 0)
      hinit
  refine ⟨unifiedOutcome v p A F q, ?_, ?_⟩
  · refine unifiedOutcome_valid v p hp A F q hAdisj hFdisj hq0 ?_
    simpa using hqsum
  · intro i
    rw [util_unifiedOutcome]
    exact hserve i (Finset.mem_univ i)
end FairSelling
