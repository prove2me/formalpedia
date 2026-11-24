-- Prove2me | solution 1 for FairSelling.GeneralTPS.exists_TPS_SEFX_of_money_goods
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:12.489077+00:00
-- url     : https://prove2.me/submissions/c2a83341-740b-488d-a756-db8681adef6a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_SEFX_of_EF
import Theorems.Thm_FairSelling_TPS_le_PS
import Theorems.Thm_FairSelling_TPS_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hvp : ∀ i g, v i g ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  set M : ℝ := (∑ g, p g) / n with hM
  have hMnn : 0 ≤ M := div_nonneg (Finset.sum_nonneg fun g _ => hp g) (by linarith)
  refine ⟨⟨Finset.univ, fun _ => ∅, fun _ => M⟩, ⟨fun j => by simp, fun j k _ => by simp,
    fun j => hMnn, ?_⟩, ?_, ?_⟩
  · show (∑ _j : Fin n, M) ≤ ∑ g ∈ (Finset.univ : Finset G), p g
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hM,
      mul_div_cancel₀ _ hn0]
  · intro i
    -- the proportional share of a pure-money instance is `(∑ p)/n`
    have hPS : PS n (v i) p = M := by
      unfold PS
      rw [hM]
      congr 1
      exact Finset.sum_congr rfl fun g _ => max_eq_left (hvp i g)
    have hTPS : TPS n (v i) p ≤ M := hPS ▸ TPS_le_PS (n := n) (v i) p hp
    have hTPS0 : (0:ℝ) ≤ TPS n (v i) p := TPS_nonneg (n := n) (v i) p hp
    have hratio : (n : ℝ) / (2 * n - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    show ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ (∑ _g ∈ (∅ : Finset G), v i _g) + M
    rw [Finset.sum_empty, zero_add]
    nlinarith
  · refine SEFX_of_EF ?_
    intro i j
    show vbarSum (v i) p ∅ + M ≥ vbarSum (v i) p ∅ + M
    exact le_rfl
end FairSelling.GeneralTPS
