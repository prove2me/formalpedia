-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.norm_index_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:53:28.198597+00:00
-- url     : https://prove2.me/submissions/8ed61330-4350-410b-9916-b12327da7d76

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Count_Step_antitone
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Count_sum_succs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
theorem _root_.solution (hS : StripsMem) (hP : GTPieri) (hC : StdCountGT) (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) :
    ∀ (k i : ℕ), i + k = N → ∀ μ₀ : Fin n → ℤ, Antitone μ₀ →
      Finite (ContIdx n i N isVec B μ₀) ∧
      Nat.card (ContIdx n i N isVec B μ₀) = dGT n μ₀ * ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  intro k
  induction k with
  | zero =>
    intro i hi μ₀ hμ
    simp only [add_zero] at hi
    subst hi
    obtain ⟨hfin, hcard⟩ := hC n μ₀ hμ
    have e := baseEquiv n i isVec B μ₀
    refine ⟨Finite.of_equiv _ e.symm, ?_⟩
    rw [Nat.card_congr e, hcard, Finset.Ico_self, Finset.prod_empty, mul_one]
  | succ k ih =>
    intro i hi μ₀ hμ
    have hiN : i < N := by omega
    have e : ContIdx n i N isVec B μ₀ ≃
        Σ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, ContIdx n (i + 1) N isVec B ν.1 :=
      (Equiv.sigmaFiberEquiv (nextW hS hiN isVec B μ₀)).symm.trans
        (Equiv.sigmaCongrRight fun ν => fibreEquiv hS hiN isVec B μ₀ ν)
    have hν : ∀ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, Antitone ν.1 :=
      fun ν => Step.antitone ((mem_succs hS _ _ _ _).1 ν.2)
    have ihν := fun ν : {ν // ν ∈ succs (isVec i) (B i) μ₀} => ih (i + 1) (by omega) ν.1 (hν ν)
    haveI : ∀ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, Finite (ContIdx n (i + 1) N isVec B ν.1) :=
      fun ν => (ihν ν).1
    refine ⟨Finite.of_equiv _ e.symm, ?_⟩
    have hsum : ∑ ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}, Nat.card (ContIdx n (i + 1) N isVec B ν.1) =
        (∑ ν ∈ succs (isVec i) (B i) μ₀, dGT n ν) *
          ∏ l ∈ Finset.Ico (i + 1) N, (n + B l - 1).choose (B l) := by
      rw [Finset.sum_mul, ← Finset.sum_coe_sort (succs (isVec i) (B i) μ₀)]
      exact Finset.sum_congr rfl fun ν _ => (ihν ν).2
    rw [Nat.card_congr e, Nat.card_sigma, hsum, sum_succs hP _ _ _ hμ,
      Finset.prod_eq_prod_Ico_succ_bot hiN]
    ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
