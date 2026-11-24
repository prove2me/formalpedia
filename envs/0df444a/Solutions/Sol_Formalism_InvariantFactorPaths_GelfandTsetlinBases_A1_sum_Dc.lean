-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.sum_Dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:46:55.646616+00:00
-- url     : https://prove2.me/submissions/6c4d8038-918c-4c65-b6b3-49b9fd6fe86b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_strip_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A1
section Top
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
end Top
section Col
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
end Col
private theorem card_filter_eq_Ioc_lemma_15 (S : Finset ℤ) (P : ℤ → Prop) [DecidablePred P] (a b : ℤ)
    (hiff : ∀ c, P c ↔ c ∈ Finset.Ioc a b) (hS : ∀ c, P c → c ∈ S) : (S.filter P).card = (b - a).toNat := by
  have e : S.filter P = Finset.Ioc a b := by
    ext c
    rw [Finset.mem_filter, hiff c]
    exact ⟨fun h => h.2, fun h => ⟨hS c ((hiff c).mpr h), h⟩⟩
  rw [e, Int.card_Ioc]
end A1
namespace A1
end A1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) (S : Finset ℤ)
    (hS : ∀ c, colHeight (μ (N + 1)) c ≠ colHeight (μ N) c → c ∈ S) :
    ∑ c ∈ S, Dc μ N c = DD μ N := by
  classical
  obtain ⟨-, hanti, hstr⟩ := hp
  have hN := hstr N (Nat.lt_succ_self N)
  have key : ∀ m : Fin n, (S.filter fun c => Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c ≠ Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c ∧
      m.val = min (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c)).card = (|μ (N + 1) m - μ N m|).toNat := by
    intro m
    by_cases hv : isVec N = true
    · rw [if_pos hv] at hN
      rw [card_filter_eq_Ioc_lemma_15 S (fun c => Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c ≠ Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c ∧ m.val = min (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c)) (μ N m) (μ (N + 1) m)
        (fun c => strip_iff (hanti (N + 1) le_rfl) (hanti N (Nat.le_succ N)) hN c m)
        (fun c h => hS c h.1), abs_of_nonneg (sub_nonneg.mpr (hN.1 m))]
    · rw [if_neg hv] at hN
      rw [card_filter_eq_Ioc_lemma_15 S (fun c => Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c ≠ Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c ∧ m.val = min (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c)) (μ (N + 1) m) (μ N m)
        (fun c => by rw [← strip_iff (hanti N (Nat.le_succ N)) (hanti (N + 1) le_rfl) hN c m, ne_comm, min_comm])
        (fun c h => hS c h.1), abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hN.1 m))]
  unfold Dc DD
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Finsupp.smul_single, smul_eq_mul, mul_one, key m]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
