-- Prove2me | solution 1 for BayesProphet.MultiSec.compensated_coupling_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:57:33.896338+00:00
-- url     : https://prove2.me/submissions/5208f025-43a9-47fa-b575-1950d5a87a72

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem

namespace BayesProphet.MultiSec.CCAux
open BayesProphet.MultiSec OnlineProblem

section General
variable {S Θ A : Type*} (P : OnlineProblem S Θ A)

lemma offVal_local (θ θ' : ℕ → Θ) : ∀ t s, (∀ τ, τ ≤ t → θ τ = θ' τ) →
    P.offVal θ t s = P.offVal θ' t s
  | 0, _, _ => rfl
  | t + 1, s, h => by
    simp only [OnlineProblem.offVal]
    rw [h (t + 1) le_rfl]
    congr 1; funext a
    rw [offVal_local θ θ' t _ (fun τ hτ => h τ (by omega))]

lemma stateAux_local (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ θ' : ℕ → Θ)
    (hπ : ∀ t, ∀ θ θ' : ℕ → Θ, θ t = θ' t → π t θ = π t θ')
    (h : ∀ τ, τ ≤ T → θ τ = θ' τ) : ∀ k, P.stateAux π T s₀ θ k = P.stateAux π T s₀ θ' k
  | 0 => rfl
  | k + 1 => by
    simp only [OnlineProblem.stateAux]
    rw [stateAux_local π T s₀ θ θ' hπ h k, hπ (T - k) θ θ' (h _ (by omega)), h (T - k) (by omega)]

lemma regret_local (π : Policy S Θ A) (T : ℕ) (s₀ : S) (θ θ' : ℕ → Θ)
    (hπ : ∀ t, ∀ θ θ' : ℕ → Θ, θ t = θ' t → π t θ = π t θ')
    (h : ∀ τ, τ ≤ T → θ τ = θ' τ) : P.regret π T s₀ θ = P.regret π T s₀ θ' := by
  unfold OnlineProblem.regret OnlineProblem.onlineValue OnlineProblem.onlineState
  rw [offVal_local P θ θ' T s₀ h]
  congr 1
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have ht' := (Finset.mem_Icc.mp ht).2
  rw [stateAux_local P π T s₀ θ θ' hπ h, hπ t θ θ' (h t ht'), h t ht']

lemma stateAux_shift (π : Policy S Θ A) (T : ℕ) (s : S) (θ : ℕ → Θ) : ∀ k,
    P.stateAux π (T + 1) s θ (k + 1) =
      P.stateAux π T (P.trans (π (T + 1) θ s) s (θ (T + 1))) θ k
  | 0 => by simp [OnlineProblem.stateAux]
  | k + 1 => by
    rw [OnlineProblem.stateAux, stateAux_shift π T s θ k, OnlineProblem.stateAux]
    rw [show T + 1 - (k + 1) = T - k by omega]

lemma regret_succ (π : Policy S Θ A) (T : ℕ) (s : S) (θ : ℕ → Θ) :
    P.regret π (T + 1) s θ =
      P.margComp θ (T + 1) (π (T + 1) θ s) s +
        P.regret π T (P.trans (π (T + 1) θ s) s (θ (T + 1))) θ := by
  unfold OnlineProblem.regret OnlineProblem.margComp
  have hv : P.onlineValue π (T + 1) s θ =
      P.reward (π (T + 1) θ s) s (θ (T + 1)) +
        P.onlineValue π T (P.trans (π (T + 1) θ s) s (θ (T + 1))) θ := by
    unfold OnlineProblem.onlineValue
    rw [Finset.sum_Icc_succ_top (by omega), add_comm]
    congr 1
    · simp [OnlineProblem.onlineState, OnlineProblem.stateAux]
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      have ht' := (Finset.mem_Icc.mp ht).2
      unfold OnlineProblem.onlineState
      rw [show T + 1 - t = (T - t) + 1 by omega, stateAux_shift]
  rw [hv, Nat.add_sub_cancel]
  ring


lemma onlineState_shift (π : Policy S Θ A) (T : ℕ) (s : S) (θ : ℕ → Θ) (t : ℕ) (ht : t ≤ T) :
    P.onlineState π (T + 1) s θ t =
      P.onlineState π T (P.trans (π (T + 1) θ s) s (θ (T + 1))) θ t := by
  unfold OnlineProblem.onlineState
  rw [show T + 1 - t = (T - t) + 1 by omega, stateAux_shift]

lemma offVal_le (θ : ℕ → Θ) (c₂ : ℝ)
    (hP : ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
      (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧ P.reward a s j ≤ c₂) :
    ∀ t s, P.offVal θ t s ≤ t * c₂
  | 0, _ => by simp [OnlineProblem.offVal]
  | t + 1, s => by
    obtain ⟨a0, ha0, hmax, hc⟩ := hP s (θ (t + 1))
    haveI : Nonempty (P.feasible s) := ⟨⟨a0, ha0⟩⟩
    simp only [OnlineProblem.offVal]
    apply ciSup_le
    rintro ⟨a, ha⟩
    have h1 := hmax a ha
    have h2 := offVal_le θ c₂ hP t (P.trans a s (θ (t + 1)))
    push_cast
    linarith

lemma le_offVal (θ : ℕ → Θ) (c₂ : ℝ)
    (hP : ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
      (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧ P.reward a s j ≤ c₂)
    (t : ℕ) (s : S) (a : A) (ha : a ∈ P.feasible s) :
    P.reward a s (θ (t + 1)) + P.offVal θ t (P.trans a s (θ (t + 1))) ≤ P.offVal θ (t + 1) s := by
  obtain ⟨a0, ha0, hmax, hc⟩ := hP s (θ (t + 1))
  simp only [OnlineProblem.offVal]
  have hbdd : BddAbove (Set.range fun a : P.feasible s =>
      P.reward a s (θ (t + 1)) + P.offVal θ t (P.trans a s (θ (t + 1)))) := by
    refine ⟨c₂ + t * c₂, ?_⟩
    rintro _ ⟨⟨a', ha'⟩, rfl⟩
    have h1 := hmax a' ha'
    have h2 := offVal_le P θ c₂ hP t (P.trans a' s (θ (t + 1)))
    simp only
    linarith
  exact le_ciSup hbdd (⟨a, ha⟩ : P.feasible s)

lemma margComp_mul_ind (θ : ℕ → Θ) (c₂ : ℝ)
    (hP : ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
      (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧ P.reward a s j ≤ c₂)
    (t : ℕ) (s : S) (a : A) (ha : a ∈ P.feasible s) :
    P.margComp θ (t + 1) a s * P.disagreeInd θ (t + 1) a s = P.margComp θ (t + 1) a s := by
  classical
  unfold OnlineProblem.disagreeInd
  split_ifs with hd
  · ring
  · unfold OnlineProblem.Disagree at hd
    push Not at hd
    have := le_offVal P θ c₂ hP t s a ha
    unfold OnlineProblem.margComp
    rw [Nat.add_sub_cancel] at hd ⊢
    linarith

end General

end BayesProphet.MultiSec.CCAux

open BayesProphet.MultiSec BayesProphet.MultiSec.CCAux OnlineProblem in
theorem solution {S Θ A : Type*} (P : OnlineProblem S Θ A)
    (hP : P.StandingAssumption) (T : ℕ) (π : Policy S Θ A) (hπ : P.IsOnlinePolicy T π)
    (s₀ : S) (θ : ℕ → Θ) :
    P.regret π T s₀ θ =
      ∑ t ∈ Finset.Icc 1 T,
        P.margComp θ t (π t θ (P.onlineState π T s₀ θ t)) (P.onlineState π T s₀ θ t) *
          P.disagreeInd θ t (π t θ (P.onlineState π T s₀ θ t)) (P.onlineState π T s₀ θ t) := by
  obtain ⟨c₁, c₂, -, -, hc⟩ := hP
  have hP' : ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
      (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧ P.reward a s j ≤ c₂ := by
    intro s j
    obtain ⟨a, ha, h1, -, h3⟩ := hc s j
    exact ⟨a, ha, h1, h3⟩
  have hf := hπ.1
  clear hπ
  induction T generalizing s₀ with
  | zero =>
    simp [OnlineProblem.regret, OnlineProblem.onlineValue, OnlineProblem.offVal]
  | succ T ih =>
    have hf' : ∀ t ∈ Finset.Icc 1 T, ∀ (θ : ℕ → Θ) (s : S), π t θ s ∈ P.feasible s := by
      intro t ht θ s
      exact hf t (by simp at ht ⊢; omega) θ s
    rw [regret_succ, ih _ hf', Finset.sum_Icc_succ_top (by omega), add_comm]
    have hs : P.onlineState π (T + 1) s₀ θ (T + 1) = s₀ := by
      simp [OnlineProblem.onlineState, OnlineProblem.stateAux]
    rw [hs, margComp_mul_ind P θ c₂ hP' T s₀ _ (hf (T + 1) (by simp) θ s₀)]
    congr 1
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [onlineState_shift P π T s₀ θ t (Finset.mem_Icc.mp ht).2]
