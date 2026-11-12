-- Prove2me | solution 1 for FairShares.no_feasible_share_dominates_all_sm_feasible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:26:49.372222+00:00
-- url     : https://prove2.me/submissions/351ebd63-7971-42aa-a874-4cb16aef4bd8

import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_IsShare
import Definitions.Def_FairShares_Feasible
import Definitions.Def_FairShares_SelfMax
import Definitions.Def_FairShares_Dominates
import Definitions.Def_FairShares_IsSMDominantFeasible
import Theorems.Thm_FairShares_pickShare_isShareAt
import Theorems.Thm_FairShares_lemma_14
import Theorems.Thm_FairShares_lemma_15
import Theorems.Thm_FairShares_lemma_16
import Theorems.Thm_FairShares_kpw18_no_mms_allocation

namespace Aux_FairShares_Theorem1
open FairShares

noncomputable def familyShare (Ω : ∀ m n : ℕ, 1 ≤ n → Fin m → Fin n)
    (m n : ℕ) (v : Finset (Fin m) → ℝ) : ℝ :=
  if hn : 1 ≤ n then pickShare (Ω m n hn) v else 0

lemma familyShare_eq (Ω : ∀ m n : ℕ, 1 ≤ n → Fin m → Fin n) {m n : ℕ} (hn : 1 ≤ n) :
    familyShare Ω m n = pickShare (Ω m n hn) := by
  funext v
  exact dif_pos hn

lemma familyShare_isShare (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (Ω : ∀ m n : ℕ, 1 ≤ n → Fin m → Fin n) :
    IsShare C (familyShare Ω) := by
  intro m n hn
  rw [familyShare_eq Ω hn]
  exact pickShare_isShareAt hn (Ω m n hn) (C m)

lemma familyShare_feasible (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (Ω : ∀ m n : ℕ, 1 ≤ n → Fin m → Fin n) :
    Feasible C (familyShare Ω) := by
  intro m n hn
  rw [familyShare_eq Ω hn]
  exact lemma_15 hn (Ω m n hn) (C m)

lemma familyShare_selfMax (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (Ω : ∀ m n : ℕ, 1 ≤ n → Fin m → Fin n) :
    SelfMax C (familyShare Ω) := by
  intro m n hn
  rw [familyShare_eq Ω hn]
  exact lemma_14 hn (Ω m n hn) (C m)

def extendOrder {m₀ n₀ : ℕ} (ω₀ : Fin m₀ → Fin n₀)
    (m n : ℕ) (hn : 1 ≤ n) : Fin m → Fin n :=
  if h : m = m₀ ∧ n = n₀ then
    fun g => ⟨(ω₀ ⟨g.1, h.1 ▸ g.2⟩).1, h.2 ▸ (ω₀ ⟨g.1, h.1 ▸ g.2⟩).2⟩
  else
    fun _ => ⟨0, hn⟩

lemma extendOrder_self {m₀ n₀ : ℕ} (ω₀ : Fin m₀ → Fin n₀) (hn₀ : 1 ≤ n₀) :
    extendOrder ω₀ m₀ n₀ hn₀ = ω₀ := by
  unfold extendOrder
  rw [dif_pos ⟨rfl, rfl⟩]

end Aux_FairShares_Theorem1

open FairShares Aux_FairShares_Theorem1

theorem solution
    (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (hC : ∀ (m : ℕ) (v : Finset (Fin m) → ℝ), IsAdditive v → v ∈ C m) :
    (¬ ∃ s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
        IsShare C s ∧ Feasible C s ∧
          ∀ s' : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
            IsShare C s' → Feasible C s' → SelfMax C s' → Dominates C s s') ∧
      ¬ ∃ s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ, IsSMDominantFeasible C s := by
  have h1 : ¬ ∃ s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
      IsShare C s ∧ Feasible C s ∧
        ∀ s' : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
          IsShare C s' → Feasible C s' → SelfMax C s' → Dominates C s s' := by
    rintro ⟨s, _, hfeas, hdom⟩
    rcases kpw18_no_mms_allocation with ⟨m₀, vs, hadd, hno⟩
    have h3 : 1 ≤ 3 := by decide
    have hvC : ∀ i : Fin 3, vs i ∈ C m₀ := fun i => hC m₀ (vs i) (hadd i)
    rcases hfeas m₀ 3 h3 vs hvC with ⟨A, hA⟩
    refine hno ⟨A, fun i => ?_⟩
    rcases lemma_16 h3 (vs i) (hadd i) with ⟨ω, hω⟩
    have hdom_i := hdom (familyShare (extendOrder ω))
      (familyShare_isShare C (extendOrder ω))
      (familyShare_feasible C (extendOrder ω))
      (familyShare_selfMax C (extendOrder ω))
      m₀ 3 h3 (vs i) (hvC i)
    rw [familyShare_eq (extendOrder ω) h3, extendOrder_self ω h3, hω] at hdom_i
    exact hdom_i.trans (hA i)
  exact ⟨h1, h1⟩
