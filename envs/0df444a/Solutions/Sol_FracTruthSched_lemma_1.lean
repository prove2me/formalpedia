-- Prove2me | solution 1 for FracTruthSched.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:36:56.77418+00:00
-- url     : https://prove2.me/submissions/ff1d17fe-1f2b-4160-822d-22012fe30237

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric
import Theorems.Thm_FracTruthSched_padding_sequence_exists
import Theorems.Thm_FracTruthSched_padding_sequence_limit

set_option autoImplicit false

open FracTruthSched

theorem solution {n : ℕ} [NeZero n] (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (ρ : ℝ) (hρ : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ * opt t)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ M : FracMech n (CoreTask n ℓ),
      IsFeasibleOn IsGraphInput M ∧ IsTruthfulOn IsGraphInput M ∧
      (∀ t, IsGraphInput t → makespan M t ≤ ρ * C t) ∧
      (∀ ρ' : ℝ, (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
          makespan (R m) t ≤ ρ' * opt t) →
        ∀ t, IsGraphInput t → makespan M t ≤ ρ' * C t) ∧
      IsEligible M ∧ HasUniqueZeros M ∧ HasZeroTypeIrrelevance M ∧ IsClassSymmetric M := by
  obtain ⟨S⟩ := padding_sequence_exists R hfeas htruth ρ hρ ℓ hℓ
  exact padding_sequence_limit R hfeas htruth ρ hρ ℓ hℓ S
