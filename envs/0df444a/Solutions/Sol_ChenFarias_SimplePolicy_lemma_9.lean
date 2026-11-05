-- Prove2me | solution 1 for ChenFarias.SimplePolicy.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:43:53.584755+00:00
-- url     : https://prove2.me/submissions/df219d07-25c5-471d-955d-9f049c44cb78

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
import Theorems.Thm_ChenFarias_SimplePolicy_policy_value
import Theorems.Thm_ChenFarias_SimplePolicy_exp_horizon_identity
import Theorems.Thm_ChenFarias_SimplePolicy_max_horizon_bound
import Theorems.Thm_ChenFarias_SimplePolicy_expected_max

open scoped ENNReal
open ChenFarias.SimplePolicy

theorem solution (lam β T : ℝ) (x0 : ℕ) (f : ℝ → ℝ)
    (hlam : 0 < lam) (hβ : 0 < β) (hT : 0 < T)
    (hf : Assumption1 f) (V : ℕ → ℝ)
    (hV : IsValueFn lam β f V) (π : ℕ → ℝ)
    (hπ : IsRootPolicy f V π) :
    ENNReal.ofReal (V x0) ≤
      ENNReal.ofReal (1 + Real.exp (-(β * T)) / (β * T)) *
        J lam f π x0 T := by
  rw [policy_value lam β f V π x0 hlam hβ hf hV hπ,
    exp_horizon_identity lam β f V π x0 hlam hβ hf hV hπ,
    ← expected_max β T hβ hT]
  exact max_horizon_bound lam β T f V π x0 hlam hβ hT hf hV hπ
