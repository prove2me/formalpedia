-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_val_coeff_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:15.811798+00:00
-- url     : https://prove2.me/submissions/c55a1f59-2fe2-488d-9465-5d3329aae932

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp

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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution {K : Type} [Field K] (v : AddValuation K (WithTop ℝ)) {σ : Type}
    (w : (σ →₀ ℕ) → ℝ) (hw : ∀ m m', w (m + m') = w m + w m') (c : ℝ)
    (h : MvPowerSeries σ K) (hh : ∀ m, ((c - w m : ℝ) : WithTop ℝ) ≤ v (coeff m h)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), (((k : ℝ) * c - w m : ℝ) : WithTop ℝ) ≤ v (coeff m (h ^ k)) := by
  classical
  have hw0 : w 0 = 0 := by have := hw 0 0; simp at this; linarith
  intro k
  induction k with
  | zero =>
    intro m
    rw [pow_zero, coeff_one]
    split_ifs with hm
    · subst hm; simp [hw0]
    · simp
  | succ k ih =>
    intro m
    rw [pow_succ, coeff_mul]
    apply AddValuation.map_le_sum
    intro pq hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [AddValuation.map_mul, ← hpq, hw]
    calc ((((k + 1 : ℕ) : ℝ) * c - (w pq.1 + w pq.2) : ℝ) : WithTop ℝ)
        = (((k : ℝ) * c - w pq.1 : ℝ) : WithTop ℝ) + ((c - w pq.2 : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; congr 1; push_cast; ring
      _ ≤ _ := add_le_add (ih pq.1) (hh pq.2)
end Formalism.IncomingBounds
