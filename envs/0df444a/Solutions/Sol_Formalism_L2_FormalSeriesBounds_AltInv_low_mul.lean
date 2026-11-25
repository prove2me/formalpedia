-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.low_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:04.514604+00:00
-- url     : https://prove2.me/submissions/d00bad3e-035d-40d2-9f81-9e8b45587a92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sum
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
open Classical
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
private theorem degree_add_lemma_2 (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add _ a b
  | exact Finsupp.sum_add_index' (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)
end Formalism.L2.FormalSeriesBounds.AltInv
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution {E D D' : ℕ} {f g : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f)
    (hg : OrdV D' g) (hg' : LowLt (v := v) (E + D') g) :
    OrdV (D + D') (f * g) ∧ LowLt (v := v) (E + (D + D')) (f * g) := by
  constructor
  · intro μ hμ
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
    · rw [hg p.2 (by omega), mul_zero]
  · intro μ hμ
    rw [coeff_mul]
    refine intC_sum _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
      exact intC_zero
    · by_cases h2 : p.2.degree < D'
      · rw [hg p.2 h2, mul_zero]
        exact intC_zero
      · exact intC_mul (hf' p.1 (by omega)) (hg' p.2 (by omega))
end Formalism.L2.FormalSeriesBounds.AltInv
