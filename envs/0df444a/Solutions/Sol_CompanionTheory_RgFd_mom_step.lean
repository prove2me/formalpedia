-- Prove2me | solution 1 for CompanionTheory.RgFd.mom_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:03.247176+00:00
-- url     : https://prove2.me/submissions/7d4a6e4c-29d5-4cf5-9184-6956f7757085

import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomB
import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomentRecursion_MomStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.RgFd
namespace CompanionTheory.RgFd
theorem _root_.solution {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ν : Measure Ω} {ν' : Measure Ω'} {V : Ω → ℝ}
    {V' : Ω' → ℝ} (hV : Measurable V) (hV' : Measurable V') (h0 : ∀ x, 0 ≤ V x ∧ V x ≤ 1) (h0' : ∀ y, 0 ≤ V' y ∧ V' y ≤ 1)
    (he : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j) ∂ν')
    (hf : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν ≠ ⊤) (M : ℕ) : ∀ j : ℕ, 1 ≤ j →
    ∫⁻ x, ENNReal.ofReal (V x ^ j * (1 - V x) ^ M) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j * (1 - V' y) ^ M) ∂ν' := by
  have split : ∀ {A : Type} [MeasurableSpace A] (m : Measure A) (W : A → ℝ), Measurable W → (∀ x, 0 ≤ W x ∧ W x ≤ 1) →
      ∀ j M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ j * (1 - W x) ^ M) ∂m =
        ∫⁻ x, ENNReal.ofReal (W x ^ j * (1 - W x) ^ (M + 1)) ∂m + ∫⁻ x, ENNReal.ofReal (W x ^ (j + 1) * (1 - W x) ^ M) ∂m := by
    intro A _ m W hW h j M
    rw [← lintegral_add_left (by fun_prop)]
    refine lintegral_congr fun x => ?_
    have a := (h x).1
    have b := sub_nonneg.2 (h x).2
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  induction M with
  | zero => simpa using he
  | succ M ih =>
    intro j hj
    have fin : ∫⁻ x, ENNReal.ofReal (V x ^ (j + 1) * (1 - V x) ^ M) ∂ν ≠ ⊤ := by
      refine ne_top_of_le_ne_top (hf (j + 1) (by omega)) (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
      have a := (h0 x).1
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (sub_nonneg.2 (h0 x).2) (by linarith))
    have e := ih j hj
    rw [split ν V hV h0 j M, split ν' V' hV' h0' j M, ← ih (j + 1) (by omega)] at e
    exact (ENNReal.add_left_inj fin).1 e
end CompanionTheory.RgFd
