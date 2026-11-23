-- Prove2me | solution 1 for Formalism.LIFT.gammaGradedStep_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:30.992311+00:00
-- url     : https://prove2.me/submissions/a56ff479-9c54-4882-a6d5-7fe064ba9d9e

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LIFT
namespace Formalism.LIFT
theorem _root_.solution : GradedStep := by
  intro ℓ _ A _ _ B M D _ _ _ _ W i n hn
  obtain ⟨t, ht⟩ := B.γX
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ k
      = algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t)
        + algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A ((B.u : ℤ_[ℓ]) ^ i) (B.X ^ i • n)]
    module
end Formalism.LIFT
