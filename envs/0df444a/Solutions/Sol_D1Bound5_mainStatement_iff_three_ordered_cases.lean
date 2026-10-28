-- Prove2me | solution 1 for D1Bound5.mainStatement_iff_three_ordered_cases
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T21:28:55.42013+00:00
-- url     : https://prove2.me/submissions/b7772455-6c33-498a-898a-5d9f99db9baf

import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_MainStatement
import Mathlib.Analysis.Complex.Basic
import Lean.Elab.Tactic.Omega
import Theorems.Thm_D1Bound5_card_bound_iff_three_ordered_cases
open scoped NumberField
universe u

namespace D1Bound5

theorem _root_.solution :
    MainStatement.{u} ↔
      ∀ (K : Type u) [Field K] [NumberField K]
        [NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
        ∀ phi : K →+* ℂ,
          (∀ t : Fin 6 → 𝓞 K, IsD1Tuple t →
            Monotone (fun i => ‖phi (t i : K)‖) →
            3 ≤ ‖phi (t 0 : K)‖ → False) ∧
          (∀ t : Fin 6 → 𝓞 K, IsD1Tuple t →
            Monotone (fun i => ‖phi (t i : K)‖) →
            ‖phi (t 0 : K)‖ < 3 → 3 ≤ ‖phi (t 1 : K)‖ → False) ∧
          (∀ t : Fin 6 → 𝓞 K, IsD1Tuple t →
            Monotone (fun i => ‖phi (t i : K)‖) →
            ‖phi (t 1 : K)‖ < 3 → False) := by
  constructor
  · intro h K _ _ _ hK phi
    exact (card_bound_iff_three_ordered_cases
      (fun z : 𝓞 K => ‖phi (z : K)‖) (3 : ℝ)).mp (h K hK)
  · intro h
    intro K _ _ _ hK
    let phi : K →+* ℂ := Classical.choice inferInstance
    exact (card_bound_iff_three_ordered_cases
      (fun z : 𝓞 K => ‖phi (z : K)‖) (3 : ℝ)).mpr (h K hK phi)

end D1Bound5
