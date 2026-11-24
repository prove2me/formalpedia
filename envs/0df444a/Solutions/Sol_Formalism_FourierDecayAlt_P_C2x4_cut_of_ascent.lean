-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x4.cut_of_ascent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:40.067846+00:00
-- url     : https://prove2.me/submissions/b24d2cff-113c-425b-a718-d73ca1d07c8a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x4
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m)
    (ha : a.val + 1 < m) (hasc : w a < w ⟨a.val + 1, ha⟩) : IsCut w a := by
  have key : ∀ n : ℕ, ∀ x y : Fin m, x ≤ a → a < y → w y < w x → (w x).val - (w y).val = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hx hy hxy hn
      have hxy' : x < y := lt_of_le_of_lt hx hy
      by_cases h1 : (w x).val = (w y).val + 1
      · have := ((hC x y hxy' hxy).1).mpr h1
        have hxa : x = a := by
          apply Fin.ext; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        have hya : y = ⟨a.val + 1, ha⟩ := by
          apply Fin.ext; simp only; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        rw [hxa, hya] at hxy
        exact absurd hasc (not_lt.mpr (le_of_lt hxy))
      · have hlt : (w y).val + 1 < (w x).val := by
          rw [Fin.lt_def] at hxy; omega
        set v : Fin m := ⟨(w y).val + 1, by omega⟩ with hv
        set z := w.symm v with hz
        have hwz : w z = v := by rw [hz, Equiv.apply_symm_apply]
        by_cases hza : z ≤ a
        · apply ih ((w z).val - (w y).val) (by rw [hwz]; simp only [hv]; omega) z y hza hy
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
        · push_neg at hza
          apply ih ((w x).val - (w z).val) (by rw [hwz]; simp only [hv]; omega) x z hx hza
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
  intro x y hx hy
  by_contra hcon
  push_neg at hcon
  have hne : w y ≠ w x := fun e => (ne_of_lt (lt_of_le_of_lt hx hy)) (w.injective e).symm
  exact key _ x y hx hy (lt_of_le_of_ne hcon hne) rfl
end Formalism.FourierDecayAlt.P.C2x4
