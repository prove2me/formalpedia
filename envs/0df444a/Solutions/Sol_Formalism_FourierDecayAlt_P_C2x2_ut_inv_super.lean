-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.ut_inv_super
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:32:56.393698+00:00
-- url     : https://prove2.me/submissions/2907f065-69d7-4149-8611-1f2c60856021

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv

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
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x2
theorem _root_.solution {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a : Fin m) (h : a.val + 1 < m) :
    u⁻¹ a ⟨a.val + 1, h⟩ = -u a ⟨a.val + 1, h⟩ := by
  have hi := ut_inv hu
  have hne : a ≠ ⟨a.val + 1, h⟩ := fun e => by have := congrArg Fin.val e; simp at this
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv u (ut_unit hu)) a) ⟨a.val + 1, h⟩
  rw [Matrix.mul_apply, Matrix.one_apply_ne hne, Fintype.sum_eq_add a ⟨a.val + 1, h⟩ hne] at e
  · rw [hu.2, hi.2, one_mul, mul_one] at e
    linear_combination e
  · intro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hl | hl
    · rw [hu.1 a k hl, zero_mul]
    · have : (⟨a.val + 1, h⟩ : Fin m) < k := by
        rw [Fin.lt_def] at hl ⊢
        have : k.val ≠ a.val + 1 := fun e => hk2 (Fin.ext e)
        simp only; omega
      rw [hi.1 k _ this, mul_zero]
end Formalism.FourierDecayAlt.P.C2x2
