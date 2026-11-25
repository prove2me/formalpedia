-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.block_diagonal_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:42:28.754797+00:00
-- url     : https://prove2.me/submissions/34a6809e-40a0-46bf-92fa-9276ba062c02

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.BlockDiagPSD := by
  classical
  intro α β _ F c k hb
  unfold TB.PSDOn at hb ⊢
  let Fb : β → Finset α := fun b => F.filter fun x => c x = b
  let Q : ∀ b, Matrix F (Fb b) ℂ := fun b => Matrix.of fun x z => if (x : α) = (z : α) then 1 else 0
  have hQM : ∀ b (x : F) (w : Fb b),
      (Q b * Matrix.of (fun x y : Fb b => k x y)) x w = if c x = b then k x w else 0 := by
    intro b x w
    rw [Matrix.mul_apply]
    simp only [Q, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_coe_sort (Fb b) (fun z => if (x : α) = z then k z w else 0), Finset.sum_ite_eq]
    simp [Fb, x.2]
  have hA : ∀ b (x y : F), (Q b * Matrix.of (fun x y : Fb b => k x y) * Matrix.conjTranspose (Q b)) x y =
      if c x = b ∧ c y = b then k x y else 0 := by
    intro b x y
    rw [Matrix.mul_apply]
    simp only [hQM, Matrix.conjTranspose_apply, Q, Matrix.of_apply, apply_ite star, star_one, star_zero,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_coe_sort (Fb b) (fun w => if (y : α) = w then (if c x = b then k x w else 0) else 0),
      Finset.sum_ite_eq]
    by_cases hx : c x = b <;> by_cases hy : c y = b <;> simp [Fb, hx, hy, y.2]
  have hsum : (Matrix.of fun x y : F => if c x = c y then k x y else 0) =
      ∑ b ∈ F.image c, Q b * Matrix.of (fun x y : Fb b => k x y) * Matrix.conjTranspose (Q b) := by
    ext x y
    rw [Matrix.sum_apply]
    simp only [hA, Matrix.of_apply]
    rw [Finset.sum_eq_single (c x)]
    · by_cases h : c x = c y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro b _ hb'
      simp [Ne.symm hb']
    · intro h
      exact absurd (Finset.mem_image_of_mem c x.2) h
  beta_reduce
  rw [hsum]
  exact Matrix.posSemidef_sum _ fun b _ => (hb b).mul_mul_conjTranspose_same (Q b)
end Formalism.FourierDecayAlt.P
