-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.zhat_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:43:57.546527+00:00
-- url     : https://prove2.me/submissions/811d4bf2-f075-465a-9f00-617a52bbaa46

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatNormBound

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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.ZhatBound := by
  intro k r z z'
  set K : Fin (r + 1) → Fin (r + 1) → ℝ := fun a b =>
    ∑ i, ‖fvec k r z a i‖ * ∑ j, (∑ p, ‖Hpk k r i p‖) * ‖fvec k r z' b j‖ with hK
  refine ⟨∑ a, ∑ b, K a b, fun g => ?_⟩
  have hg : ∀ p j, ‖g p j‖ ≤ B.gN g := by
    intro p j
    unfold B.gN
    rw [← Real.sqrt_sq (norm_nonneg (g p j)), ← Complex.normSq_eq_norm_sq]
    apply Real.sqrt_le_sqrt
    exact le_trans (Finset.single_le_sum (f := fun j => Complex.normSq (g p j))
      (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)) (Finset.mem_univ p))
  have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hKnn : ∀ a b, 0 ≤ K a b := fun a b => Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg (fun j _ => mul_nonneg (Finset.sum_nonneg (fun p _ => norm_nonneg _)) (norm_nonneg _))))
  have hC : 0 ≤ ∑ a, ∑ b, K a b := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hKnn a b))
  unfold C2.mx
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hgN)).mpr
  intro a
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hgN)).mpr
  intro b
  show ‖Zhat k r z z' g a b‖ ≤ _
  have hent : ‖Zhat k r z z' g a b‖ ≤ B.gN g * K a b := by
    simp only [Zhat, herm, Matrix.mulVec_mulVec]
    calc ‖star (fvec k r z a) ⬝ᵥ ((Hpk k r * g) *ᵥ fvec k r z' b)‖
        ≤ ∑ i, ‖fvec k r z a i‖ * ∑ j, ‖(Hpk k r * g) i j‖ * ‖fvec k r z' b j‖ := by
          simp only [dotProduct, Matrix.mulVec]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
          rw [norm_mul, Pi.star_apply, norm_star]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
          rw [norm_mul]
      _ ≤ ∑ i, ‖fvec k r z a i‖ * ∑ j, ((∑ p, ‖Hpk k r i p‖) * B.gN g) * ‖fvec k r z' b j‖ := by
          gcongr with i _ j _
          rw [Matrix.mul_apply]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum (fun p _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg p j) (norm_nonneg _))
      _ = B.gN g * K a b := by
          simp only [hK, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          ring
  calc ‖Zhat k r z z' g a b‖ ≤ B.gN g * K a b := hent
    _ ≤ B.gN g * ∑ a, ∑ b, K a b := mul_le_mul_of_nonneg_left
        (le_trans (Finset.single_le_sum (f := fun b => K a b) (fun b _ => hKnn a b) (Finset.mem_univ b))
          (Finset.single_le_sum (f := fun a => ∑ b, K a b)
            (fun a _ => Finset.sum_nonneg (fun b _ => hKnn a b)) (Finset.mem_univ a))) hgN
    _ = (∑ a, ∑ b, K a b) * B.gN g := mul_comm _ _
end Formalism.FourierDecayAlt.P
