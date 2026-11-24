-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_castform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:02.410169+00:00
-- url     : https://prove2.me/submissions/4cf80e02-d39b-4d23-a801-a100589621cb

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (G : Matrix ι ι ℚ) (w : ι → ℚ) :
    (fun i => (w i : ℝ)) ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) =
      2 * ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by
  have h1 : ((G + Gᵀ).map (Rat.cast : ℚ → ℝ)) = G.map (Rat.cast : ℚ → ℝ) + (G.map (Rat.cast : ℚ → ℝ))ᵀ := by
    ext i j
    simp
  have h2 : ∀ M : Matrix ι ι ℝ, ∀ v : ι → ℝ, v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
    intro M v
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : (((w ⬝ᵥ (G *ᵥ w)) : ℚ) : ℝ) =
      (fun i => (w i : ℝ)) ⬝ᵥ (G.map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
    push_cast
    try rfl
  rw [h1, Matrix.add_mulVec, dotProduct_add, h2, ← h3]
  ring
end Formalism.HermitianLatticesTheory
