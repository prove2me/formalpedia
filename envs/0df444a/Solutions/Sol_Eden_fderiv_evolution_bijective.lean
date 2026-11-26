-- Prove2me | solution 1 for Eden.fderiv_evolution_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:04.081501+00:00
-- url     : https://prove2.me/submissions/16ef1eef-a078-4bfc-9dd8-816e734b9de9

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
import Theorems.Thm_Eden_derivativeFactors_pos
import Theorems.Thm_Eden_fderiv_evolution_orthogonal_decomposition
import Theorems.Thm_Eden_diagonalLinear_bijective

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Function.Bijective (fderiv ℝ (evolution c t) p) := by
  have heq := fderiv_evolution_orthogonal_decomposition c ht p
  change Function.Bijective (fderiv ℝ (evolution c t) p).toLinearMap
  rw [heq]
  have h := (angularRotation t).bijective.comp ((radialFrame p).bijective.comp
    ((diagonalLinear_bijective (fun i => ne_of_gt (derivativeFactors_pos c ht p i))).comp
      (radialFrame p).symm.bijective))
  exact h
end Eden
