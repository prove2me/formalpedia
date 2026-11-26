-- Prove2me | solution 1 for EdenVerified.p10_fderiv_planarEvolution_orthogonal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:46.78752+00:00
-- url     : https://prove2.me/submissions/79489263-d703-4513-83e4-ead895ffbff5

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_planarEvolution_orthogonal_decomposition


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PlanarSpace),
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      ((planarRadialFrame p).trans (planarAngularRotation Ω t)).toLinearMap ∘ₗ
        planarDiagonal (planarFactors t p) ∘ₗ (planarRadialFrame p).symm.toLinearMap :=
  @Eden.fderiv_planarEvolution_orthogonal_decomposition
end EdenVerified
