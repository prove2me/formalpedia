-- Prove2me | solution 1 for EdenVerified.p09_toMatrix_fderiv_planarVectorField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:33.204842+00:00
-- url     : https://prove2.me/submissions/dac0cd61-e405-4999-8f16-c70fea0e8dab

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_toMatrix_fderiv_planarVectorField


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω : ℝ) (p : PlanarSpace),
    (fderiv ℝ (planarVectorField Ω) p).toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
      q (p 0 ^ 2 + p 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (2 * deriv q (p 0 ^ 2 + p 1 ^ 2)) •
          Matrix.vecMulVec (fun i => p i) (fun i => p i) +
        Ω • !![0, -1; 1, 0] :=
  @Eden.toMatrix_fderiv_planarVectorField
end EdenVerified
