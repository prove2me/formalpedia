-- Prove2me | solution 1 for EdenVerified.p13_fderiv_evolution_orthogonal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:23:32.968517+00:00
-- url     : https://prove2.me/submissions/e4a2238c-6357-427c-b510-c999cd239de6

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_evolution_orthogonal_decomposition


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace),
    (fderiv ℝ (evolution c t) p).toLinearMap =
      (angularRotation t).toLinearEquiv.toLinearMap ∘ₗ
        (radialFrame p).toLinearEquiv.toLinearMap ∘ₗ
          diagonalLinear (derivativeFactors c t p) ∘ₗ
            (radialFrame p).symm.toLinearEquiv.toLinearMap :=
  @Eden.fderiv_evolution_orthogonal_decomposition
end EdenVerified
