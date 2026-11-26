-- Prove2me | solution 1 for EdenVerified.p13_fderiv_evolution_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:23:29.425427+00:00
-- url     : https://prove2.me/submissions/db12c312-1632-46be-89d3-97a79db6a73f

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_evolution_apply


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace),
    fderiv ℝ (evolution c t) p v =
      !₂[planarDerivativeX 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeY 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeX (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         planarDerivativeY (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         Real.exp (-c * t) * v 4] :=
  @Eden.fderiv_evolution_apply
end EdenVerified
