-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.Q_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:04.708148+00:00
-- url     : https://prove2.me/submissions/6db2a510-5953-466b-8a68-9e8eb2178c1c

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type*} [CommRing K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Q (F.subst ![x, y]) =
      ccd 0 F * Q x + ccd 0 x * (ccd 0 (MvPowerSeries.pderiv K 0 F) * ccd 1 x +
          ccd 1 (MvPowerSeries.pderiv K 0 F) * ccd 1 y) +
        ccd 1 F * Q y + ccd 0 y * (ccd 0 (MvPowerSeries.pderiv K 1 F) * ccd 1 x +
          ccd 1 (MvPowerSeries.pderiv K 1 F) * ccd 1 y) := by
  unfold Q
  rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
  rw [pderiv_subst (hv hx hy), pderiv_subst (hv hx hy)]
  simp only [Fin.sum_univ_two, map_add, map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy),
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ccd]
  ring
end Formalism.ELL.FormalGroupQuadraticJets
