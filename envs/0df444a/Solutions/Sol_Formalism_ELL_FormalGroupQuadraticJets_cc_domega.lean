-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.cc_domega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:04.907812+00:00
-- url     : https://prove2.me/submissions/606014fe-9b90-4e25-a22e-f61dc36c95fe

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_pd_unit_X
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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (F : FormalGroup (Formalism.G.unitBall K)) :
    PowerSeries.constantCoeff (PowerSeries.derivative K (omegaF F)) =
      ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries) := by
  have hd : ∀ g : PowerSeries K, PowerSeries.derivative K g = MvPowerSeries.pderiv K () g := by
    intro g
    ext n
    rw [PowerSeries.coeff_derivative]
    show _ = MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderiv K () g)
    rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add]
    simp only [Finsupp.single_eq_same]
    rfl
  rw [hd]
  change MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K () (Formalism.ELL.omegaF F)) = _
  unfold Formalism.ELL.omegaF
  rw [pderiv_subst hb, Fin.sum_univ_two]
  simp only [map_add, map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ hb, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, pd_unit_X, map_zero, mul_zero, add_zero, map_one, mul_one]
  rfl
end Formalism.ELL.FormalGroupQuadraticJets
