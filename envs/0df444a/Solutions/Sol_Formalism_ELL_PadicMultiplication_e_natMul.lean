-- Prove2me | solution 1 for Formalism.ELL.PadicMultiplication.e_natMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:14.239287+00:00
-- url     : https://prove2.me/submissions/7acb36ff-1407-44b8-8391-ed38186d3e58

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
import Theorems.Thm_Formalism_ELL_PadicMultiplication_constantCoeff_mulN
import Theorems.Thm_Formalism_ELL_PadicMultiplication_log_mulN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicMultiplication
theorem _root_.solution (F : FormalGroup (unitBall K)) (l e : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (hel : e.subst l = X) (m : ℕ) :
    e.subst ((m : K) • l) = (mulN F m).map (unitBall K).subtype := by
  have hM : MvPowerSeries.constantCoeff ((mulN F m).map (unitBall K).subtype) = 0 := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (mulN F m)) = 0
    rw [MvPowerSeries.constantCoeff_map, constantCoeff_mulN]; simp
  rw [← log_mulN F l hl m, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hl.1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hM), hel,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hM)]
end Formalism.ELL.PadicMultiplication
