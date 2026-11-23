-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.constantCoeff_logOnePlus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:29.775609+00:00
-- url     : https://prove2.me/submissions/a4fa885d-9f68-4e77-a937-2bb71f9e3adf

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (logOnePlus f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hf _ PowerSeries.constantCoeff_log
end Formalism.ELL.EulerSeries
