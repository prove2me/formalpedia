-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.integral_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:21.906259+00:00
-- url     : https://prove2.me/submissions/651982bc-47bc-4d0d-9254-ce31fcfa4462

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
import Theorems.Thm_Formalism_ELL_EulerSeries_integral_map

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
variable [IsUltrametricDist K]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution {f g : MvPowerSeries σ K} (hf : IntegralMv f) (hg : IntegralMv g) :
    IntegralMv (f + g + f * g) := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  have hg' : ∀ n, MvPowerSeries.coeff n g ∈ unitBall K := fun n => hg n
  have := integral_map (f.toSubring _ hf' + g.toSubring _ hg' +
    f.toSubring _ hf' * g.toSubring _ hg')
  simpa only [map_add, map_mul, MvPowerSeries.map_toSubring] using this
end Formalism.ELL.EulerSeries
