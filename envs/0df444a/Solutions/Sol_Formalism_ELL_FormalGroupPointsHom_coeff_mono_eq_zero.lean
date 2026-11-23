-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.coeff_mono_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:48.527881+00:00
-- url     : https://prove2.me/submissions/7dbd2a69-4211-42d8-88a3-d2f9a1ca287f

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {s t : MvPowerSeries (Fin 2) K} (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) {d e : Fin 2 →₀ ℕ} (h : e.degree < d.degree) :
    MvPowerSeries.coeff e (s ^ (d 0) * t ^ (d 1)) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_mul)
  refine lt_of_lt_of_le ?_ (add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hs0)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ht0))
  rw [degree_fin_two_eq_add_of_ne d] at h
  exact_mod_cast h
end Formalism.ELL.FormalGroupPointsHom
