-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.xOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:07.921947+00:00
-- url     : https://prove2.me/submissions/b24b97c2-4097-45a0-910a-cd9d13747e69

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_subst_w
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_isUnit_subst

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
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassCoordinateSubstitution
theorem _root_.solution {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) (hne : s ≠ 0) :
    xOf w s = (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (s ^ 2 * u.subst s))⁻¹ := by
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
  have hs' : algebraMap _ (FractionRing (MvPowerSeries σ K)) s ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hne
  have hu' : algebraMap _ (FractionRing (MvPowerSeries σ K)) (u.subst s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (isUnit_subst hu s hs).ne_zero
  rw [xOf, subst_w hwu s hs, map_mul, map_mul, map_pow, map_pow]
  field_simp
end Formalism.ELL.WeierstrassCoordinateSubstitution
