-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.xOf_ne_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:31.015812+00:00
-- url     : https://prove2.me/submissions/38a5a751-dd9e-4537-a044-528043e2e56d

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_isUnit_subst
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_xOf_eq

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
    {σ : Type} (φ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (s t : MvPowerSeries σ K)
    (hs0 : MvPowerSeries.constantCoeff s = 0) (ht0 : MvPowerSeries.constantCoeff t = 0)
    (hs : s ≠ 0) (ht : t ≠ 0) (hφs : φ s = 0) (hφt : φ t ≠ 0) : xOf w s ≠ xOf w t := by
  intro h
  rw [xOf_eq hwu hu s hs0 hs, xOf_eq hwu hu t ht0 ht, inv_inj] at h
  have h2 := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) h
  have h3 := congrArg φ h2
  rw [map_mul, map_mul, map_pow, map_pow, hφs] at h3
  have hut : IsUnit (φ (u.subst t)) := (isUnit_subst hu t ht0).map φ
  have h4 : φ t ^ 2 * φ (u.subst t) ≠ 0 := mul_ne_zero (pow_ne_zero _ hφt) hut.ne_zero
  apply h4
  rw [← h3]
  simp
end Formalism.ELL.WeierstrassCoordinateSubstitution
