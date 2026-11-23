-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.eq_of_xy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:30.2975+00:00
-- url     : https://prove2.me/submissions/c9af35db-ffe1-4759-baa2-4f35f02d0fbc

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
    {σ : Type} (A B : MvPowerSeries σ K) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hx : xOf w A = xOf w B)
    (hy : yOf w A = yOf w B) : A = B := by
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
  have key : ∀ s : MvPowerSeries σ K,
      xOf w s = -(algebraMap _ (FractionRing (MvPowerSeries σ K)) s) * yOf w s := by
    intro s
    simp only [xOf, yOf]
    ring
  have zero_of : ∀ s : MvPowerSeries σ K, MvPowerSeries.constantCoeff s = 0 →
      yOf w s = 0 → s = 0 := by
    intro s hs hys
    simp only [yOf, div_eq_zero_iff, neg_eq_zero, one_ne_zero, false_or] at hys
    have h1 : w.subst s = 0 := (map_eq_zero_iff _ hinj).mp hys
    rw [subst_w hwu s hs] at h1
    exact (pow_eq_zero_iff (by norm_num)).mp
      ((mul_eq_zero.mp h1).resolve_right (isUnit_subst hu s hs).ne_zero)
  by_cases hy0 : yOf w A = 0
  · rw [zero_of A hA hy0, zero_of B hB (by rw [← hy]; exact hy0)]
  · have hyB : yOf w B ≠ 0 := by rw [← hy]; exact hy0
    rw [key A, key B, hy] at hx
    exact hinj (neg_inj.mp (mul_right_cancel₀ hyB hx))
end Formalism.ELL.WeierstrassCoordinateSubstitution
