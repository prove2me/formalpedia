-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.coeff_Wi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:17.228177+00:00
-- url     : https://prove2.me/submissions/401feb27-83e5-49a0-9158-2879ff3e56fb

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

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
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (w : PowerSeries K) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (Wi w i) = if e = Finsupp.single i (e i) then coeff (e i) w else 0 := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
      | exact PowerSeries.HasSubst.X i
      | exact PowerSeries.HasSubst.X'
  rw [Wi, PowerSeries.coeff_subst ha]
  first
    | simp only [MvPowerSeries.coeff_X_pow]
    | simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h, smul_eq_mul, mul_one]
    · intro d hd
      rw [if_neg, smul_zero]
      intro h'
      apply hd
      rw [h']
      simp
  · have hz : ∀ d : ℕ, (coeff d w • if e = Finsupp.single i d then (1 : K) else 0) = 0 := by
      intro d
      rw [if_neg, smul_zero]
      intro h'
      apply h
      rw [h']
      simp
    simp only [hz, finsum_zero]
end Formalism.ELL.WeierstrassChordSeries
