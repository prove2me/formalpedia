-- Prove2me | solution 1 for Formalism.MainNotions.J.cc_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:37.16856+00:00
-- url     : https://prove2.me/submissions/4eeab7ee-eaac-401c-a7b4-c2817cfec78e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.J
open MvPowerSeries
section AlgebraTools
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
private theorem powerSeries_hasSubst_of_constantCoeff_eq_zero {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    PowerSeries.HasSubst f := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hf
  | (show IsNilpotent _; rw [hf]; exact IsNilpotent.zero)
private theorem coeff_diagS [DecidableEq ι] (a : PowerSeries R) (i : ι) (e : ι →₀ ℕ) :
    coeff e (diagS a i : MvPowerSeries ι R) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) a else 0 := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries ι R) := powerSeries_hasSubst_of_constantCoeff_eq_zero (constantCoeff_X i)
  unfold diagS
  rw [PowerSeries.coeff_subst hX]
  have hterm : ∀ d : ℕ, PowerSeries.coeff d a • coeff e ((X i : MvPowerSeries ι R) ^ d) =
      if e = Finsupp.single i d then PowerSeries.coeff d a else 0 := by
    intro d
    first
    | (rw [MvPowerSeries.coeff_X_pow, smul_eq_mul]; split_ifs <;> simp)
    | (rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]; split_ifs <;> simp)
  simp_rw [hterm]
  rw [finsum_eq_single _ (e i)]
  intro d hd
  have hne : ¬ e = Finsupp.single i d := fun he => hd (by rw [he, Finsupp.single_eq_same])
  simp [hne]
private theorem coeff_diagS_eq_zero_of_apply_eq_zero {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (i : ι) (d : ι →₀ ℕ) (hd : d i = 0) : coeff d (diagS a i : MvPowerSeries ι R) = 0 := by
  classical
  rw [coeff_diagS]
  split_ifs
  · rw [hd, PowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
  · rfl
end AlgebraTools
section Exp
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
end Exp
section Int
variable {ι κ : Type} {K : Type} [Field K]
end Int
end Formalism.MainNotions.J
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
namespace Formalism.MainNotions.J
theorem _root_.solution {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) (i : ι) :
    constantCoeff (diagS a i : MvPowerSeries ι R) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_diagS_eq_zero_of_apply_eq_zero ha i 0 (by simp)
end Formalism.MainNotions.J
