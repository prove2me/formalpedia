-- Prove2me | solution 1 for Formalism.MainNotions.J.descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:49.057511+00:00
-- url     : https://prove2.me/submissions/9b7666be-d76e-4787-bb71-aacb3e007cc2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_hs_dg
import Theorems.Thm_Formalism_MainNotions_J_subst_psubst
import Theorems.Thm_Formalism_MainNotions_J_dg_comp
import Theorems.Thm_Formalism_MainNotions_J_int_subst_dg
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
private theorem hasSubst_of_finite_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {c : σ → MvPowerSeries τ R}
    (hc : ∀ s, constantCoeff (c s) = 0) : HasSubst c := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hc
private theorem diagS_unit (a : PowerSeries R) :
    (diagS a () : MvPowerSeries Unit R) = (a : MvPowerSeries Unit R) := by
  refine MvPowerSeries.ext fun e => ?_
  have he : e = Finsupp.single () (e ()) := Finsupp.ext fun u => by
    cases u
    rw [Finsupp.single_eq_same]
  rw [coeff_diagS, if_pos he]
  conv_rhs => rw [he]
  rfl
private theorem constantCoeff_powerSeries_subst_eq_zero_admissible_parameter_joins {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0)
    {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) :
    constantCoeff (PowerSeries.subst f a) = 0 := by
  obtain ⟨b, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
  first
  | rw [PowerSeries.subst_mul (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), PowerSeries.subst_X (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, hf, zero_mul]
  | rw [← PowerSeries.coe_substAlgHom (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (powerSeries_hasSubst_of_constantCoeff_eq_zero hf), map_mul, hf, zero_mul]
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
variable {ι κ : Type} {K : Type} [Field K]
namespace Formalism.MainNotions.J
theorem _root_.solution (O : Subring K) (th lg ps : PowerSeries K) (hth0 : PowerSeries.constantCoeff th = 0)
    (hps0 : PowerSeries.constantCoeff ps = 0) (hpsO : ∀ n, PowerSeries.coeff n ps ∈ O)
    (hinv : PowerSeries.subst ps th = PowerSeries.X) (hlg0 : PowerSeries.constantCoeff lg = 0)
    (G : MvPowerSeries ι K) (h : ∀ n, coeff n (subst (diagS (PowerSeries.subst th lg)) G) ∈ O) :
    ∀ n, coeff n (subst (diagS lg) G) ∈ O := by
  have hthlg : constantCoeff (PowerSeries.subst th lg) = 0 := constantCoeff_powerSeries_subst_eq_zero_admissible_parameter_joins hth0 hlg0
  have hcomp : PowerSeries.subst ps (PowerSeries.subst th lg) = lg := by
    have hu : HasSubst (fun _ : Unit => ps) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hps0)
    have h1 : PowerSeries.subst ps (PowerSeries.subst th lg) =
        PowerSeries.subst (PowerSeries.subst ps th) lg :=
      subst_psubst hu hth0 lg
    rw [h1, hinv]
    exact diagS_unit lg
  have key : subst (diagS ps) (subst (diagS (PowerSeries.subst th lg)) G) =
      subst (diagS lg) G := by
    rw [MvPowerSeries.subst_comp_subst_apply (hs_dg hthlg) (hs_dg hps0)]
    congr 1
    funext i
    rw [dg_comp hps0 i, hcomp]
  rw [← key]
  exact int_subst_dg O _ h ps hps0 hpsO
end Formalism.MainNotions.J
