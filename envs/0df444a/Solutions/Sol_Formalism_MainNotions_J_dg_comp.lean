-- Prove2me | solution 1 for Formalism.MainNotions.J.dg_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:40:08.074817+00:00
-- url     : https://prove2.me/submissions/15e0d90f-092d-4457-b2d9-e1c949b90b36

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_hs_dg
import Theorems.Thm_Formalism_MainNotions_J_subst_psubst
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
private theorem hasSubst_of_finite_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {c : σ → MvPowerSeries τ R}
    (hc : ∀ s, constantCoeff (c s) = 0) : HasSubst c := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hc
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
theorem _root_.solution {a b : PowerSeries R} (hb : PowerSeries.constantCoeff b = 0) (i : ι) :
    subst (diagS b) (diagS a i : MvPowerSeries ι R) = diagS (PowerSeries.subst b a) i := by
  have hc : HasSubst (diagS b : ι → MvPowerSeries ι R) := hs_dg hb
  have hXi : constantCoeff (X i : MvPowerSeries ι R) = 0 := constantCoeff_X i
  have hb' : constantCoeff (b : MvPowerSeries Unit R) = 0 := hb
  have hu : HasSubst (fun _ : Unit => (X i : MvPowerSeries ι R)) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hXi)
  calc subst (diagS b) (diagS a i : MvPowerSeries ι R)
      = PowerSeries.subst (subst (diagS b) (X i : MvPowerSeries ι R)) a :=
        subst_psubst hc hXi a
    _ = PowerSeries.subst (diagS b i) a := by rw [MvPowerSeries.subst_X hc]
    _ = PowerSeries.subst (subst (fun _ : Unit => (X i : MvPowerSeries ι R)) b) a := rfl
    _ = subst (fun _ : Unit => (X i : MvPowerSeries ι R)) (PowerSeries.subst b a) :=
        (subst_psubst hu hb' a).symm
    _ = diagS (PowerSeries.subst b a) i := rfl
end Formalism.MainNotions.J
