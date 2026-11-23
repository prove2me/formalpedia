-- Prove2me | solution 1 for Formalism.MainNotions.J.subst_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:33.629943+00:00
-- url     : https://prove2.me/submissions/5a08641e-d185-4165-ad43-d1c077dc03e6

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
theorem _root_.solution {c : ι → MvPowerSeries κ R} (hc : HasSubst c) {f : MvPowerSeries ι R}
    (hf : constantCoeff f = 0) (a : PowerSeries R) :
    subst c (PowerSeries.subst f a) = PowerSeries.subst (subst c f) a := by
  have hf' : HasSubst (fun _ : Unit => f) := hasSubst_of_finite_constantCoeff_eq_zero (fun _ => hf)
  first
  | exact MvPowerSeries.subst_comp_subst_apply hf' hc a
  | (rw [PowerSeries.subst, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hf' hc])
end Formalism.MainNotions.J
