-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:29.283133+00:00
-- url     : https://prove2.me/submissions/de7a3160-85ac-4aaf-b430-d7a8a82487ae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_finsum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
private theorem hasSubst_lemma [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a :=
  ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
end Formalism.L2.FormalSeriesBounds.AltInv
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ C} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (ha : ∀ s, IntS v (a s)) {γ : MvPowerSeries σ C} (hγ : IntS v γ) : IntS v (subst a γ) := by
  have hsub : HasSubst a := hasSubst_lemma ha0
  intro μ
  rw [coeff_subst hsub]
  refine intC_finsum fun d => ?_
  rw [smul_eq_mul]
  exact intC_mul (hγ d) (intS_prod _ (fun s _ => intS_pow (ha s) _) μ)
end Formalism.L2.FormalSeriesBounds.AltInv
