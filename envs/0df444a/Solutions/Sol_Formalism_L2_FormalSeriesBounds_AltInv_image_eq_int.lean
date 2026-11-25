-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.image_eq_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:09:38.326299+00:00
-- url     : https://prove2.me/submissions/eca861c6-d561-4b6a-a4c1-679e3740055c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_inv
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
theorem _root_.solution [Fintype σ] (Φ t : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntS v γ ∧ F = subst t γ} = {F | IntS v F} := by
  have htI : ∀ y, IntS v (t y) := intS_inv Φ t hΦ0 hΦ hL ht0 heq
  ext F
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact intS_subst ht0 htI hγ
  · intro hF
    have hΦs : HasSubst Φ := hasSubst_lemma hΦ0
    have hts : HasSubst t := hasSubst_lemma ht0
    refine ⟨subst Φ F, intS_subst hΦ0 hΦ hF, ?_⟩
    rw [subst_comp_subst_apply hΦs hts]
    have hX : (fun x => subst t (Φ x)) = (X : σ → MvPowerSeries σ C) := funext heq
    rw [hX, subst_self]
    rfl
end Formalism.L2.FormalSeriesBounds.AltInv
