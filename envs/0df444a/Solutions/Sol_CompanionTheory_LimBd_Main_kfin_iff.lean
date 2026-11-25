-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.kfin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:23.338521+00:00
-- url     : https://prove2.me/submissions/0127fb05-a346-424c-871d-d0fbfca2bd84

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_back_K
import Theorems.Thm_CompanionTheory_LimBd_Main_forth_K
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (hP : IsCayleyU k r ε P)
    (σ : B.Mat k r → (H →L[ℂ] H)) (v : H) :
    IsKFinHpk (k := k) (r := r) σ v ↔ IsKFin ε (fun g => σ (P⁻¹ * g * P)) v := by
  constructor
  · rintro ⟨S, hS, hv, hst⟩
    exact ⟨S, hS, hv, fun g hg y hy => hst _ (back_K hP hg) y hy⟩
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun x hx y hy => ?_⟩
    have := hst _ (forth_K hP hx) y hy
    simpa only [back_forth hP.1] using this
end CompanionTheory.LimBd.Main
