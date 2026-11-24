-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wl_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:00:19.864076+00:00
-- url     : https://prove2.me/submissions/fee62b07-dbb1-42cb-b1ec-298a8a89ca65

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_comp_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_trace
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_Ecc
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_postcomp
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_precomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (hNat : InvNat) (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) (l : ℕ) {h : V}
    (hh : G.IsHW la h) (h0 : h ≠ 0) [FiniteDimensional K (G.gS {h})]
    (hSch : ∀ φ : (G.gS {h}) →ₗ[K] (G.gS {h}),
      (∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c φ = 0) →
      InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ =
        (LinearMap.trace K _ φ / (Module.finrank K (G.gS {h}) : K)) • LinearMap.id)
    (θ : G.gS {h} →ₗ[K] V) (hθ : ∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x))
    (hθY : ∀ y, θ y ∈ IsoW G W la) (y : G.gS {h}) :
    InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la) ⟨θ y, hθY y⟩ =
      ((Module.finrank K (G.gS {h}) : K))⁻¹ • θ y := by
  have e1 := hNat K (IsoW G W la →ₗ[K] V) (G.gS {h} →ₗ[K] V) (Fin n)
    (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) (homAct (res G _ (G.gS_stable {h})).E G.E)
    (LinearMap.lcomp K V (θ.codRestrict (IsoW G W la) hθY))
    (fun a b φ => homAct_precomp (res G (IsoW G W la) (wl_iso_stable G W la)).E (res G _ (G.gS_stable {h})).E G.E
      (θ.codRestrict (IsoW G W la) hθY) (fun a b x => Subtype.ext (hθ a b x)) a b φ)
    l (List.finRange n) (topC G W la)
  have e2 := hNat K (G.gS {h} →ₗ[K] G.gS {h}) (G.gS {h} →ₗ[K] V) (Fin n)
    (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) (homAct (res G _ (G.gS_stable {h})).E G.E)
    (LinearMap.llcomp K _ _ V θ)
    (fun a b φ => homAct_postcomp (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E G.E θ hθ a b φ)
    l (List.finRange n) ((res G _ (G.gS_stable {h})).comp la)
  have e3 : LinearMap.lcomp K V (θ.codRestrict (IsoW G W la) hθY) (topC G W la) =
      LinearMap.llcomp K _ _ V θ ((res G _ (G.gS_stable {h})).comp la) := by
    ext x
    exact (wl_comp_comm (res G _ (G.gS_stable {h})) G θ (fun c x => hθ c c x) la x).symm
  have h0' : ∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c
      ((res G _ (G.gS_stable {h})).comp la) = 0 := by
    intro c
    ext x
    rw [homAct_apply, (res G _ (G.gS_stable {h})).diag, (res G _ (G.gS_stable {h})).comp_Ecc, sub_self]
    rfl
  rw [e3, ← e2, hSch _ h0', wl_trace G hh h0, map_smul, one_div] at e1
  exact LinearMap.congr_fun e1 y
end Formalism.InvariantFactorPaths.PW
