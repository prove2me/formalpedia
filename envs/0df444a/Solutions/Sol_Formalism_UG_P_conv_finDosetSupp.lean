-- Prove2me | solution 1 for Formalism.UG.P.conv_finDosetSupp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:19.035208+00:00
-- url     : https://prove2.me/submissions/8573a3e8-5bda-43e9-83d9-b4c8c18376af

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Theorems.Thm_Formalism_UG_P_finite_cosets_in_doset
import Theorems.Thm_Formalism_UG_P_finite_support_cosets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution {k : Type} [CommRing k] {K : Subgroup G} (hK : IsCommensurated K)
    (f₁ f₂ : G → k) (hs₁ : FinDosetSupp K f₁) (hs₂ : FinDosetSupp K f₂) :
    FinDosetSupp K (conv K f₁ f₂) := by
  classical
  have hX := finite_support_cosets hK hs₁
  obtain ⟨S₂, hS₂⟩ := hs₂
  set T : Set G := ⋃ t ∈ (S₂ : Set G), ⋃ x ∈ {x : G ⧸ K | f₁ x.out ≠ 0},
    ⋃ y ∈ {y : G ⧸ K | ∃ a b : K, y.out = (a : G) * t * b}, {x.out * y.out} with hTdef
  have hT : T.Finite :=
    S₂.finite_toSet.biUnion fun t _ => hX.biUnion fun x _ =>
      (finite_cosets_in_doset hK t).biUnion fun y _ => Set.finite_singleton _
  refine ⟨hT.toFinset, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (finsum_eq_zero_of_forall_eq_zero h)
  have h1 : f₁ x.out ≠ 0 := left_ne_zero_of_mul hx
  have h2 : f₂ (x.out⁻¹ * g) ≠ 0 := right_ne_zero_of_mul hx
  obtain ⟨t, ht, a, b, hab⟩ := hS₂ _ h2
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * t)
  refine ⟨x.out * (QuotientGroup.mk ((a : G) * t) : G ⧸ K).out, ?_, 1, c⁻¹ * b, ?_⟩
  · rw [Set.Finite.mem_toFinset, hTdef]
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨t, ht, x, h1, _, ⟨a, c, hc⟩, rfl⟩
  · rw [hc]
    have e : g = x.out * (x.out⁻¹ * g) := by group
    rw [e, hab]
    simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    group
end Formalism.UG.P
