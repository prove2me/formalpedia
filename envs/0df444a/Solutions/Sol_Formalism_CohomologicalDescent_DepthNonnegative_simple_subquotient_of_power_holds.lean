-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.simple_subquotient_of_power_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:31.365577+00:00
-- url     : https://prove2.me/submissions/e7598cbb-8591-4c7b-94c8-0d4720f84a55

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open CategoryTheory CategoryTheory.Limits
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : SimpleSubquotOfPower := by
  intro O _ A _ _ V _ _ _ _ ϖ n F F' hFF hn hsimple
  classical
  have hcov : F ⋖ F' := (covBy_iff_quot_is_simple hFF).mpr hsimple
  set Fa : ℕ → Submodule A V := fun a => F ⊔ (F' ⊓ scaleSub A V (ϖ ^ a)) with hFa
  have hle : ∀ a, F ≤ Fa a := fun a => le_sup_left
  have hle' : ∀ a, Fa a ≤ F' := fun a => sup_le hFF inf_le_left
  have h0 : Fa 0 = F' := by
    apply le_antisymm (hle' 0)
    intro x hx
    exact Submodule.mem_sup_right ⟨hx, x, by simp⟩
  have hnF : Fa n = F := le_antisymm (sup_le le_rfl (inf_le_right.trans hn)) (hle n)
  have hex : ∃ a, Fa a = F := ⟨n, hnF⟩
  have ha1 := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h, h0] at ha1
    exact hcov.ne ha1.symm
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have haF' : Fa a = F' := by
    rcases hcov.eq_or_eq (hle a) (hle' a) with h | h
    · exact absurd h (Nat.find_min hex (by omega))
    · exact h
  have haF : Fa (a + 1) = F := by rw [← Nat.succ_eq_add_one, ← ha]; exact ha1

  let m : V →ₗ[A] V := (scaleSub A V (ϖ ^ a)).subtype ∘ₗ mulOntoScaledSubmodule A V (ϖ ^ a)
  have hm : ∀ v, m v = ϖ ^ a • v := fun v => rfl
  let E0 : Submodule A V := F'.comap m
  let ψ0 : E0 →ₗ[A] (F' ⧸ F.comap F'.subtype) :=
    (F.comap F'.subtype).mkQ ∘ₗ m.restrict (p := E0) (q := F') (fun x hx => hx)
  have hψ0 : Function.Surjective ψ0 := by
    intro z
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hz' : z ∈ Fa a := haF'.symm ▸ hz
    obtain ⟨u, hu, v, ⟨hv, y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz'
    refine ⟨⟨y, hv⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have : (ϖ ^ a • y) - (u + ϖ ^ a • y) = -u := by abel
    show (ϖ ^ a • y) - (u + ϖ ^ a • y) ∈ F
    rw [this]
    exact F.neg_mem hu
  let π : E0 →ₗ[A] E0.map (scaleSub A V ϖ).mkQ :=
    ((scaleSub A V ϖ).mkQ).restrict (p := E0) (q := E0.map (scaleSub A V ϖ).mkQ)
      (fun x hx => Submodule.mem_map_of_mem hx)
  have hπ : Function.Surjective π := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker ψ0 := by
    rintro ⟨x, hx⟩ hxk
    rw [LinearMap.mem_ker] at hxk ⊢
    have h1 : (scaleSub A V ϖ).mkQ x = 0 := congrArg Subtype.val hxk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨y, rfl⟩ := h1
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show ϖ ^ a • ϖ • y ∈ F
    rw [← haF]
    refine Submodule.mem_sup_right ⟨hx, y, ?_⟩
    rw [pow_succ, mul_smul]
  refine ⟨E0.map (scaleSub A V ϖ).mkQ,
    (LinearMap.ker π).liftQ ψ0 hker ∘ₗ (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := hψ0 z
  refine ⟨LinearMap.quotKerEquivOfSurjective π hπ (Submodule.Quotient.mk x), ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl
end Formalism.CohomologicalDescent.DepthNonnegative
