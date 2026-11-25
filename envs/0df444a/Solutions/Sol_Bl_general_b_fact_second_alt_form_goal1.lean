-- Prove2me | solution 1 for Bl.general_b_fact_second_alt_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:27.655679+00:00
-- url     : https://prove2.me/submissions/0d4327ce-73b8-440a-852d-2067b2eae2ac

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondAltForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second_alt_form
namespace Bl.general_b_fact_second_alt_form
theorem _root_.solution :
  ∀ {Wq : Type u_1} {Wp : Type u_2} [inst : AddCommGroup.{u_1} Wq] [inst_1 : Module.{0, u_1} Complex Wq]
  [FiniteDimensional.{0, u_1} Complex Wq] [inst_3 : AddCommGroup.{u_2} Wp] [inst_4 : Module.{0, u_2} Complex Wp]
  [FiniteDimensional.{0, u_2} Complex Wp] (S' : Submodule.{0, u_1} Complex Wq) (S : Submodule.{0, u_2} Complex Wp)
  (Gq : Set.{u_1} (Module.End.{0, u_1} Complex Wq)) (Gp : Set.{u_2} (Module.End.{0, u_2} Complex Wp)),
  (∀ (K : Submodule.{0, u_1} Complex Wq),
      LE.le.{u_1} K S' →
        (∀ (A : Module.End.{0, u_1} Complex Wq),
            Membership.mem.{u_1, u_1} Gq A →
              ∀ (v : Wq),
                Membership.mem.{u_1, u_1} K v →
                  Membership.mem.{u_1, u_1} K (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} A v)) →
          Or (Eq.{u_1 + 1} K Bot.bot.{u_1}) (Eq.{u_1 + 1} K S')) →
    (∀ (K : Submodule.{0, u_2} Complex Wp),
        LE.le.{u_2} K S →
          (∀ (B : Module.End.{0, u_2} Complex Wp),
              Membership.mem.{u_2, u_2} Gp B →
                ∀ (w : Wp),
                  Membership.mem.{u_2, u_2} K w →
                    Membership.mem.{u_2, u_2} K (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1} B w)) →
            Or (Eq.{u_2 + 1} K Bot.bot.{u_2}) (Eq.{u_2 + 1} K S)) →
      (∀ (A : Module.End.{0, u_1} Complex Wq),
          Membership.mem.{u_1, u_1} Gq A →
            ∀ (v : Wq),
              Membership.mem.{u_1, u_1} S' v →
                Membership.mem.{u_1, u_1} S' (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} A v)) →
        ∀ (E Z : LinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} Complex) Wq Wp),
          (∀ (v : Wq),
              Membership.mem.{u_1, u_1} S' v →
                Membership.mem.{u_2, u_2} S (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} E v)) →
            (∀ (v : Wq),
                Membership.mem.{u_1, u_1} S' v →
                  Membership.mem.{u_2, u_2} S (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} Z v)) →
              (∀ (A : Module.End.{0, u_1} Complex Wq),
                  Membership.mem.{u_1, u_1} Gq A →
                    Exists.{u_2 + 1} fun (B : Module.End.{0, u_2} Complex Wp) ↦
                      And
                        (Eq.{max (u_1 + 1) (u_2 + 1)} (LinearMap.comp.{0, 0, 0, u_1, u_1, u_2} E A)
                          (LinearMap.comp.{0, 0, 0, u_1, u_2, u_2} B E))
                        (Eq.{max (u_1 + 1) (u_2 + 1)} (LinearMap.comp.{0, 0, 0, u_1, u_1, u_2} Z A)
                          (LinearMap.comp.{0, 0, 0, u_1, u_2, u_2} B Z))) →
                (∀ (B : Module.End.{0, u_2} Complex Wp),
                    Membership.mem.{u_2, u_2} Gp B →
                      Exists.{u_1 + 1} fun (A : Module.End.{0, u_1} Complex Wq) ↦
                        And (Membership.mem.{u_1, u_1} Gq A)
                          (Eq.{max (u_1 + 1) (u_2 + 1)} (LinearMap.comp.{0, 0, 0, u_1, u_1, u_2} E A)
                            (LinearMap.comp.{0, 0, 0, u_1, u_2, u_2} B E))) →
                  (Exists.{u_1 + 1} fun (v : Wq) ↦
                      And (Membership.mem.{u_1, u_1} S' v)
                        (Ne.{u_2 + 1} (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} E v) 0)) →
                    Exists.{1} fun (c : Complex) ↦
                      ∀ (v : Wq),
                        Membership.mem.{u_1, u_1} S' v →
                          Eq.{u_2 + 1} (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} Z v)
                            (HSMul.hSMul.{0, u_2, u_2} c (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1} E v)) := by
  intro Wq Wp _ _ _ _ _ _ S' S Gq Gp hirrq hirrp hinvq E Z hE hZ hcomm hsurj hne
  classical
  obtain ⟨v0, hv0S, hv0⟩ := hne
  have hker : S' ⊓ LinearMap.ker E = ⊥ := by
    rcases hirrq (S' ⊓ LinearMap.ker E) inf_le_left (by
      intro A hA v hv
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
      obtain ⟨B, hB1, -⟩ := hcomm A hA
      refine ⟨hinvq A hA v hv.1, ?_⟩
      have h3 := LinearMap.congr_fun hB1 v
      simp only [LinearMap.comp_apply] at h3
      rw [h3, hv.2, map_zero]) with h | h
    · exact h
    · exfalso
      have h4 : v0 ∈ S' ⊓ LinearMap.ker E := by rw [h]; exact hv0S
      exact hv0 (LinearMap.mem_ker.mp (Submodule.mem_inf.mp h4).2)
  have himg : S'.map E = S := by
    rcases hirrp (S'.map E) (by
      rintro _ ⟨v, hv, rfl⟩; exact hE v hv) (by
      rintro B hB _ ⟨v, hv, rfl⟩
      obtain ⟨A, hA, hAB⟩ := hsurj B hB
      refine ⟨A v, hinvq A hA v hv, ?_⟩
      have h3 := LinearMap.congr_fun hAB v
      simpa only [LinearMap.comp_apply] using h3) with h | h
    · exfalso
      have h4 : E v0 ∈ S'.map E := ⟨v0, hv0S, rfl⟩
      rw [h, Submodule.mem_bot] at h4
      exact hv0 h4
    · exact h
  let E' : S' →ₗ[ℂ] S := E.restrict hE
  let Z' : S' →ₗ[ℂ] S := Z.restrict hZ
  have hbij : Function.Bijective E' := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have h1 : (x : Wq) ∈ S' ⊓ LinearMap.ker E := by
        refine Submodule.mem_inf.mpr ⟨x.2, ?_⟩
        rw [LinearMap.mem_ker]
        have h5 := congrArg Subtype.val hx
        simpa [E'] using h5
      rw [hker, Submodule.mem_bot] at h1
      exact Subtype.ext h1
    · rintro ⟨w, hw⟩
      rw [← himg] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨⟨v, hv⟩, rfl⟩
  let e := LinearEquiv.ofBijective E' hbij
  let T : Module.End ℂ S' := e.symm.toLinearMap ∘ₗ Z'
  have : Nontrivial S' := ⟨⟨⟨v0, hv0S⟩, 0, fun h => hv0 (by
    rw [show v0 = 0 from congrArg Subtype.val h, map_zero])⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hTx := hx.apply_eq_smul
  have hZx : Z x = c • E x := by
    have h1 : e (T x) = Z' x := by simp [T]
    rw [hTx, map_smul] at h1
    have h2 := congrArg Subtype.val h1
    simp [e, E', Z'] at h2
    exact h2.symm
  have hx0 : (x : Wq) ≠ 0 := fun h => hx.2 (Subtype.ext h)
  let K : Submodule ℂ Wq := S' ⊓ LinearMap.ker (Z - c • E)
  have hK : K = S' := by
    rcases hirrq K inf_le_left (by
      intro A hA v hv
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
      obtain ⟨B, hB1, hB2⟩ := hcomm A hA
      refine ⟨hinvq A hA v hv.1, ?_⟩
      have e1 := LinearMap.congr_fun hB1 v
      have e2 := LinearMap.congr_fun hB2 v
      simp only [LinearMap.comp_apply] at e1 e2
      have hv2 := hv.2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hv2 ⊢
      rw [e1, e2, hv2, map_smul]) with h | h
    · exfalso
      have h6 : (x : Wq) ∈ K := by
        refine Submodule.mem_inf.mpr ⟨x.2, ?_⟩
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
        exact hZx
      rw [h, Submodule.mem_bot] at h6
      exact hx0 h6
    · exact h
  refine ⟨c, fun v hv => ?_⟩
  have h7 : v ∈ K := by rw [hK]; exact hv
  have h8 := (Submodule.mem_inf.mp h7).2
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at h8
  exact h8
end Bl.general_b_fact_second_alt_form
