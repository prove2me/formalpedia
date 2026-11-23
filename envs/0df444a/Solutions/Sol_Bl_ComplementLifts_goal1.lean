-- Prove2me | solution 1 for Bl.ComplementLifts.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:05.308445+00:00
-- url     : https://prove2.me/submissions/ad3578d0-1e61-4d49-a625-05602d13efeb

import Mathlib
import Definitions.Def_Lemmata_ComplementLifts_ComplLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1 u_2
namespace Bl.ComplementLifts
private lemma compl_lift {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N N' : Submodule R M) (hN : IsCompl N N') (A B : Submodule R N) (hAB : IsCompl A B) :
    IsCompl (A.map N.subtype) (B.map N.subtype ⊔ N') := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxA hxB
    obtain ⟨y, hy, n', hn', rfl⟩ := Submodule.mem_sup.1 hxB
    obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 hxA
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hy
    simp only [Submodule.subtype_apply] at hax ⊢
    have hn'N : n' ∈ N := by
      have : n' = (a : M) - (b : M) := by
        rw [hax]; abel
      rw [this]; exact N.sub_mem a.2 b.2
    have hn0 : n' = 0 := (Submodule.disjoint_def.1 hN.disjoint) n' hn'N hn'
    rw [hn0, add_zero] at hax ⊢
    have hab : a = b := Subtype.ext hax
    have h0 : b = 0 := (Submodule.disjoint_def.1 hAB.disjoint) b (hab ▸ ha) hb
    simp [h0]
  · rw [codisjoint_iff, ← sup_assoc, ← Submodule.map_sup, hAB.sup_eq_top, Submodule.map_top,
      Submodule.range_subtype, hN.sup_eq_top]
end Bl.ComplementLifts
end

set_option autoImplicit false
universe u_1 u_2
open Bl Bl.ComplementLifts
namespace Bl.ComplementLifts
theorem _root_.solution :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [IsDomain.{u_1} R] [IsPrincipalIdealRing.{u_1} R]
  [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M] (N N' S : Submodule.{u_1, u_2} R M),
  IsCompl.{u_2} N N' →
    ∀ [Module.Finite.{u_1, u_2} R (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x)],
      LE.le.{u_2} S N →
        (∀ (a : R) (x : M),
            Ne.{u_1 + 1} a 0 →
              Membership.mem.{u_2, u_2} S (HSMul.hSMul.{u_1, u_2, u_2} a x) → Membership.mem.{u_2, u_2} S x) →
          Exists.{u_2 + 1} fun (T : Submodule.{u_1, u_2} R M) ↦ IsCompl.{u_2} S T := by
  intro R M _ _ _ _ _ N N' S hN _ hSN hsat
  let S' : Submodule R N := S.comap N.subtype
  have : Module.IsTorsionFree R (N ⧸ S') := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective S' q
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [S', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul] at hq ⊢
      exact hsat r x hr hq
  obtain ⟨h, hh⟩ := LinearMap.exists_rightInverse_of_surjective S'.mkQ (Submodule.range_mkQ S')
  have hidem : IsIdempotentElem (h ∘ₗ S'.mkQ) :=
    LinearMap.ext fun x => congrArg h (LinearMap.congr_fun hh (S'.mkQ x))
  have hker : LinearMap.ker (h ∘ₗ S'.mkQ) = S' := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hx
      have := congrArg S'.mkQ hx
      rw [← LinearMap.comp_apply S'.mkQ h, hh, LinearMap.id_apply, map_zero] at this
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    · intro hx
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S').2 hx, map_zero]
  have hc : IsCompl S' (LinearMap.range (h ∘ₗ S'.mkQ)) := by
    have := LinearMap.IsIdempotentElem.isCompl hidem
    rw [hker] at this
    exact this.symm
  have hS : S'.map N.subtype = S := by
    simp only [S', Submodule.map_comap_subtype]
    exact inf_eq_right.2 hSN
  refine ⟨(LinearMap.range (h ∘ₗ S'.mkQ)).map N.subtype ⊔ N', ?_⟩
  have := compl_lift N N' hN S' _ hc
  rwa [hS] at this
end Bl.ComplementLifts
