-- Prove2me | solution 1 for Bl.general_b_fact_tail.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:27.876301+00:00
-- url     : https://prove2.me/submissions/69cc77af-4da1-4938-be18-77637261ca00

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactTail_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open Bl Bl.general_b_fact_tail
namespace Bl.general_b_fact_tail
theorem _root_.solution :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [inst_1 : IsDomain.{u_1} R]
  [inst_2 : IsPrincipalIdealRing.{u_1} R] [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M]
  {ι : Type u_3} [inst_5 : Fintype.{u_3} ι] [DecidableEq.{u_3 + 1} ι] (b : Module.Basis.{u_3, u_1, u_2} ι R M)
  (N : Submodule.{u_1, u_2} R M)
  (h :
    Eq.{1} (Module.finrank.{u_1, u_2} R (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x))
      (Module.finrank.{u_1, u_2} R M))
  (e :
    LinearEquiv.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} R) M
      (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x)),
  Associated.{u_1}
    (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1} LinearMap.det.{u_2, u_1}
      (LinearMap.comp.{u_1, u_1, u_1, u_2, u_2, u_2} (Submodule.subtype.{u_1, u_2} N)
        (LinearEquiv.toLinearMap.{u_1, u_1, u_2, u_2} e)))
    (Finset.prod.{u_3, u_1} Finset.univ.{u_3} fun (i : ι) ↦ Submodule.smithNormalFormCoeffs.{u_3, u_1, u_2} b h i) := by
  intro R M _ _ _ _ _ ι _ _ b N h e
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let e' : M ≃ₗ[R] N := b'.equiv (Submodule.smithNormalFormBotBasis b h) (Equiv.refl _)
  refine (LinearMap.associated_det_comp_equiv N.subtype e e').trans (Associated.of_eq ?_)
  have h1 := Module.Basis.det_comp b' (N.subtype ∘ₗ (e' : M →ₗ[R] N)) b'
  rw [Module.Basis.det_self, mul_one] at h1
  rw [← h1]
  have h2 : (⇑(N.subtype ∘ₗ (e' : M →ₗ[R] N)) ∘ ⇑b') =
      fun i => Submodule.smithNormalFormCoeffs b h i • b' i := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, e',
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply]
    exact ab_eq i
  rw [h2, AlternatingMap.map_smul_univ, Module.Basis.det_self, smul_eq_mul, mul_one]
end Bl.general_b_fact_tail
