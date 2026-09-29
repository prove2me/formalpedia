-- Prove2me | solution 1 for CommGroup.index_range_powMonoidHom_eq_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/26050664-424e-541e-97b9-e663b6d5de02

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CommGroup_index_range_powMonoidHom_eq_pow_finrank

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution {F : Type*} [CommGroup F] [Group.FG F]
    (htf : ∀ (x : F) (m : ℕ), 0 < m → x ^ m = 1 → x = 1) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : F →* F).range.index = n ^ Module.finrank ℤ (Additive F) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Module.Finite ℤ (Additive F) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  haveI : NoZeroSMulDivisors ℤ (Additive F) := by
    refine ⟨fun {c x} h => ?_⟩
    by_contra hne
    rcases not_or.1 hne with ⟨hc, hx⟩
    apply hx
    have h' : (c.natAbs : ℤ) • x = 0 := by
      rcases Int.natAbs_eq c with hc' | hc'
      · rwa [← hc']
      · rw [show (c.natAbs : ℤ) = -c by omega, neg_smul, h, neg_zero]
    rw [natCast_zsmul] at h'
    have h2 := htf (Additive.toMul x) c.natAbs (Int.natAbs_pos.2 hc) (by rw [← toMul_nsmul, h']; rfl)
    exact Additive.toMul.injective (by rw [h2]; rfl)
  haveI : Module.Free ℤ (Additive F) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ (Additive F)
  let e := b.equivFun
  let ψ : Additive F →+ (Fin (Module.finrank ℤ (Additive F)) → ZMod n) :=
    ((Int.castAddHom (ZMod n)).compLeft (Fin (Module.finrank ℤ (Additive F)))).comp e.toLinearMap.toAddMonoidHom
  have hψ : ∀ x i, ψ x i = ((e x i : ℤ) : ZMod n) := fun x i => rfl
  have hsurj : Function.Surjective ψ := by
    intro t
    refine ⟨e.symm (fun i => ((t i).val : ℤ)), ?_⟩
    funext i
    rw [hψ, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hker : Subgroup.toAddSubgroup ((powMonoidHom n : F →* F).range) = ψ.ker := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rw [AddMonoidHom.mem_ker]
      have hx : x = n • Additive.ofMul y := by
        rw [← ofMul_pow, ← powMonoidHom_apply, hy]; rfl
      funext i
      rw [hψ, hx, map_nsmul, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
        zero_mul, Pi.zero_apply]
    · intro hx
      rw [AddMonoidHom.mem_ker] at hx
      have hdiv : ∀ i, (n : ℤ) ∣ e x i := fun i => by
        have h := congrFun hx i
        rw [hψ, Pi.zero_apply] at h
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
      choose c hc using hdiv
      refine ⟨Additive.toMul (e.symm c), ?_⟩
      rw [powMonoidHom_apply, ← toMul_nsmul]
      congr 1
      apply e.injective
      rw [map_nsmul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, nsmul_eq_mul, hc i]
  rw [← Subgroup.index_toAddSubgroup, hker, ← AddMonoidHom.comap_bot, AddSubgroup.index_comap_of_surjective _ hsurj,
    AddSubgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end S_CommGroup_index_range_powMonoidHom_eq_pow_finrank
end P2MW
export P2MW.S_CommGroup_index_range_powMonoidHom_eq_pow_finrank (solution)
