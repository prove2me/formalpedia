-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/549fa908-0103-5473-b8a5-8a1df781526c

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Theorems.Thm_Deformation_mem_wittHom_one_iff_coeff_mem_primitives
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map

set_option autoImplicit false

namespace KVPNat
open Function Deformation

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A : Type*) [CommRing A] [HopfAlgebra k A]

private theorem coeff_zero_add (x y : TruncatedWittVector p 1 A) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p 1 A x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p 1 A y
  rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.add_coeff_zero x y

omit [Fact p.Prime] [CommRing A] in

private theorem eq_mk_coeff_zero (x : TruncatedWittVector p 1 A) : x = TruncatedWittVector.mk p (fun _ => x.coeff 0) :=
  TruncatedWittVector.ext fun i => by
    rw [TruncatedWittVector.coeff_mk]
    congr 1
    exact Fin.ext (by omega)

private noncomputable def wittHomOneEquiv : wittHom k p 1 A ≃+ ↥(primitives k A) where
  toFun x := ⟨(x : TruncatedWittVector p 1 A).coeff 0, (mem_wittHom_one_iff_coeff_mem_primitives k p A x.1).1 x.2⟩
  invFun a := ⟨TruncatedWittVector.mk p (fun _ => (a : A)),
    (mem_wittHom_one_iff_coeff_mem_primitives k p A _).2 (by rw [TruncatedWittVector.coeff_mk]; exact a.2)⟩
  left_inv x := Subtype.ext (eq_mk_coeff_zero p A x.1).symm
  right_inv a := Subtype.ext (by
    change TruncatedWittVector.coeff (0 : Fin 1) (TruncatedWittVector.mk p fun _ => (a : A)) = a
    rw [TruncatedWittVector.coeff_mk])
  map_add' u v := Subtype.ext (coeff_zero_add p A u.1 v.1)

private theorem verschiebung_one_eq_zero (x : TruncatedWittVector p 1 A) : TruncWitt.verschiebung x = 0 :=
  TruncatedWittVector.ext fun i => by
    have hi : i = 0 := Fin.ext (by omega)
    subst hi
    rw [TruncWitt.coeff_verschiebung_zero]
    exact (TruncatedWittVector.coeff_zero p 1 A 0).symm

omit [CharP k p] in

private theorem verschiebung_of_one (x : wittHom k p 1 A) :
    DieudonneModule.verschiebung k p A (DieudonneModule.of k p A 1 x) = 0 := by
  rw [DieudonneModule.verschiebung_of]
  have : wittHomVerschiebung k p 1 A x = 0 := Subtype.ext (by rw [coe_wittHomVerschiebung]; exact verschiebung_one_eq_zero p A x.1)
  rw [this, map_zero]

private noncomputable def ofOne : wittHom k p 1 A →+ (DieudonneModule.verschiebung k p A).ker :=
  (DieudonneModule.of k p A 1).codRestrict _ fun x => by
    rw [AddMonoidHom.mem_ker]; exact verschiebung_of_one k p A x

omit [CharP k p] in
private theorem ofOne_injective : Injective (ofOne k p A) := fun _ _ h =>
  DieudonneModule.of_injective 1 (congrArg Subtype.val h)

private theorem eq_shiftLE_of_verschiebung_eq_zero {n : ℕ} (hn : 1 ≤ n) (x : TruncatedWittVector p n A)
    (hx : TruncWitt.verschiebung x = 0) :
    x = TruncWitt.shiftLE hn (TruncatedWittVector.mk p fun _ => x.coeff ⟨n - 1, by omega⟩) := by
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncWitt.coeff_shiftLE]
  split_ifs with hi
  · rw [TruncatedWittVector.coeff_mk]
    congr 1
    exact Fin.ext (by simp only; omega)
  ·
    have hi' : (i : ℕ) + 1 < n := by omega
    have h := TruncWitt.coeff_verschiebung_succ x i hi'
    rw [hx] at h
    have : (⟨(i : ℕ), Nat.lt_of_succ_lt hi'⟩ : Fin n) = i := Fin.ext rfl
    rw [this] at h
    rw [← h]
    exact TruncatedWittVector.coeff_zero p n A _

omit [CharP k p] in
private theorem ofOne_surjective : Surjective (ofOne k p A) := by
  rintro ⟨z, hz⟩
  rw [AddMonoidHom.mem_ker] at hz
  obtain ⟨n, x, rfl⟩ := DieudonneModule.exists_of z
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hx0 : x = 0 := Subtype.ext (TruncatedWittVector.ext fun i => i.elim0)
    subst hx0
    refine ⟨0, Subtype.ext ?_⟩
    change DieudonneModule.of k p A 1 0 = DieudonneModule.of k p A 0 0
    rw [map_zero, map_zero]
  · have hn1 : 1 ≤ n := hn

    rw [DieudonneModule.verschiebung_of] at hz
    have hVx : TruncWitt.verschiebung (x : TruncatedWittVector p n A) = 0 := by
      have h0 : wittHomVerschiebung k p n A x = 0 := DieudonneModule.of_injective n (by rw [hz, map_zero])
      have := congrArg Subtype.val h0
      rwa [coe_wittHomVerschiebung] at this

    set y : TruncatedWittVector p 1 A := TruncatedWittVector.mk p fun _ => (x : TruncatedWittVector p n A).coeff ⟨n - 1, by omega⟩ with hy_def
    have hxy : (x : TruncatedWittVector p n A) = TruncWitt.shiftLE hn1 y :=
      eq_shiftLE_of_verschiebung_eq_zero p A hn1 x.1 hVx
    have hy : y ∈ wittHom k p 1 A := (shiftLE_mem_wittHom_iff hn1 y).1 (hxy ▸ x.2)
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change DieudonneModule.of k p A 1 ⟨y, hy⟩ = DieudonneModule.of k p A n x
    rw [← DieudonneModule.of_shiftLE hn1 ⟨y, hy⟩]
    congr 1
    exact Subtype.ext (by rw [coe_wittHomShiftLE]; exact hxy.symm)

private noncomputable def kerEquivOne : (DieudonneModule.verschiebung k p A).ker ≃+ wittHom k p 1 A :=
  (AddEquiv.ofBijective (ofOne k p A) ⟨ofOne_injective k p A, ofOne_surjective k p A⟩).symm

end KVPNat

namespace KVPNat
open Function Deformation

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A : Type*) [CommRing A] [HopfAlgebra k A]

private noncomputable def kerEquivPrim : (DieudonneModule.verschiebung k p A).ker ≃+ ↥(primitives k A) :=
  (kerEquivOne k p A).trans (wittHomOneEquiv k p A)

omit [CharP k p] in
private theorem kerEquivOne_ofOne (x : wittHom k p 1 A) : kerEquivOne k p A (ofOne k p A x) = x := by
  apply (AddEquiv.ofBijective (ofOne k p A) ⟨ofOne_injective k p A, ofOne_surjective k p A⟩).injective
  rw [kerEquivOne, AddEquiv.apply_symm_apply]
  rfl

private theorem kerEquivPrim_of_one (x : wittHom k p 1 A)
    (hx : DieudonneModule.of k p A 1 x ∈ (DieudonneModule.verschiebung k p A).ker) :
    (kerEquivPrim k p A ⟨DieudonneModule.of k p A 1 x, hx⟩ : A) = (x : TruncatedWittVector p 1 A).coeff 0 := by
  have h : (⟨DieudonneModule.of k p A 1 x, hx⟩ : (DieudonneModule.verschiebung k p A).ker) = ofOne k p A x := rfl
  rw [h, kerEquivPrim, AddEquiv.trans_apply, kerEquivOne_ofOne]
  rfl

private theorem kerEquivPrim_map (ψ : A →ₐc[k] A) (z : (DieudonneModule.verschiebung k p A).ker)
    (hz : DieudonneModule.map k p ψ z ∈ (DieudonneModule.verschiebung k p A).ker) :
    (kerEquivPrim k p A ⟨DieudonneModule.map k p ψ z, hz⟩ : A) = ψ (kerEquivPrim k p A z : A) := by
  obtain ⟨y, hy⟩ := ofOne_surjective k p A z
  have hz1 : (z : DieudonneModule k p A) = DieudonneModule.of k p A 1 y := by rw [← hy]; rfl
  have hmap : DieudonneModule.map k p ψ z = DieudonneModule.of k p A 1 (wittHomMap p 1 ψ y) := by
    rw [hz1, DieudonneModule.map_of]
  have hmem : DieudonneModule.of k p A 1 (wittHomMap p 1 ψ y) ∈ (DieudonneModule.verschiebung k p A).ker := hmap ▸ hz
  have h1 : (⟨DieudonneModule.map k p ψ z, hz⟩ : (DieudonneModule.verschiebung k p A).ker) =
      ⟨DieudonneModule.of k p A 1 (wittHomMap p 1 ψ y), hmem⟩ := Subtype.ext hmap
  rw [h1, kerEquivPrim_of_one, coeff_wittHomMap, ← hy]
  congr 1
  exact (kerEquivPrim_of_one k p A y (ofOne k p A y).2).symm

end KVPNat

theorem solution
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type*) [CommRing A] [HopfAlgebra k A] :
    ∃ e : (Deformation.DieudonneModule.verschiebung k p A).ker ≃+ ↥(primitives k A),
      (∀ (x : Deformation.wittHom k p 1 A)
          (hx : Deformation.DieudonneModule.of k p A 1 x ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.of k p A 1 x, hx⟩ : A) = (x : TruncatedWittVector p 1 A).coeff 0) ∧
      ∀ (ψ : A →ₐc[k] A) (z : (Deformation.DieudonneModule.verschiebung k p A).ker)
        (hz : Deformation.DieudonneModule.map k p ψ z ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.map k p ψ z, hz⟩ : A) = ψ (e z : A) := by
  refine ⟨KVPNat.kerEquivPrim k p A, fun x hx => KVPNat.kerEquivPrim_of_one k p A x hx,
    fun ψ z hz => KVPNat.kerEquivPrim_map k p A ψ z hz⟩

end S_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map (solution)
