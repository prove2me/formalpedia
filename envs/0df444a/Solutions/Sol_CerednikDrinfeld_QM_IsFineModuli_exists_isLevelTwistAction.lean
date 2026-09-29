-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_isLevelTwistAction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e90f9dc9-98ad-5a96-81fa-18f503e95b5e

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKcLevelTwistAction

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

def orderSubring (hΛ : IsOrder Λ) : Subring ℍ[ℚ, a, b] where
  carrier := Λ
  mul_mem' hx hy := hΛ.mul_mem hx hy
  one_mem' := hΛ.one_mem
  add_mem' hx hy := Λ.add_mem hx hy
  zero_mem' := Λ.zero_mem
  neg_mem' hx := Λ.neg_mem hx

@[scoped simp] theorem mem_orderSubring (hΛ : IsOrder Λ) (x : ℍ[ℚ, a, b]) : x ∈ orderSubring hΛ ↔ x ∈ Λ := Iff.rfl

def Cong (Λ : Submodule ℤ ℍ[ℚ, a, b]) (m : ℕ) (x y : ℍ[ℚ, a, b]) : Prop :=
  ∃ z : ↥Λ, x - y = (m : ℚ) • (z : ℍ[ℚ, a, b])

theorem Cong.refl (m : ℕ) (x : ℍ[ℚ, a, b]) : Cong Λ m x x := ⟨0, by simp⟩

theorem Cong.symm {m : ℕ} {x y : ℍ[ℚ, a, b]} (h : Cong Λ m x y) : Cong Λ m y x := by
  obtain ⟨z, hz⟩ := h
  exact ⟨-z, by rw [Submodule.coe_neg, smul_neg, ← hz]; abel⟩

theorem Cong.trans {m : ℕ} {x y w : ℍ[ℚ, a, b]} (h : Cong Λ m x y) (h' : Cong Λ m y w) : Cong Λ m x w := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := h'
  exact ⟨z + z', by rw [Submodule.coe_add, smul_add, ← hz, ← hz']; abel⟩

theorem Cong.add {m : ℕ} {x y x' y' : ℍ[ℚ, a, b]} (h : Cong Λ m x y) (h' : Cong Λ m x' y') :
    Cong Λ m (x + x') (y + y') := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := h'
  exact ⟨z + z', by rw [Submodule.coe_add, smul_add, ← hz, ← hz']; abel⟩

theorem Cong.mul (hΛ : IsOrder Λ) {m : ℕ} {x y x' y' : ℍ[ℚ, a, b]} (hy : y ∈ Λ) (hx' : x' ∈ Λ)
    (h : Cong Λ m x y) (h' : Cong Λ m x' y') :
    Cong Λ m (x * x') (y * y') := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := h'
  refine ⟨⟨(z : ℍ[ℚ, a, b]) * x' + y * (z' : ℍ[ℚ, a, b]), Λ.add_mem (hΛ.mul_mem z.2 hx') (hΛ.mul_mem hy z'.2)⟩, ?_⟩
  have : x * x' - y * y' = (x - y) * x' + y * (x' - y') := by noncomm_ring
  rw [this, hz, hz']
  simp only [smul_add, smul_mul_assoc, mul_smul_comm]

def congr (hΛ : IsOrder Λ) (m : ℕ) : RingCon ↥(orderSubring hΛ) where
  r x y := Cong Λ m (x : ℍ[ℚ, a, b]) (y : ℍ[ℚ, a, b])
  iseqv := ⟨fun x => Cong.refl m (x : ℍ[ℚ, a, b]), fun h => h.symm, fun h h' => h.trans h'⟩
  mul' {w x y z} h h' := by
    show Cong Λ m ((w : ℍ[ℚ, a, b]) * y) ((x : ℍ[ℚ, a, b]) * z)
    exact Cong.mul hΛ x.2 y.2 h h'
  add' {w x y z} h h' := by
    show Cong Λ m ((w : ℍ[ℚ, a, b]) + y) ((x : ℍ[ℚ, a, b]) + z)
    exact Cong.add h h'

abbrev Qring (hΛ : IsOrder Λ) (m : ℕ) : Type := (congr hΛ m).Quotient

theorem congr_eq_iff (hΛ : IsOrder Λ) (m : ℕ) (x y : ↥(orderSubring hΛ)) :
    ((x : Qring hΛ m) = (y : Qring hΛ m)) ↔ Cong Λ m (x : ℍ[ℚ, a, b]) (y : ℍ[ℚ, a, b]) :=
  RingCon.eq _

theorem moduleFinite_orderSubring (hΛ : IsOrder Λ) : Module.Finite ℤ ↥(orderSubring hΛ) := by
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg
  let e : ↥Λ →ₗ[ℤ] ↥(orderSubring hΛ) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun n x => by
        apply Subtype.ext
        show ((n • x : ↥Λ) : ℍ[ℚ, a, b]) = n • (x : ℍ[ℚ, a, b])
        rw [Submodule.coe_smul] }
  exact Module.Finite.of_surjective e fun y => ⟨⟨y.1, y.2⟩, rfl⟩

theorem finite_Qring (hΛ : IsOrder Λ) (m : ℕ) [NeZero m] : Finite (Qring hΛ m) := by
  haveI := moduleFinite_orderSubring hΛ
  let π : ↥(orderSubring hΛ) →ₗ[ℤ] Qring hΛ m := ((congr hΛ m).mk' : _ →+* _).toAddMonoidHom.toIntLinearMap
  haveI : Module.Finite ℤ (Qring hΛ m) :=
    Module.Finite.of_surjective π (RingCon.mk'_surjective _)
  refine Module.finite_of_fg_torsion (Qring hΛ m) ?_
  intro q
  refine ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (NeZero.ne m))⟩, ?_⟩
  obtain ⟨x, rfl⟩ := RingCon.mk'_surjective (congr hΛ m) q
  show (m : ℤ) • ((congr hΛ m).mk' x) = 0
  rw [zsmul_eq_mul, show ((m : ℤ) : Qring hΛ m) = (congr hΛ m).mk' (m : ℤ) by simp, ← map_mul, ← map_zero (congr hΛ m).mk']
  show ((((m : ℤ) : ↥(orderSubring hΛ)) * x : ↥(orderSubring hΛ)) : Qring hΛ m) = ((0 : ↥(orderSubring hΛ)) : Qring hΛ m)
  rw [congr_eq_iff]
  refine ⟨⟨x.1, x.2⟩, ?_⟩
  simp only [ZeroMemClass.coe_zero, sub_zero, Subring.coe_mul, Subring.coe_intCast]
  rw [Int.cast_natCast, Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul]

abbrev G (hΛ : IsOrder Λ) (m : ℕ) : Type := (Qring hΛ m)ˣ

theorem finite_G (hΛ : IsOrder Λ) (m : ℕ) [NeZero m] : Finite (G hΛ m) := by
  haveI := finite_Qring hΛ m
  infer_instance

noncomputable def lift (hΛ : IsOrder Λ) (m : ℕ) (q : Qring hΛ m) : ↥(orderSubring hΛ) :=
  Classical.choose (RingCon.mk'_surjective (congr hΛ m) q)

theorem mk'_lift (hΛ : IsOrder Λ) (m : ℕ) (q : Qring hΛ m) : (congr hΛ m).mk' (lift hΛ m q) = q :=
  Classical.choose_spec (RingCon.mk'_surjective (congr hΛ m) q)

theorem coe_lift (hΛ : IsOrder Λ) (m : ℕ) (q : Qring hΛ m) : ((lift hΛ m q : ↥(orderSubring hΛ)) : Qring hΛ m) = q :=
  mk'_lift hΛ m q

noncomputable def chi (hΛ : IsOrder Λ) (m : ℕ) (g : G hΛ m) : ↥Λ :=
  ⟨(lift hΛ m (g : Qring hΛ m) : ℍ[ℚ, a, b]), (lift hΛ m (g : Qring hΛ m)).2⟩

theorem coe_chi (hΛ : IsOrder Λ) (m : ℕ) (g : G hΛ m) :
    (chi hΛ m g : ℍ[ℚ, a, b]) = (lift hΛ m (g : Qring hΛ m) : ℍ[ℚ, a, b]) := rfl

theorem chi_eq_lift (hΛ : IsOrder Λ) (m : ℕ) (g : G hΛ m) :
    (⟨(chi hΛ m g : ℍ[ℚ, a, b]), (chi hΛ m g).2⟩ : ↥(orderSubring hΛ)) = lift hΛ m (g : Qring hΛ m) := rfl

theorem label_one (hΛ : IsOrder Λ) (m : ℕ) : Cong Λ m (chi hΛ m 1 : ℍ[ℚ, a, b]) 1 := by
  have h : ((lift hΛ m ((1 : G hΛ m) : Qring hΛ m) : ↥(orderSubring hΛ)) : Qring hΛ m) =
      ((1 : ↥(orderSubring hΛ)) : Qring hΛ m) := by
    rw [coe_lift]; rfl
  exact (congr_eq_iff hΛ m _ _).mp h

theorem label_mul (hΛ : IsOrder Λ) (m : ℕ) (g g' : G hΛ m) :
    Cong Λ m (chi hΛ m (g * g') : ℍ[ℚ, a, b]) ((chi hΛ m g : ℍ[ℚ, a, b]) * (chi hΛ m g' : ℍ[ℚ, a, b])) := by
  have h : ((lift hΛ m ((g * g' : G hΛ m) : Qring hΛ m) : ↥(orderSubring hΛ)) : Qring hΛ m) =
      ((lift hΛ m (g : Qring hΛ m) * lift hΛ m (g' : Qring hΛ m) : ↥(orderSubring hΛ)) : Qring hΛ m) := by
    rw [coe_lift, Units.val_mul, RingCon.coe_mul, coe_lift, coe_lift]
  exact (congr_eq_iff hΛ m _ _).mp h

theorem label_injective (hΛ : IsOrder Λ) (m : ℕ) (g g' : G hΛ m)
    (h : Cong Λ m (chi hΛ m g : ℍ[ℚ, a, b]) (chi hΛ m g' : ℍ[ℚ, a, b])) : g = g' := by
  apply Units.ext
  rw [← coe_lift hΛ m (g : Qring hΛ m), ← coe_lift hΛ m (g' : Qring hΛ m), congr_eq_iff]
  exact h

theorem label_surjective (hΛ : IsOrder Λ) (m : ℕ) (c d : ↥Λ)
    (hcd : Cong Λ m ((c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b])) 1)
    (hdc : Cong Λ m ((d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b])) 1) :
    ∃ g : G hΛ m, Cong Λ m (chi hΛ m g : ℍ[ℚ, a, b]) (c : ℍ[ℚ, a, b]) := by
  let c' : ↥(orderSubring hΛ) := ⟨c.1, c.2⟩
  let d' : ↥(orderSubring hΛ) := ⟨d.1, d.2⟩
  have h1 : ((c' * d' : ↥(orderSubring hΛ)) : Qring hΛ m) = ((1 : ↥(orderSubring hΛ)) : Qring hΛ m) :=
    (congr_eq_iff hΛ m _ _).mpr hcd
  have h2 : ((d' * c' : ↥(orderSubring hΛ)) : Qring hΛ m) = ((1 : ↥(orderSubring hΛ)) : Qring hΛ m) :=
    (congr_eq_iff hΛ m _ _).mpr hdc
  let g : G hΛ m :=
    { val := (c' : Qring hΛ m)
      inv := (d' : Qring hΛ m)
      val_inv := by rw [← RingCon.coe_mul, h1]; rfl
      inv_val := by rw [← RingCon.coe_mul, h2]; rfl }
  refine ⟨g, ?_⟩
  have h : ((lift hΛ m (g : Qring hΛ m) : ↥(orderSubring hΛ)) : Qring hΛ m) = (c' : Qring hΛ m) := coe_lift hΛ m _
  exact (congr_eq_iff hΛ m _ _).mp h

section Points

variable {N : ℕ} {S : Type u} [CommRing S]

theorem pushPt_act_one (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt (E.act x) (E.act_over x) (E.L.one t) = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_hom x t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  exact mul_left_cancel (a := pushPt (E.act x) (E.act_over x) (E.L.one t)) (h.symm.trans (mul_one _).symm)

theorem pushPt_act_zero (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f) :
    pushPt (E.act 0) (E.act_over 0) Q = E.L.one t := by
  letI := E.L.pointGroup t
  have h := E.act_add 0 0 t Q
  rw [add_zero] at h

  exact mul_left_cancel (a := pushPt (E.act 0) (E.act_over 0) Q) (h.symm.trans (mul_one _).symm)

theorem pushPt_act_pushPt_act (E : FakeEllipticCurve Λ N S) (x c : ↥Λ)
    (h : (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (pushPt (E.act c) (E.act_over c) Q) =
      pushPt (E.act ⟨(x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]), h⟩) (E.act_over _) Q := by
  apply Subtype.ext
  simp only [pushPt, mapPt_coe, E.act_mul x c h, Category.assoc]

theorem coe_rat_eq_smul_one (q : ℚ) : ((q : ℚ) : ℍ[ℚ, a, b]) = q • (1 : ℍ[ℚ, a, b]) := by
  ext <;> simp

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [coe_rat_eq_smul_one, show ((n : ℚ) • (1 : ℍ[ℚ, a, b])) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) by
    rw [← Int.cast_smul_eq_zsmul ℚ]; simp]
  exact Λ.smul_mem _ hΛ.one_mem

theorem pushPt_act_natCast (hΛ : IsOrder Λ) (E : FakeEllipticCurve Λ N S) (n : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩) (E.act_over _) Q = nsmulPt E.L t n Q := by
  induction n with
  | zero =>
      have h0 : (⟨((0 : ℕ) : ℚ), natCast_mem hΛ 0⟩ : ↥Λ) = 0 := Subtype.ext (by simp)
      rw [h0]
      exact pushPt_act_zero E t Q
  | succ n ih =>
      have hsplit : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
          ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ :=
        Subtype.ext (by push_cast; rfl)
      have h1 : pushPt (E.act ⟨1, hΛ.one_mem⟩) (E.act_over _) Q = Q :=
        Subtype.ext (by simp only [pushPt, mapPt_coe, E.act_one hΛ.one_mem, Category.comp_id])
      rw [hsplit, E.act_add, ih, h1]
      rfl

theorem pushPt_act_eq_of_cong (hΛ : IsOrder Λ) {m : ℕ} (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (c c' : ↥Λ) (h : Cong Λ m (c : ℍ[ℚ, a, b]) (c' : ℍ[ℚ, a, b])) :
    pushPt (E.act c) (E.act_over c) P.P = pushPt (E.act c') (E.act_over c') P.P := by
  obtain ⟨z, hz⟩ := h
  letI := E.L.pointGroup (𝟙 (Spec (CommRingCat.of S)))
  have hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := natCast_mem hΛ m
  have hzm : (z : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hΛ.mul_mem z.2 hm

  have hc : c = c' + ⟨(z : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]), hzm⟩ := by
    apply Subtype.ext
    show (c : ℍ[ℚ, a, b]) = (c' : ℍ[ℚ, a, b]) + (z : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b])
    rw [coe_rat_eq_smul_one, mul_smul_comm, mul_one, ← hz]
    abel

  have hzero : pushPt (E.act ⟨(z : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]), hzm⟩) (E.act_over _) P.P =
      E.L.one (𝟙 (Spec (CommRingCat.of S))) := by
    rw [← pushPt_act_pushPt_act E z ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ hzm, pushPt_act_natCast hΛ E m, P.torsion,
      pushPt_act_one]
  rw [hc, E.act_add, hzero, E.L.mul_one]

def IsUnitMod (Λ : Submodule ℤ ℍ[ℚ, a, b]) (m : ℕ) (c : ↥Λ) : Prop :=
  ∃ d : ↥Λ, Cong Λ m ((c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b])) 1 ∧ Cong Λ m ((d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b])) 1

theorem isUnitMod_one (hΛ : IsOrder Λ) (m : ℕ) : IsUnitMod Λ m ⟨1, hΛ.one_mem⟩ :=
  ⟨⟨1, hΛ.one_mem⟩, by simpa using Cong.refl m (1 : ℍ[ℚ, a, b]), by simpa using Cong.refl m (1 : ℍ[ℚ, a, b])⟩

theorem IsUnitMod.mul (hΛ : IsOrder Λ) {m : ℕ} {c c' : ↥Λ} (hc : IsUnitMod Λ m c) (hc' : IsUnitMod Λ m c') :
    IsUnitMod Λ m ⟨(c : ℍ[ℚ, a, b]) * (c' : ℍ[ℚ, a, b]), hΛ.mul_mem c.2 c'.2⟩ := by
  obtain ⟨d, hcd, hdc⟩ := hc
  obtain ⟨d', hcd', hdc'⟩ := hc'
  refine ⟨⟨(d' : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]), hΛ.mul_mem d'.2 d.2⟩, ?_, ?_⟩
  ·
    have h1 : Cong Λ m ((c : ℍ[ℚ, a, b]) * ((c' : ℍ[ℚ, a, b]) * (d' : ℍ[ℚ, a, b])) * (d : ℍ[ℚ, a, b]))
        ((c : ℍ[ℚ, a, b]) * 1 * (d : ℍ[ℚ, a, b])) :=
      Cong.mul hΛ (hΛ.mul_mem c.2 hΛ.one_mem) d.2 (Cong.mul hΛ c.2 (hΛ.mul_mem c'.2 d'.2) (Cong.refl m _) hcd')
        (Cong.refl m _)
    rw [mul_one] at h1
    have : (c : ℍ[ℚ, a, b]) * (c' : ℍ[ℚ, a, b]) * ((d' : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b])) =
        (c : ℍ[ℚ, a, b]) * ((c' : ℍ[ℚ, a, b]) * (d' : ℍ[ℚ, a, b])) * (d : ℍ[ℚ, a, b]) := by noncomm_ring
    rw [Submodule.coe_mk, this]
    exact h1.trans hcd
  · have h1 : Cong Λ m ((d' : ℍ[ℚ, a, b]) * ((d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b])) * (c' : ℍ[ℚ, a, b]))
        ((d' : ℍ[ℚ, a, b]) * 1 * (c' : ℍ[ℚ, a, b])) :=
      Cong.mul hΛ (hΛ.mul_mem d'.2 hΛ.one_mem) c'.2 (Cong.mul hΛ d'.2 (hΛ.mul_mem d.2 c.2) (Cong.refl m _) hdc)
        (Cong.refl m _)
    rw [mul_one] at h1
    have : (d' : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) * ((c : ℍ[ℚ, a, b]) * (c' : ℍ[ℚ, a, b])) =
        (d' : ℍ[ℚ, a, b]) * ((d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b])) * (c' : ℍ[ℚ, a, b]) := by noncomm_ring
    rw [Submodule.coe_mk, this]
    exact h1.trans hdc'

theorem IsUnitMod.of_cong {m : ℕ} {c c' : ↥Λ} (hΛ : IsOrder Λ) (hc : IsUnitMod Λ m c)
    (h : Cong Λ m (c : ℍ[ℚ, a, b]) (c' : ℍ[ℚ, a, b])) : IsUnitMod Λ m c' := by
  obtain ⟨d, hcd, hdc⟩ := hc
  refine ⟨d, ?_, ?_⟩
  · exact (Cong.mul hΛ c'.2 d.2 h (Cong.refl m _)).symm.trans hcd
  · exact (Cong.mul hΛ d.2 c.2 (Cong.refl m _) h).symm.trans hdc

theorem isUnitMod_chi (hΛ : IsOrder Λ) (m : ℕ) (g : G hΛ m) : IsUnitMod Λ m (chi hΛ m g) := by
  refine ⟨chi hΛ m g⁻¹, ?_, ?_⟩
  · have := (label_mul hΛ m g g⁻¹).symm
    rw [mul_inv_cancel] at this
    exact this.trans (label_one hΛ m)
  · have := (label_mul hΛ m g⁻¹ g).symm
    rw [inv_mul_cancel] at this
    exact this.trans (label_one hΛ m)

variable (hΛ : IsOrder Λ) {m : ℕ}

noncomputable def twist (c : ↥Λ) (hc : IsUnitMod Λ m c) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    FakeEllipticCurve.WithFullLevel Λ N m S :=
  ⟨u.1, Classical.choose
    (CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
      hΛ u.1 u.2 c hc.choose hc.choose_spec.1 hc.choose_spec.2)⟩

@[scoped simp] theorem twist_fst (c : ↥Λ) (hc : IsUnitMod Λ m c) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    (twist hΛ c hc u).1 = u.1 := rfl

theorem twist_P (c : ↥Λ) (hc : IsUnitMod Λ m c) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    (twist hΛ c hc u).2.P = pushPt (u.1.act c) (u.1.act_over c) u.2.P :=
  (Classical.choose_spec
    (CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
      hΛ u.1 u.2 c hc.choose hc.choose_spec.1 hc.choose_spec.2)).1

theorem isTwist_twist (c : ↥Λ) (hc : IsUnitMod Λ m c) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    FakeEllipticCurve.WithFullLevel.IsTwist c u (twist hΛ c hc u) :=
  (Classical.choose_spec
    (CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
      hΛ u.1 u.2 c hc.choose hc.choose_spec.1 hc.choose_spec.2)).2

theorem iso_of_P_eq (E : FakeEllipticCurve Λ N S) (P P' : E.FullLevel m) (h : P.P = P'.P) :
    FakeEllipticCurve.WithFullLevel.Iso (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) ⟨E, P'⟩ := by
  refine ⟨Iso.refl E.A, Category.id_comp E.f, ?_, ?_, ?_, ?_⟩
  · intro T t Q R
    have hQ : ∀ X : SchemeHomOver t E.f, mapPt (Iso.refl E.A).hom (Category.id_comp E.f) X = X :=
      fun X => Subtype.ext (Category.comp_id X.1)
    rw [hQ, hQ, hQ]
  · intro x
    show E.act x ≫ 𝟙 E.A = 𝟙 E.A ≫ E.act x
    rw [Category.comp_id, Category.id_comp]
  · intro T t Q
    have hQ : mapPt (Iso.refl E.A).hom (Category.id_comp E.f) Q = Q := Subtype.ext (Category.comp_id Q.1)
    rw [hQ]
  · exact (Subtype.ext (Category.comp_id _)).trans h

theorem iso_twist_of_cong (c c' : ↥Λ) (hc : IsUnitMod Λ m c) (hc' : IsUnitMod Λ m c')
    (h : Cong Λ m (c : ℍ[ℚ, a, b]) (c' : ℍ[ℚ, a, b])) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    FakeEllipticCurve.WithFullLevel.Iso (twist hΛ c hc u) (twist hΛ c' hc' u) :=
  iso_of_P_eq u.1 (twist hΛ c hc u).2 (twist hΛ c' hc' u).2
    (by rw [twist_P, twist_P, pushPt_act_eq_of_cong hΛ u.1 u.2 c c' h])

theorem iso_twist_one (h1 : IsUnitMod Λ m ⟨1, hΛ.one_mem⟩) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    FakeEllipticCurve.WithFullLevel.Iso (twist hΛ ⟨1, hΛ.one_mem⟩ h1 u) u :=
  iso_of_P_eq u.1 (twist hΛ ⟨1, hΛ.one_mem⟩ h1 u).2 u.2
    (by
      rw [twist_P]
      exact Subtype.ext (by simp only [pushPt, mapPt_coe, u.1.act_one hΛ.one_mem, Category.comp_id]))

theorem iso_twist_twist (c c' : ↥Λ) (hc : IsUnitMod Λ m c) (hc' : IsUnitMod Λ m c')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    FakeEllipticCurve.WithFullLevel.Iso (twist hΛ c hc (twist hΛ c' hc' u))
      (twist hΛ ⟨(c : ℍ[ℚ, a, b]) * (c' : ℍ[ℚ, a, b]), hΛ.mul_mem c.2 c'.2⟩ (hc.mul hΛ hc') u) :=
  iso_of_P_eq u.1 (twist hΛ c hc (twist hΛ c' hc' u)).2 (twist hΛ _ (hc.mul hΛ hc') u).2
    (by
      rw [twist_P, twist_P, twist_P]
      exact pushPt_act_pushPt_act u.1 c c' (hΛ.mul_mem c.2 c'.2) u.2.P)

theorem iso_twist_of_isTwist (c : ↥Λ) (hc : IsUnitMod Λ m c) (u u' : FakeEllipticCurve.WithFullLevel Λ N m S)
    (h : FakeEllipticCurve.WithFullLevel.IsTwist c u u') :
    FakeEllipticCurve.WithFullLevel.Iso (twist hΛ c hc u) u' := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  refine ⟨e, he, hmul, hact, hlev, ?_⟩
  show mapPt e.hom he (twist hΛ c hc u).2.P = u'.2.P
  rw [twist_P]
  exact hP

theorem twist_P_val (c : ↥Λ) (hc : IsUnitMod Λ m c) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    (FakeEllipticCurve.FullLevel.P (E := u.1) (twist hΛ c hc u).2).1 = (u.2.P).1 ≫ u.1.act c :=
  congrArg Subtype.val (twist_P hΛ c hc u)

theorem iso_twist_of_iso (c : ↥Λ) (hc : IsUnitMod Λ m c) (u u' : FakeEllipticCurve.WithFullLevel Λ N m S)
    (h : FakeEllipticCurve.WithFullLevel.Iso u u') :
    FakeEllipticCurve.WithFullLevel.Iso (twist hΛ c hc u) (twist hΛ c hc u') := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  refine ⟨e, he, hmul, hact, hlev, ?_⟩
  apply Subtype.ext
  dsimp only [twist_fst, mapPt_coe]
  rw [twist_P_val, twist_P_val, Category.assoc, hact c, ← Category.assoc, ← mapPt_coe e.hom he, hP]

theorem isPullback_twist {S' : Type u} [CommRing S'] (φ : S →+* S') (c : ↥Λ) (hc : IsUnitMod Λ m c)
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') :
    FakeEllipticCurve.WithFullLevel.IsPullback φ (twist hΛ c hc u) (twist hΛ c hc u') := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := h
  refine ⟨g, hg, hmul, hact, hlev, ?_⟩
  dsimp only [twist_fst]
  rw [twist_P_val, twist_P_val, Category.assoc, hact c, ← Category.assoc, hP, Category.assoc]

end Points

section Yoneda

variable {N m : ℕ} {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
  (hM : IsFineModuli Λ N m M πM ptF)
  {T : Scheme.{0}} (πT : T ⟶ Spec (CommRingCat.of 𝒪))
  (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πT)
  (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S),
    FakeEllipticCurve.WithFullLevel.Iso u u' → pt' S s u = pt' S s u')
  (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S'),
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1)

include hM hiso hpb in

theorem comp_pt'_eq_of_comp_ptF_eq {R R' C : Type} [CommRing R] [CommRing R'] [CommRing C]
    (sR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪)) (sR' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) (v : FakeEllipticCurve.WithFullLevel Λ N m R')
    (α : R →+* C) (β : R' →+* C)
    (hs : Spec.map (CommRingCat.ofHom α) ≫ sR = Spec.map (CommRingCat.ofHom β) ≫ sR')
    (h : Spec.map (CommRingCat.ofHom α) ≫ (ptF R sR u).1 = Spec.map (CommRingCat.ofHom β) ≫ (ptF R' sR' v).1) :
    Spec.map (CommRingCat.ofHom α) ≫ (pt' R sR u).1 = Spec.map (CommRingCat.ofHom β) ≫ (pt' R' sR' v).1 := by
  obtain ⟨u', hu'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback α u
  obtain ⟨v', hv'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback β v
  let sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪) := Spec.map (CommRingCat.ofHom α) ≫ sR
  have h1 := hM.ptF_pullback R C α sR sC rfl u u' hu'
  have h2 := hM.ptF_pullback R' C β sR' sC hs.symm v v' hv'
  have h12 : ptF C sC u' = ptF C sC v' := Subtype.ext (by rw [h1, h2, h])
  have hI : FakeEllipticCurve.WithFullLevel.Iso u' v' := hM.ptF_injective C sC u' v' h12
  have h3 := hpb R C α sR sC rfl u u' hu'
  have h4 := hpb R' C β sR' sC hs.symm v v' hv'
  rw [← h3, ← h4, hiso C sC _ _ hI]

include hM hiso hpb in

theorem existsUnique_hom_pt'_eq :
    ∃! Φ : M ⟶ T, Φ ≫ πT = πM ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N m S), (pt' S s u).1 = (ptF S s u).1 ≫ Φ := by
  classical

  let A : M.affineCover.I₀ → CommRingCat.{0} := fun j => M.affineOpenCover.X j
  let ι : ∀ j, Spec (CommRingCat.of (A j)) ⟶ M := fun j => M.affineCover.f j
  let s : ∀ j, Spec (CommRingCat.of (A j)) ⟶ Spec (CommRingCat.of 𝒪) := fun j => ι j ≫ πM
  have hu : ∀ j, ∃ u : FakeEllipticCurve.WithFullLevel Λ N m (A j), ptF (A j) (s j) u = ⟨ι j, rfl⟩ :=
    fun j => hM.ptF_surjective (A j) (s j) ⟨ι j, rfl⟩
  choose u hu using hu
  let φ : ∀ j, Spec (CommRingCat.of (A j)) ⟶ T := fun j => (pt' (A j) (s j) (u j)).1

  have key : ∀ {C : Type} [CommRing C] (j : M.affineCover.I₀) {S : Type} [CommRing S]
      (sS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (v : FakeEllipticCurve.WithFullLevel Λ N m S)
      (γ : S →+* C) (δ : (A j) →+* C),
      Spec.map (CommRingCat.ofHom γ) ≫ (ptF S sS v).1 = Spec.map (CommRingCat.ofHom δ) ≫ ι j →
      Spec.map (CommRingCat.ofHom γ) ≫ (pt' S sS v).1 = Spec.map (CommRingCat.ofHom δ) ≫ φ j := by
    intro C _ j S _ sS v γ δ h
    refine comp_pt'_eq_of_comp_ptF_eq hM πT pt' hiso hpb sS (s j) v (u j) γ δ ?_ ?_
    · rw [← (ptF S sS v).2, ← Category.assoc, h, Category.assoc]
    · rw [h, hu j]

  have hφ : ∀ i j, Limits.pullback.fst (ι i) (ι j) ≫ φ i = Limits.pullback.snd (ι i) (ι j) ≫ φ j := by
    intro i j
    refine Scheme.Cover.hom_ext (Limits.pullback (ι i) (ι j)).affineCover _ _ fun k => ?_
    let w := (Limits.pullback (ι i) (ι j)).affineCover.f k
    have hα : Spec.map (Spec.preimage (w ≫ Limits.pullback.fst (ι i) (ι j))) = w ≫ Limits.pullback.fst (ι i) (ι j) :=
      Spec.map_preimage _
    have hβ : Spec.map (Spec.preimage (w ≫ Limits.pullback.snd (ι i) (ι j))) = w ≫ Limits.pullback.snd (ι i) (ι j) :=
      Spec.map_preimage _
    rw [← Category.assoc, ← Category.assoc, ← hα, ← hβ]
    have hk := key i (s j) (u j) (Spec.preimage (w ≫ Limits.pullback.snd (ι i) (ι j))).hom
      (Spec.preimage (w ≫ Limits.pullback.fst (ι i) (ι j))).hom
    simp only [CommRingCat.ofHom_hom] at hk
    refine (hk ?_).symm
    rw [hu j, hα, hβ]
    show (w ≫ _) ≫ ι j = (w ≫ _) ≫ ι i
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  let Φ : M ⟶ T := Scheme.Cover.glueMorphisms M.affineCover φ hφ
  have hΦι : ∀ j, ι j ≫ Φ = φ j := fun j => Scheme.Cover.ι_glueMorphisms M.affineCover φ hφ j

  have hprop : ∀ (S : Type) [CommRing S] (sS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (v : FakeEllipticCurve.WithFullLevel Λ N m S), (pt' S sS v).1 = (ptF S sS v).1 ≫ Φ := by
    intro S _ sS v
    let y := (ptF S sS v).1
    refine Scheme.Cover.hom_ext (M.affineCover.pullback₁ y) _ _ fun j => ?_
    change Limits.pullback.fst y (ι j) ≫ (pt' S sS v).1 = Limits.pullback.fst y (ι j) ≫ (y ≫ Φ)
    refine Scheme.Cover.hom_ext (Limits.pullback y (ι j)).affineCover _ _ fun k => ?_
    let w := (Limits.pullback y (ι j)).affineCover.f k
    show w ≫ Limits.pullback.fst y (ι j) ≫ (pt' S sS v).1 = w ≫ Limits.pullback.fst y (ι j) ≫ (y ≫ Φ)
    have hγ : Spec.map (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))) = w ≫ Limits.pullback.fst y (ι j) :=
      Spec.map_preimage _
    have hδ : Spec.map (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))) = w ≫ Limits.pullback.snd y (ι j) :=
      Spec.map_preimage _
    rw [← Category.assoc, ← Category.assoc, ← hγ]
    have hk := key j sS v (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))).hom
      (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))).hom
    simp only [CommRingCat.ofHom_hom] at hk
    have hc : Spec.map (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))) ≫ (ptF S sS v).1 =
        Spec.map (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))) ≫ ι j := by
      rw [hγ, hδ]
      show (w ≫ _) ≫ y = (w ≫ _) ≫ ι j
      rw [Category.assoc, Category.assoc, Limits.pullback.condition]
    refine (hk hc).trans ?_
    show Spec.map (Spec.preimage (w ≫ Limits.pullback.snd y (ι j))) ≫ φ j =
      Spec.map (Spec.preimage (w ≫ Limits.pullback.fst y (ι j))) ≫ y ≫ Φ
    rw [← hΦι j, ← Category.assoc, ← Category.assoc]
    congr 1
    exact hc.symm
  refine ⟨Φ, ⟨?_, hprop⟩, ?_⟩
  ·
    refine Scheme.Cover.hom_ext M.affineCover _ _ fun j => ?_
    change (ι j ≫ Φ) ≫ πT = ι j ≫ πM
    rw [hΦι j]
    exact (pt' (A j) (s j) (u j)).2
  ·
    rintro Φ' ⟨-, hΦ'⟩
    refine Scheme.Cover.hom_ext M.affineCover _ _ fun j => ?_
    change ι j ≫ Φ' = ι j ≫ Φ
    rw [hΦι j]
    have := hΦ' (A j) (s j) (u j)
    rw [hu j] at this
    exact this.symm

end Yoneda

section Action

variable {N m : ℕ} {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
  (hΛ : IsOrder Λ) (hM : IsFineModuli Λ N m M πM ptF)

noncomputable def ptTw (c : ↥Λ) (hc : IsUnitMod Λ m c) :
    ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM :=
  fun S _ s u => ptF S s (twist hΛ c hc u)

include hM in
theorem ptTw_iso (c : ↥Λ) (hc : IsUnitMod Λ m c) (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u u' : FakeEllipticCurve.WithFullLevel Λ N m S)
    (h : FakeEllipticCurve.WithFullLevel.Iso u u') : ptTw (ptF := ptF) hΛ c hc S s u = ptTw (ptF := ptF) hΛ c hc S s u' :=
  hM.ptF_iso S s _ _ (iso_twist_of_iso hΛ c hc u u' h)

include hM in
theorem ptTw_pullback (c : ↥Λ) (hc : IsUnitMod Λ m c) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪))
    (hs : Spec.map (CommRingCat.ofHom φ) ≫ s = s')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') :
    (ptTw (ptF := ptF) hΛ c hc S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptTw (ptF := ptF) hΛ c hc S s u).1 :=
  hM.ptF_pullback S S' φ s s' hs _ _ (isPullback_twist hΛ φ c hc u u' h)

noncomputable def rho0 (c : ↥Λ) (hc : IsUnitMod Λ m c) : M ⟶ M :=
  (existsUnique_hom_pt'_eq hM πM (ptTw hΛ c hc) (ptTw_iso hΛ hM c hc) (ptTw_pullback hΛ hM c hc)).exists.choose

theorem rho0_over (c : ↥Λ) (hc : IsUnitMod Λ m c) : rho0 hΛ hM c hc ≫ πM = πM :=
  (existsUnique_hom_pt'_eq hM πM (ptTw hΛ c hc) (ptTw_iso hΛ hM c hc) (ptTw_pullback hΛ hM c hc)).exists.choose_spec.1

theorem rho0_spec (c : ↥Λ) (hc : IsUnitMod Λ m c) (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    (ptF S s (twist hΛ c hc u)).1 = (ptF S s u).1 ≫ rho0 hΛ hM c hc :=
  (existsUnique_hom_pt'_eq hM πM (ptTw hΛ c hc) (ptTw_iso hΛ hM c hc) (ptTw_pullback hΛ hM c hc)).exists.choose_spec.2
    S s u

theorem rho0_unique (c : ↥Λ) (hc : IsUnitMod Λ m c) (Φ : M ⟶ M) (hΦ : Φ ≫ πM = πM)
    (h : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithFullLevel Λ N m S), (ptF S s (twist hΛ c hc u)).1 = (ptF S s u).1 ≫ Φ) :
    Φ = rho0 hΛ hM c hc :=
  (existsUnique_hom_pt'_eq hM πM (ptTw hΛ c hc) (ptTw_iso hΛ hM c hc) (ptTw_pullback hΛ hM c hc)).unique
    ⟨hΦ, h⟩ ⟨rho0_over hΛ hM c hc, rho0_spec hΛ hM c hc⟩

theorem rho0_congr (c c' : ↥Λ) (hc : IsUnitMod Λ m c) (hc' : IsUnitMod Λ m c')
    (h : Cong Λ m (c : ℍ[ℚ, a, b]) (c' : ℍ[ℚ, a, b])) : rho0 hΛ hM c hc = rho0 hΛ hM c' hc' := by
  refine rho0_unique hΛ hM c' hc' _ (rho0_over hΛ hM c hc) fun S _ s u => ?_
  rw [← rho0_spec hΛ hM c hc S s u]
  exact congrArg Subtype.val (hM.ptF_iso S s _ _ (iso_twist_of_cong hΛ c c' hc hc' h u)).symm

theorem rho0_one (h1 : IsUnitMod Λ m ⟨1, hΛ.one_mem⟩) : rho0 hΛ hM ⟨1, hΛ.one_mem⟩ h1 = 𝟙 M := by
  symm
  refine rho0_unique hΛ hM _ h1 _ (Category.id_comp _) fun S _ s u => ?_
  rw [Category.comp_id]
  exact congrArg Subtype.val (hM.ptF_iso S s _ _ (iso_twist_one hΛ h1 u))

theorem rho0_mul (c c' : ↥Λ) (hc : IsUnitMod Λ m c) (hc' : IsUnitMod Λ m c') :
    rho0 hΛ hM ⟨(c : ℍ[ℚ, a, b]) * (c' : ℍ[ℚ, a, b]), hΛ.mul_mem c.2 c'.2⟩ (hc.mul hΛ hc') =
      rho0 hΛ hM c' hc' ≫ rho0 hΛ hM c hc := by
  symm
  refine rho0_unique hΛ hM _ (hc.mul hΛ hc') _ ?_ fun S _ s u => ?_
  · rw [Category.assoc, rho0_over, rho0_over]
  · rw [← Category.assoc, ← rho0_spec hΛ hM c' hc' S s u, ← rho0_spec hΛ hM c hc S s (twist hΛ c' hc' u)]
    exact congrArg Subtype.val (hM.ptF_iso S s _ _ (iso_twist_twist hΛ c c' hc hc' u)).symm

theorem rho0_chi_comp_rho0_chi_inv (g : G hΛ m) :
    rho0 hΛ hM (chi hΛ m g) (isUnitMod_chi hΛ m g) ≫ rho0 hΛ hM (chi hΛ m g⁻¹) (isUnitMod_chi hΛ m g⁻¹) = 𝟙 M := by
  rw [← rho0_mul hΛ hM (chi hΛ m g⁻¹) (chi hΛ m g) (isUnitMod_chi hΛ m g⁻¹) (isUnitMod_chi hΛ m g),
    ← rho0_one hΛ hM (isUnitMod_one hΛ m)]
  refine rho0_congr hΛ hM _ _ _ _ ?_
  have h := (label_mul hΛ m g⁻¹ g).symm
  rw [inv_mul_cancel] at h
  exact h.trans (label_one hΛ m)

noncomputable def rhoIso (g : G hΛ m) : M ≅ M where
  hom := rho0 hΛ hM (chi hΛ m g) (isUnitMod_chi hΛ m g)
  inv := rho0 hΛ hM (chi hΛ m g⁻¹) (isUnitMod_chi hΛ m g⁻¹)
  hom_inv_id := rho0_chi_comp_rho0_chi_inv hΛ hM g
  inv_hom_id := by
    have h := rho0_chi_comp_rho0_chi_inv hΛ hM g⁻¹
    have e : rho0 hΛ hM (chi hΛ m g⁻¹⁻¹) (isUnitMod_chi hΛ m g⁻¹⁻¹) = rho0 hΛ hM (chi hΛ m g) (isUnitMod_chi hΛ m g) := by
      congr 1
    rw [e] at h
    exact h

noncomputable def rho : G hΛ m →* Aut M where
  toFun := rhoIso hΛ hM
  map_one' := by
    apply Iso.ext
    show rho0 hΛ hM (chi hΛ m 1) (isUnitMod_chi hΛ m 1) = 𝟙 M
    rw [← rho0_one hΛ hM (isUnitMod_one hΛ m)]
    exact rho0_congr hΛ hM _ _ _ _ (label_one hΛ m)
  map_mul' g h := by
    apply Iso.ext
    show rho0 hΛ hM (chi hΛ m (g * h)) (isUnitMod_chi hΛ m (g * h)) =
      rho0 hΛ hM (chi hΛ m h) (isUnitMod_chi hΛ m h) ≫ rho0 hΛ hM (chi hΛ m g) (isUnitMod_chi hΛ m g)
    rw [← rho0_mul hΛ hM (chi hΛ m g) (chi hΛ m h) (isUnitMod_chi hΛ m g) (isUnitMod_chi hΛ m h)]
    exact rho0_congr hΛ hM _ _ _ _ (label_mul hΛ m g h)

theorem rho_hom (g : G hΛ m) : (rho hΛ hM g).hom = rho0 hΛ hM (chi hΛ m g) (isUnitMod_chi hΛ m g) := rfl

theorem isLevelTwistAction : IsLevelTwistAction Λ N m M πM ptF (G hΛ m) (rho hΛ hM) (chi hΛ m) where
  over_base g := rho0_over hΛ hM _ _
  twist g S _ s u u' h := by
    rw [rho_hom, ← rho0_spec hΛ hM (chi hΛ m g) (isUnitMod_chi hΛ m g) S s u]
    exact congrArg Subtype.val (hM.ptF_iso S s _ _ (iso_twist_of_isTwist hΛ (chi hΛ m g) (isUnitMod_chi hΛ m g) u u' h)).symm
  label_one := label_one hΛ m
  label_mul g g' := label_mul hΛ m g g'
  label_surjective c d hcd hdc := by
    obtain ⟨g, hg⟩ := label_surjective hΛ m c d hcd hdc
    exact ⟨g, hg⟩
  label_injective g g' h := label_injective hΛ m g g' h

end Action

end P2mKcLevelTwistAction
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction.P2mKcLevelTwistAction"

open P2mKcLevelTwistAction in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (N m : ℕ) [NeZero m]
    {𝒪 : Type} [CommRing 𝒪]
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (ρ : G →* Aut M) (χ : G → ↥Λ),
      IsLevelTwistAction Λ N m M πM ptF G ρ χ := by
  haveI := finite_G hΛ m
  exact ⟨G hΛ m, inferInstance, Fintype.ofFinite _, rho hΛ hM, chi hΛ m, isLevelTwistAction hΛ hM⟩

end S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction (solution)
