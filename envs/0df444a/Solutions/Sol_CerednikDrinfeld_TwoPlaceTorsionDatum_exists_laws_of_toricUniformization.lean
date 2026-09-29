-- Prove2me | solution 1 for CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_toricUniformization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8786d8dd-2fe1-57c9-984b-cfd1dd07a3ff

import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve CerednikDrinfeld P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "ribbonGramModP ribbonGramModP_apply ToricUniformization JPrimeTorsionDatum DegeneracyData ribbonKernel mem_ribbonKernel ribbonGram ribbonGram_apply ribbonComponentGroup ribbonComponentGroupProj HeckeData heckeKernelMap JPrimeTorsionDatum.LocalLaws TwoPlaceTorsionDatum"
p2m_open "CerednikDrinfeld"

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {p r : ℕ} [Fact r.Prime] {D : DegeneracyData E V} {H : HeckeData D} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {hA : A.LiesOverPrime r} {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
  {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}

namespace ToricUniformization
p2m_export "CerednikDrinfeld.ToricUniformization" "mk kummer frob_quot U torsionEquiv divisible frob_toric periodEquiv π_hecke period_adjoint torsion_hecke π_surj_torsion tame_surjective tame heckeU π"
p2m_open "CerednikDrinfeld.ToricUniformization"

private def _root_.CerednikDrinfeld.ToricUniformization.Tp (𝒰 : ToricUniformization p r D H A hA T hecke gal) : AddSubgroup T where
  carrier := {t | p • t = 0}
  zero_mem' := smul_zero p
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq, smul_add] at *; rw [ha, hb, add_zero]
  neg_mem' := by intro a ha; simp only [Set.mem_setOf_eq, smul_neg] at *; rw [ha, neg_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "Tp"
theorem mem_Tp (𝒰 : ToricUniformization p r D H A hA T hecke gal) (t : T) : t ∈ 𝒰.Tp ↔ p • t = 0 := Iff.rfl

private theorem _root_.CerednikDrinfeld.ToricUniformization.hecke_mem_Tp (𝒰 : ToricUniformization p r D H A hA T hecke gal) (x : HeckeAlg) {t : T} (ht : t ∈ 𝒰.Tp) :
    hecke x t ∈ 𝒰.Tp := by
  rw [mem_Tp] at ht ⊢; rw [← map_nsmul, ht, map_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "hecke_mem_Tp"

private theorem _root_.CerednikDrinfeld.ToricUniformization.gal_mem_Tp (𝒰 : ToricUniformization p r D H A hA T hecke gal) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {t : T} (ht : t ∈ 𝒰.Tp) : gal σ t ∈ 𝒰.Tp := by
  rw [mem_Tp] at ht ⊢; rw [← map_nsmul, ht, map_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "gal_mem_Tp"

private def _root_.CerednikDrinfeld.ToricUniformization.heckeTp (𝒰 : ToricUniformization p r D H A hA T hecke gal) : HeckeAlg →+* Module.End ℤ ↥𝒰.Tp where
  toFun x := ((hecke x).toAddMonoidHom.domRestrict 𝒰.Tp).codRestrict 𝒰.Tp (fun t => 𝒰.hecke_mem_Tp x t.2) |>.toIntLinearMap
  map_one' := by ext t; simp
  map_mul' x y := by ext t; simp
  map_zero' := by ext t; simp
  map_add' x y := by ext t; simp

p2m_export "CerednikDrinfeld.ToricUniformization" "heckeTp"

private def _root_.CerednikDrinfeld.ToricUniformization.galTp (𝒰 : ToricUniformization p r D H A hA T hecke gal) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut ↥𝒰.Tp where
  toFun σ :=
    { toFun := fun t => ⟨gal σ t, 𝒰.gal_mem_Tp σ t.2⟩
      invFun := fun t => ⟨gal σ⁻¹ t, 𝒰.gal_mem_Tp σ⁻¹ t.2⟩
      left_inv := fun t => by
        apply Subtype.ext
        show gal σ⁻¹ (gal σ t) = t
        rw [← AddAut.mul_apply', ← map_mul, inv_mul_cancel, map_one, AddAut.one_apply']
      right_inv := fun t => by
        apply Subtype.ext
        show gal σ (gal σ⁻¹ t) = t
        rw [← AddAut.mul_apply', ← map_mul, mul_inv_cancel, map_one, AddAut.one_apply']
      map_add' := fun a b => by ext; simp }
  map_one' := by ext t; simp
  map_mul' σ τ := by ext t; simp

p2m_export "CerednikDrinfeld.ToricUniformization" "galTp"

private def _root_.CerednikDrinfeld.ToricUniformization.toric (𝒰 : ToricUniformization p r D H A hA T hecke gal) : AddSubgroup ↥𝒰.Tp :=
  AddSubgroup.comap 𝒰.Tp.subtype ((Submodule.torsionBy ℤ 𝒰.U (p : ℤ)).toAddSubgroup.map 𝒰.π)

p2m_export "CerednikDrinfeld.ToricUniformization" "toric"

section SpHelpers

variable (𝒰 : ToricUniformization p r D H A hA T hecke gal)

private abbrev _root_.CerednikDrinfeld.ToricUniformization.Inv : AddSubgroup ↥𝒰.Tp :=
  ⨅ σ ∈ A.inertiaSubgroupIn ℚ, ((𝒰.galTp σ).toAddMonoidHom - AddMonoidHom.id ↥𝒰.Tp).ker

p2m_export "CerednikDrinfeld.ToricUniformization" "Inv"
private theorem _root_.CerednikDrinfeld.ToricUniformization.mem_Inv_iff (t : ↥𝒰.Tp) : t ∈ 𝒰.Inv ↔ ∀ σ ∈ A.inertiaSubgroupIn ℚ, gal σ (t : T) = t := by
  simp only [Inv, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    sub_eq_zero, AddEquiv.coe_toAddMonoidHom]
  refine forall_congr' fun σ => forall_congr' fun _ => ?_
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

p2m_export "CerednikDrinfeld.ToricUniformization" "mem_Inv_iff"

private theorem _root_.CerednikDrinfeld.ToricUniformization.zsmul_lift_mem_ker (t : ↥𝒰.Tp) (u : 𝒰.U) (hu : 𝒰.π u = t) : (p : ℤ) • u ∈ 𝒰.π.ker := by
  rw [AddMonoidHom.mem_ker, map_zsmul, hu, natCast_zsmul]
  exact t.2

p2m_export "CerednikDrinfeld.ToricUniformization" "zsmul_lift_mem_ker"

private def _root_.CerednikDrinfeld.ToricUniformization.IsSpValue (t : T) (c : ribbonComponentGroup D) : Prop :=
  ∃ (u : 𝒰.U) (x : ↥(ribbonKernel D)) (g : Module.Dual ℤ ↥(ribbonKernel D)),
    𝒰.π u = t ∧ (p : ℤ) • u = (𝒰.periodEquiv x : 𝒰.U) ∧ p • g = ribbonGram D x ∧ c = ribbonComponentGroupProj D g

p2m_export "CerednikDrinfeld.ToricUniformization" "IsSpValue"

private theorem _root_.CerednikDrinfeld.ToricUniformization.torsion_ker_eq_zero [Fact p.Prime] (v : 𝒰.U) (hv : (p : ℤ) • v = 0) (hk : v ∈ 𝒰.π.ker) : v = 0 := by
  set z := 𝒰.periodEquiv.symm ⟨v, hk⟩ with hz
  have hzv : (𝒰.periodEquiv z : 𝒰.U) = v := by rw [hz, AddEquiv.apply_symm_apply]
  have hpz : 𝒰.periodEquiv ((p : ℤ) • z) = 0 := by
    apply Subtype.ext
    rw [map_zsmul, AddSubgroup.coe_zsmul, hzv, hv, AddSubgroup.coe_zero]
  have hz0 : (p : ℤ) • z = 0 := 𝒰.periodEquiv.injective (by rw [hpz, map_zero])
  rcases smul_eq_zero.mp hz0 with h | h
  · exact absurd (by exact_mod_cast h) (Fact.out : p.Prime).ne_zero
  · rw [← hzv, h, map_zero, AddSubgroup.coe_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "torsion_ker_eq_zero"

theorem dual_nsmul_cancel [Fact p.Prime] {g g' : Module.Dual ℤ ↥(ribbonKernel D)} (h : p • g = p • g') : g = g' := by
  ext y
  have := LinearMap.congr_fun h y
  simp only [LinearMap.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) this

theorem proj_ribbonGram (w : ↥(ribbonKernel D)) : ribbonComponentGroupProj D (ribbonGram D w) = 0 := by
  rw [show ribbonComponentGroupProj D (ribbonGram D w) = (LinearMap.range (ribbonGram D)).mkQ (ribbonGram D w) from rfl,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self _ w

namespace IsSpValue

private theorem _root_.CerednikDrinfeld.ToricUniformization.IsSpValue.unique [Fact p.Prime] {t : T} {c c' : ribbonComponentGroup D}
    (hc : 𝒰.IsSpValue t c) (hc' : 𝒰.IsSpValue t c') : c = c' := by
  obtain ⟨u, x, g, hu, hpu, hg, rfl⟩ := hc
  obtain ⟨u', x', g', hu', hpu', hg', rfl⟩ := hc'

  have hk : u' - u ∈ 𝒰.π.ker := by rw [AddMonoidHom.mem_ker, map_sub, hu, hu', sub_self]
  set w := 𝒰.periodEquiv.symm ⟨u' - u, hk⟩ with hw
  have hwv : (𝒰.periodEquiv w : 𝒰.U) = u' - u := by rw [hw, AddEquiv.apply_symm_apply]

  have hx : x' = x + (p : ℤ) • w := by
    apply 𝒰.periodEquiv.injective
    apply Subtype.ext
    rw [map_add, map_zsmul, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, hwv, ← hpu, ← hpu', smul_sub]
    abel

  have hgg : g' = g + ribbonGram D w := by
    apply dual_nsmul_cancel (p := p)
    rw [hg', smul_add, hg, hx, map_add, map_zsmul, natCast_zsmul]
  rw [hgg, map_add, proj_ribbonGram, add_zero]

end IsSpValue
p2m_export "CerednikDrinfeld.ToricUniformization" "IsSpValue.unique"

private theorem _root_.CerednikDrinfeld.ToricUniformization.exists_isSpValue [Fact p.Prime] (t : ↥𝒰.Tp) (ht : t ∈ 𝒰.Inv) : ∃ c, 𝒰.IsSpValue (t : T) c := by
  obtain ⟨u, hu⟩ := 𝒰.π_surj_torsion (t : T) t.2
  have hk := 𝒰.zsmul_lift_mem_ker t u hu
  set x := 𝒰.periodEquiv.symm ⟨(p : ℤ) • u, hk⟩ with hxdef
  have hpu : (p : ℤ) • u = (𝒰.periodEquiv x : 𝒰.U) := by rw [hxdef, AddEquiv.apply_symm_apply]

  obtain ⟨σ, hσ⟩ := 𝒰.tame_surjective (Multiplicative.ofAdd 1)
  obtain ⟨v, hv, hχ⟩ := 𝒰.kummer σ u x hpu
  have hinv := (𝒰.mem_Inv_iff t).mp ht σ.1 σ.2
  have hπv : 𝒰.π (v : 𝒰.U) = 0 := by
    have h1 : gal σ.1 (𝒰.π u) = 𝒰.π u + 𝒰.π (v : 𝒰.U) := hv
    rw [hu, hinv] at h1
    exact (add_eq_left.mp h1.symm)
  have hv0 : (v : 𝒰.U) = 0 := 𝒰.torsion_ker_eq_zero v ((Submodule.mem_torsionBy_iff _ _).mp v.2) hπv
  have hv0' : v = 0 := Subtype.ext hv0
  rw [hv0', map_zero, hσ, toAdd_ofAdd, one_smul] at hχ

  have hdvd : ∀ y, (p : ℤ) ∣ ribbonGram D x y := by
    intro y
    have := LinearMap.congr_fun hχ y
    simp only [LinearMap.zero_apply, ribbonGramModP_apply] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this.symm

  let g : Module.Dual ℤ ↥(ribbonKernel D) :=
    { toFun := fun y => ribbonGram D x y / p
      map_add' := fun y y' => by
        rw [map_add]
        exact Int.add_ediv_of_dvd_left (hdvd y)
      map_smul' := fun n y => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (hdvd y)] }
  refine ⟨ribbonComponentGroupProj D g, u, x, g, hu, hpu, ?_, rfl⟩
  ext y
  simp only [LinearMap.smul_apply, smul_eq_mul, g, LinearMap.coe_mk, AddHom.coe_mk]
  exact Int.mul_ediv_cancel' (hdvd y)

p2m_export "CerednikDrinfeld.ToricUniformization" "exists_isSpValue"
namespace IsSpValue

private theorem _root_.CerednikDrinfeld.ToricUniformization.IsSpValue.add {t t' : T} {c c' : ribbonComponentGroup D}
    (hc : 𝒰.IsSpValue t c) (hc' : 𝒰.IsSpValue t' c') : 𝒰.IsSpValue (t + t') (c + c') := by
  obtain ⟨u, x, g, hu, hpu, hg, rfl⟩ := hc
  obtain ⟨u', x', g', hu', hpu', hg', rfl⟩ := hc'
  refine ⟨u + u', x + x', g + g', by rw [map_add, hu, hu'], ?_, by rw [smul_add, hg, hg', map_add], by rw [map_add]⟩
  rw [smul_add, hpu, hpu', map_add, AddSubgroup.coe_add]

end IsSpValue
p2m_export "CerednikDrinfeld.ToricUniformization" "IsSpValue.add"
namespace IsSpValue
private theorem _root_.CerednikDrinfeld.ToricUniformization.IsSpValue.zero : 𝒰.IsSpValue 0 0 :=
  ⟨0, 0, 0, map_zero _, by rw [smul_zero, map_zero, AddSubgroup.coe_zero], by rw [smul_zero, map_zero], by rw [map_zero]⟩

end IsSpValue
p2m_export "CerednikDrinfeld.ToricUniformization" "IsSpValue.zero"

private def _root_.CerednikDrinfeld.ToricUniformization.IsSp (s : ↥𝒰.Inv →+ ribbonComponentGroup D) : Prop := ∀ t : ↥𝒰.Inv, 𝒰.IsSpValue ((t : ↥𝒰.Tp) : T) (s t)

p2m_export "CerednikDrinfeld.ToricUniformization" "IsSp"
private theorem _root_.CerednikDrinfeld.ToricUniformization.exists_isSp [Fact p.Prime] : ∃ s, 𝒰.IsSp s := by
  classical
  refine ⟨{ toFun := fun t => (𝒰.exists_isSpValue t.1 t.2).choose
            map_zero' := ?_, map_add' := ?_ }, fun t => (𝒰.exists_isSpValue t.1 t.2).choose_spec⟩
  · exact (IsSpValue.unique 𝒰 (𝒰.exists_isSpValue (0 : ↥𝒰.Inv).1 (0 : ↥𝒰.Inv).2).choose_spec
      (by simpa using IsSpValue.zero 𝒰))
  · intro t t'
    exact IsSpValue.unique 𝒰 (𝒰.exists_isSpValue (t + t').1 (t + t').2).choose_spec
      (by simpa using IsSpValue.add 𝒰 (𝒰.exists_isSpValue t.1 t.2).choose_spec (𝒰.exists_isSpValue t'.1 t'.2).choose_spec)

p2m_export "CerednikDrinfeld.ToricUniformization" "exists_isSp"
end SpHelpers

private def _root_.CerednikDrinfeld.ToricUniformization.sp (𝒰 : ToricUniformization p r D H A hA T hecke gal) :
    ↥(⨅ σ ∈ A.inertiaSubgroupIn ℚ, ((𝒰.galTp σ).toAddMonoidHom - AddMonoidHom.id ↥𝒰.Tp).ker) →+
      ribbonComponentGroup D := by
  classical
  exact if h : ∃ s, 𝒰.IsSp s then h.choose else 0

p2m_export "CerednikDrinfeld.ToricUniformization" "sp"
private theorem _root_.CerednikDrinfeld.ToricUniformization.sp_isSp [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal) : 𝒰.IsSp 𝒰.sp := by
  classical
  have h := 𝒰.exists_isSp
  rw [sp, dif_pos h]
  exact h.choose_spec

p2m_export "CerednikDrinfeld.ToricUniformization" "sp_isSp"

private theorem _root_.CerednikDrinfeld.ToricUniformization.sp_eq_proj [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal)
    (t : ↥𝒰.Inv) (u : 𝒰.U) (x : ↥(ribbonKernel D)) (g : Module.Dual ℤ ↥(ribbonKernel D))
    (hu : 𝒰.π u = ((t : ↥𝒰.Tp) : T)) (hpu : (p : ℤ) • u = (𝒰.periodEquiv x : 𝒰.U)) (hg : p • g = ribbonGram D x) :
    𝒰.sp t = ribbonComponentGroupProj D g :=
  IsSpValue.unique 𝒰 (𝒰.sp_isSp t) ⟨u, x, g, hu, hpu, hg, rfl⟩

p2m_export "CerednikDrinfeld.ToricUniformization" "sp_eq_proj"

@[scoped simp] theorem coe_heckeTp (𝒰 : ToricUniformization p r D H A hA T hecke gal) (x : HeckeAlg) (t : ↥𝒰.Tp) :
    ((𝒰.heckeTp x t : ↥𝒰.Tp) : T) = hecke x (t : T) := rfl

@[scoped simp] theorem coe_galTp (𝒰 : ToricUniformization p r D H A hA T hecke gal) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ↥𝒰.Tp) :
    ((𝒰.galTp σ t : ↥𝒰.Tp) : T) = gal σ (t : T) := rfl

private theorem _root_.CerednikDrinfeld.ToricUniformization.mem_toric_iff (𝒰 : ToricUniformization p r D H A hA T hecke gal) (t : ↥𝒰.Tp) :
    t ∈ 𝒰.toric ↔ ∃ v : 𝒰.U, v ∈ Submodule.torsionBy ℤ 𝒰.U (p : ℤ) ∧ 𝒰.π v = (t : T) := by
  simp only [toric, AddSubgroup.mem_comap, AddSubgroup.mem_map, AddSubgroup.coe_subtype, Submodule.mem_toAddSubgroup]

p2m_export "CerednikDrinfeld.ToricUniformization" "mem_toric_iff"
private theorem _root_.CerednikDrinfeld.ToricUniformization.π_torsion_mem_Tp (𝒰 : ToricUniformization p r D H A hA T hecke gal) (v : ↥(Submodule.torsionBy ℤ 𝒰.U (p : ℤ))) : 𝒰.π (v : 𝒰.U) ∈ 𝒰.Tp := by
  rw [mem_Tp, ← map_nsmul, ← natCast_zsmul, (Submodule.mem_torsionBy_iff _ _).mp v.2, map_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "π_torsion_mem_Tp"
private theorem _root_.CerednikDrinfeld.ToricUniformization.π_torsion_mem_toric (𝒰 : ToricUniformization p r D H A hA T hecke gal) (v : ↥(Submodule.torsionBy ℤ 𝒰.U (p : ℤ))) :
    (⟨𝒰.π (v : 𝒰.U), 𝒰.π_torsion_mem_Tp v⟩ : ↥𝒰.Tp) ∈ 𝒰.toric :=
  (𝒰.mem_toric_iff _).mpr ⟨v, v.2, rfl⟩

p2m_export "CerednikDrinfeld.ToricUniformization" "π_torsion_mem_toric"

private def _root_.CerednikDrinfeld.ToricUniformization.torsionToToric (𝒰 : ToricUniformization p r D H A hA T hecke gal) : ↥(Submodule.torsionBy ℤ 𝒰.U (p : ℤ)) →+ ↥𝒰.toric where
  toFun v := ⟨⟨𝒰.π (v : 𝒰.U), 𝒰.π_torsion_mem_Tp v⟩, 𝒰.π_torsion_mem_toric v⟩
  map_zero' := Subtype.ext (Subtype.ext (by simp))
  map_add' v w := Subtype.ext (Subtype.ext (by simp))

p2m_export "CerednikDrinfeld.ToricUniformization" "torsionToToric"
private theorem _root_.CerednikDrinfeld.ToricUniformization.torsionToToric_bijective [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal) : Function.Bijective 𝒰.torsionToToric := by
  constructor
  · intro v w h
    have h' : 𝒰.π (v : 𝒰.U) = 𝒰.π (w : 𝒰.U) := congrArg (fun t : ↥𝒰.toric => ((t : ↥𝒰.Tp) : T)) h
    have hk : (v : 𝒰.U) - w ∈ 𝒰.π.ker := by rw [AddMonoidHom.mem_ker, map_sub, h', sub_self]
    have hp : (p : ℤ) • ((v : 𝒰.U) - w) = 0 := by
      rw [smul_sub, (Submodule.mem_torsionBy_iff _ _).mp v.2, (Submodule.mem_torsionBy_iff _ _).mp w.2, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (𝒰.torsion_ker_eq_zero _ hp hk))
  · intro t
    obtain ⟨v, hv, hπ⟩ := (𝒰.mem_toric_iff _).mp t.2
    exact ⟨⟨v, hv⟩, Subtype.ext (Subtype.ext hπ)⟩

p2m_export "CerednikDrinfeld.ToricUniformization" "torsionToToric_bijective"

private def _root_.CerednikDrinfeld.ToricUniformization.torsionEquivToric [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal) : ↥(Submodule.torsionBy ℤ 𝒰.U (p : ℤ)) ≃+ ↥𝒰.toric :=
  AddEquiv.ofBijective 𝒰.torsionToToric 𝒰.torsionToToric_bijective

p2m_export "CerednikDrinfeld.ToricUniformization" "torsionEquivToric"

private def _root_.CerednikDrinfeld.ToricUniformization.toricEquiv [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal) :
    ↥𝒰.toric ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p) :=
  𝒰.torsionEquivToric.symm.trans 𝒰.torsionEquiv

p2m_export "CerednikDrinfeld.ToricUniformization" "toricEquiv"

private theorem _root_.CerednikDrinfeld.ToricUniformization.toricEquiv_mk [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal) (v : ↥(Submodule.torsionBy ℤ 𝒰.U (p : ℤ)))
    (t : ↥𝒰.Tp) (ht : t ∈ 𝒰.toric) (h : 𝒰.π (v : 𝒰.U) = (t : T)) :
    𝒰.toricEquiv ⟨t, ht⟩ = 𝒰.torsionEquiv v := by
  have e : 𝒰.torsionEquivToric v = ⟨t, ht⟩ := Subtype.ext (Subtype.ext h)
  rw [toricEquiv, AddEquiv.trans_apply, ← e, AddEquiv.symm_apply_apply]

p2m_export "CerednikDrinfeld.ToricUniformization" "toricEquiv_mk"

namespace InstFinite

variable (𝒰 : ToricUniformization p r D H A hA T hecke gal)

theorem finite_linearMap {M N : Type} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    [AddCommGroup N] [Module ℤ N] [Finite N] : Finite (M →ₗ[ℤ] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := M)
  refine Finite.of_injective (fun f : M →ₗ[ℤ] N => fun x : (s : Set M) => f x) ?_
  intro f g h
  refine LinearMap.ext_on hs fun x hx => ?_
  exact congrFun h ⟨x, hx⟩

omit [Fintype V] in

scoped instance : Module.Finite ℤ ↥(ribbonKernel D) :=
  Module.Finite.of_injective (ribbonKernel D).subtype Subtype.val_injective

theorem finite_torsionBy [Fact p.Prime] : Finite ↥(Submodule.torsionBy ℤ 𝒰.U (p : ℤ)) :=
  haveI : Finite (↥(ribbonKernel D) →ₗ[ℤ] ZMod p) := finite_linearMap
  Finite.of_equiv _ 𝒰.torsionEquiv.toEquiv.symm

omit [Fintype V] in

theorem mem_ribbonKernel_of_smul_mem [Fintype V] {n : ℤ} (hn : n ≠ 0) {f : E → ℤ}
    (h : n • f ∈ ribbonKernel D) : f ∈ ribbonKernel D := by
  rw [mem_ribbonKernel] at h ⊢
  intro i
  have := h i
  rw [map_zsmul, smul_eq_zero] at this
  exact this.resolve_left hn

abbrev Λ : AddSubgroup 𝒰.U := 𝒰.π.ker

abbrev S : AddSubgroup 𝒰.U := 𝒰.Tp.comap 𝒰.π

abbrev P : AddSubgroup 𝒰.U := (Submodule.torsionBy ℤ 𝒰.U (p : ℤ)).toAddSubgroup

abbrev K : AddSubgroup 𝒰.U := Λ 𝒰 ⊔ P 𝒰

theorem mem_S {u : 𝒰.U} : u ∈ S 𝒰 ↔ p • 𝒰.π u = 0 := Iff.rfl

theorem mem_P {u : 𝒰.U} : u ∈ P 𝒰 ↔ (p : ℤ) • u = 0 := Submodule.mem_torsionBy_iff _ _

theorem Λ_le_S : Λ 𝒰 ≤ S 𝒰 := fun u hu => by
  rw [mem_S, (AddMonoidHom.mem_ker).mp hu, smul_zero]

theorem P_le_S : P 𝒰 ≤ S 𝒰 := fun u hu => by
  rw [mem_S, ← map_nsmul, ← natCast_zsmul, (mem_P 𝒰).mp hu, map_zero]

theorem K_le_S : K 𝒰 ≤ S 𝒰 := sup_le (Λ_le_S 𝒰) (P_le_S 𝒰)

theorem smul_mem_Λ {u : 𝒰.U} (hu : u ∈ S 𝒰) : (p : ℤ) • u ∈ Λ 𝒰 := by
  rw [AddMonoidHom.mem_ker, map_zsmul, natCast_zsmul]; exact hu

def toΛ : ↥(S 𝒰) →+ ↥(Λ 𝒰) where
  toFun u := ⟨(p : ℤ) • (u : 𝒰.U), smul_mem_Λ 𝒰 u.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' u v := Subtype.ext (by simp [smul_add])

def g : ↥(S 𝒰) →+ (E → ZMod p) :=
  ((Int.castAddHom (ZMod p)).compLeft E).comp <|
    ((ribbonKernel D).subtype.toAddMonoidHom).comp <|
      (𝒰.periodEquiv.symm.toAddMonoidHom).comp (toΛ 𝒰)

theorem g_apply (u : ↥(S 𝒰)) (e : E) :
    g 𝒰 u e = (((𝒰.periodEquiv.symm (toΛ 𝒰 u) : ↥(ribbonKernel D)) : E → ℤ) e : ZMod p) := rfl

theorem ker_g_le [Fact p.Prime] : (g 𝒰).ker ≤ (K 𝒰).addSubgroupOf (S 𝒰) := by
  intro u hu
  rw [AddMonoidHom.mem_ker] at hu
  rw [AddSubgroup.mem_addSubgroupOf]
  set y : ↥(ribbonKernel D) := 𝒰.periodEquiv.symm (toΛ 𝒰 u) with hy

  have hdiv : ∀ e, (p : ℤ) ∣ (y : E → ℤ) e := fun e => by
    have := congrFun hu e
    rw [g_apply, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact this
  choose f hf using hdiv
  have hyf : (y : E → ℤ) = (p : ℤ) • (f : E → ℤ) := funext fun e => by rw [Pi.smul_apply, smul_eq_mul, hf e]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hfY : (f : E → ℤ) ∈ ribbonKernel D := mem_ribbonKernel_of_smul_mem hp0 (hyf ▸ y.2)

  set lam : 𝒰.U := ((𝒰.periodEquiv ⟨f, hfY⟩ : ↥𝒰.π.ker) : 𝒰.U) with hlam
  have hplam : (p : ℤ) • lam = (p : ℤ) • (u : 𝒰.U) := by
    have e1 : (p : ℤ) • (⟨f, hfY⟩ : ↥(ribbonKernel D)) = y := Subtype.ext (by rw [hyf]; rfl)
    have e2 := congrArg (fun z : ↥(ribbonKernel D) => ((𝒰.periodEquiv z : ↥𝒰.π.ker) : 𝒰.U)) e1
    simp only [map_zsmul, AddSubgroup.coe_zsmul] at e2
    rw [hlam, e2, hy, AddEquiv.apply_symm_apply]
    rfl

  refine AddSubgroup.mem_sup.mpr ⟨lam, (𝒰.periodEquiv ⟨f, hfY⟩).2, (u : 𝒰.U) - lam, ?_, add_sub_cancel lam _⟩
  rw [mem_P, smul_sub, hplam, sub_self]

theorem finiteIndex_K [Fact p.Prime] : ((K 𝒰).addSubgroupOf (S 𝒰)).FiniteIndex := by
  haveI : Finite (↥(S 𝒰) ⧸ (g 𝒰).ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange (g 𝒰)).toEquiv.symm
  haveI : ((g 𝒰).ker).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact AddSubgroup.finiteIndex_of_le (ker_g_le 𝒰)

theorem relIndex_Λ_K_ne_zero [Fact p.Prime] : (Λ 𝒰).relIndex (K 𝒰) ≠ 0 := by
  haveI := finite_torsionBy 𝒰
  rw [show K 𝒰 = P 𝒰 ⊔ Λ 𝒰 from sup_comm _ _, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right]
  haveI : ((Λ 𝒰 ⊓ P 𝒰).addSubgroupOf (P 𝒰)).FiniteIndex := AddSubgroup.finiteIndex_of_finite
  exact AddSubgroup.FiniteIndex.index_ne_zero

theorem finiteIndex_Λ [Fact p.Prime] : ((Λ 𝒰).addSubgroupOf (S 𝒰)).FiniteIndex := by
  refine ⟨?_⟩
  show (Λ 𝒰).relIndex (S 𝒰) ≠ 0
  rw [← AddSubgroup.relIndex_mul_relIndex (Λ 𝒰) (K 𝒰) (S 𝒰) le_sup_left (K_le_S 𝒰)]
  exact mul_ne_zero (relIndex_Λ_K_ne_zero 𝒰) (finiteIndex_K 𝒰).index_ne_zero

def πS : ↥(S 𝒰) →+ ↥𝒰.Tp where
  toFun u := ⟨𝒰.π u, u.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem πS_surjective : Function.Surjective (πS 𝒰) := by
  rintro ⟨t, ht⟩
  obtain ⟨u, rfl⟩ := 𝒰.π_surj_torsion t ht
  exact ⟨⟨u, ht⟩, rfl⟩

theorem Λ_le_ker_πS : (Λ 𝒰).addSubgroupOf (S 𝒰) ≤ (πS 𝒰).ker := fun u hu => by
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker] at hu
  rw [AddMonoidHom.mem_ker]
  exact Subtype.ext hu

end InstFinite
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization.InstFinite"

open InstFinite in

private theorem _root_.CerednikDrinfeld.ToricUniformization.finite_Tp [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal) : Finite ↥𝒰.Tp := by
  haveI := finiteIndex_Λ 𝒰
  haveI : Finite (↥(S 𝒰) ⧸ (Λ 𝒰).addSubgroupOf (S 𝒰)) := AddSubgroup.finite_quotient_of_finiteIndex
  refine Finite.of_surjective (QuotientAddGroup.lift ((Λ 𝒰).addSubgroupOf (S 𝒰)) (πS 𝒰) (Λ_le_ker_πS 𝒰)) ?_
  intro t
  obtain ⟨u, rfl⟩ := πS_surjective 𝒰 t
  exact ⟨QuotientAddGroup.mk u, rfl⟩

p2m_export "CerednikDrinfeld.ToricUniformization" "finite_Tp"
scoped instance instFiniteTp [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal) : Finite ↥𝒰.Tp :=
  finite_Tp 𝒰

section Laws

variable (𝒰 : ToricUniformization p r D H A hA T hecke gal)

omit [Fintype V] in

theorem ribbonGram_injective' : Function.Injective (ribbonGram D) := by
  intro x y hxy
  rw [← sub_eq_zero]
  set z := x - y with hz
  have h0 : ribbonGram D z = 0 := by rw [hz, map_sub, hxy, sub_self]
  have hzz : ribbonGram D z z = 0 := by rw [h0, LinearMap.zero_apply]
  rw [ribbonGram_apply] at hzz
  have hnonneg : ∀ e ∈ (Finset.univ : Finset E), 0 ≤ (D.w e : ℤ) * (z.1 e * z.1 e) :=
    fun e _ => mul_nonneg (by exact_mod_cast (D.w e).pos.le) (mul_self_nonneg _)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzz
  apply Subtype.ext
  funext e
  have he := hall e (Finset.mem_univ e)
  rcases mul_eq_zero.mp he with h | h
  · exact absurd (by exact_mod_cast h) (D.w e).pos.ne'
  · exact mul_self_eq_zero.mp h

omit [Fintype V] in

theorem ribbonGram_comm' (x y : ↥(ribbonKernel D)) : ribbonGram D x y = ribbonGram D y x := by
  simp only [ribbonGram_apply]
  exact Finset.sum_congr rfl fun e _ => by ring

private theorem _root_.CerednikDrinfeld.ToricUniformization.exists_period_hecke (ℓ : Nat.Primes) (y : ↥(ribbonKernel D)) :
    ∃ y' : ↥(ribbonKernel D), 𝒰.heckeU (heckeGen ℓ) (𝒰.periodEquiv y : 𝒰.U) = (𝒰.periodEquiv y' : 𝒰.U) ∧
      (ribbonGram D y) ∘ₗ heckeKernelMap H ℓ = ribbonGram D y' := by
  have hk : 𝒰.heckeU (heckeGen ℓ) (𝒰.periodEquiv y : 𝒰.U) ∈ 𝒰.π.ker := by
    rw [AddMonoidHom.mem_ker, 𝒰.π_hecke, (AddMonoidHom.mem_ker).mp (𝒰.periodEquiv y).2, map_zero]
  refine ⟨𝒰.periodEquiv.symm ⟨_, hk⟩, by rw [AddEquiv.apply_symm_apply], ?_⟩
  have h1 : 𝒰.heckeU (heckeGen ℓ) (𝒰.periodEquiv y : 𝒰.U) = (𝒰.periodEquiv (𝒰.periodEquiv.symm ⟨_, hk⟩) : 𝒰.U) := by
    rw [AddEquiv.apply_symm_apply]
  ext z
  rw [LinearMap.comp_apply, ribbonGram_comm' y, 𝒰.period_adjoint ℓ z y _ h1, ribbonGram_comm']

p2m_export "CerednikDrinfeld.ToricUniformization" "exists_period_hecke"

private theorem _root_.CerednikDrinfeld.ToricUniformization.heckeU_mem_torsionBy (x : HeckeAlg) {v : 𝒰.U} (hv : v ∈ Submodule.torsionBy ℤ 𝒰.U (p : ℤ)) :
    𝒰.heckeU x v ∈ Submodule.torsionBy ℤ 𝒰.U (p : ℤ) := by
  rw [Submodule.mem_torsionBy_iff] at hv ⊢
  rw [← map_zsmul, hv, map_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "heckeU_mem_torsionBy"

private theorem _root_.CerednikDrinfeld.ToricUniformization.toric_hecke' (x : HeckeAlg) (t : ↥𝒰.Tp) (ht : t ∈ 𝒰.toric) : 𝒰.heckeTp x t ∈ 𝒰.toric := by
  obtain ⟨v, hv, hπ⟩ := (𝒰.mem_toric_iff t).mp ht
  refine (𝒰.mem_toric_iff _).mpr ⟨𝒰.heckeU x v, 𝒰.heckeU_mem_torsionBy x hv, ?_⟩
  rw [𝒰.π_hecke, hπ, coe_heckeTp]

p2m_export "CerednikDrinfeld.ToricUniformization" "toric_hecke'"

private theorem _root_.CerednikDrinfeld.ToricUniformization.toricEquiv_hecke' [Fact p.Prime] (ℓ : Nat.Primes) (t : ↥𝒰.Tp) (ht : t ∈ 𝒰.toric)
    (hℓt : 𝒰.heckeTp (heckeGen ℓ) t ∈ 𝒰.toric) :
    𝒰.toricEquiv ⟨𝒰.heckeTp (heckeGen ℓ) t, hℓt⟩ = (𝒰.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap H ℓ := by
  obtain ⟨v, hv, hπ⟩ := (𝒰.mem_toric_iff t).mp ht
  have hv' : 𝒰.heckeU (heckeGen ℓ) v ∈ Submodule.torsionBy ℤ 𝒰.U (p : ℤ) := 𝒰.heckeU_mem_torsionBy _ hv
  rw [𝒰.toricEquiv_mk ⟨𝒰.heckeU (heckeGen ℓ) v, hv'⟩ _ hℓt
      (by show 𝒰.π (𝒰.heckeU (heckeGen ℓ) v) = _; rw [𝒰.π_hecke, hπ, coe_heckeTp]),
    𝒰.toricEquiv_mk ⟨v, hv⟩ t ht hπ]
  exact 𝒰.torsion_hecke ℓ ⟨v, hv⟩ hv'

p2m_export "CerednikDrinfeld.ToricUniformization" "toricEquiv_hecke'"

private theorem _root_.CerednikDrinfeld.ToricUniformization.toric_le_Inv (t : ↥𝒰.Tp) (ht : t ∈ 𝒰.toric) : t ∈ 𝒰.Inv := by
  obtain ⟨v, hv, hπ⟩ := (𝒰.mem_toric_iff t).mp ht
  rw [mem_Inv_iff]
  intro σ hσ
  have hpv : (p : ℤ) • v = (𝒰.periodEquiv 0 : 𝒰.U) := by
    rw [(Submodule.mem_torsionBy_iff _ _).mp hv, map_zero, AddSubgroup.coe_zero]
  obtain ⟨v', hv', hχ⟩ := 𝒰.kummer ⟨σ, hσ⟩ v 0 hpv
  have h0 : ribbonGramModP p D 0 = 0 := by rw [ribbonGramModP, map_zero, LinearMap.comp_zero]
  rw [h0, smul_zero] at hχ
  have hv0 : v' = 0 := 𝒰.torsionEquiv.injective (by rw [hχ, map_zero])
  rw [hv0, ZeroMemClass.coe_zero, map_zero, add_zero] at hv'
  have hv'' : gal σ (𝒰.π v) = 𝒰.π v := hv'
  rw [hπ] at hv''
  exact hv''

p2m_export "CerednikDrinfeld.ToricUniformization" "toric_le_Inv"

private theorem _root_.CerednikDrinfeld.ToricUniformization.sp_eq_zero_iff' [Fact p.Prime] (t : ↥𝒰.Inv) : 𝒰.sp t = 0 ↔ (t : ↥𝒰.Tp) ∈ 𝒰.toric := by
  obtain ⟨u, x, g, hu, hpu, hg, hsp⟩ := 𝒰.sp_isSp t
  constructor
  · intro h0
    rw [h0, eq_comm, show ribbonComponentGroupProj D g = (LinearMap.range (ribbonGram D)).mkQ g from rfl,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hsp
    obtain ⟨w, hw⟩ := hsp

    have hx : x = (p : ℤ) • w := by
      apply ribbonGram_injective'
      rw [map_zsmul, natCast_zsmul, hw, hg]

    refine (𝒰.mem_toric_iff _).mpr ⟨u - (𝒰.periodEquiv w : 𝒰.U), ?_, ?_⟩
    · rw [Submodule.mem_torsionBy_iff, smul_sub, hpu, hx, map_zsmul, AddSubgroup.coe_zsmul, sub_self]
    · rw [map_sub, hu, (AddMonoidHom.mem_ker).mp (𝒰.periodEquiv w).2, sub_zero]
  · intro ht
    obtain ⟨v, hv, hπv⟩ := (𝒰.mem_toric_iff _).mp ht
    rw [𝒰.sp_eq_proj t v 0 0 hπv (by rw [map_zero, AddSubgroup.coe_zero]; exact (Submodule.mem_torsionBy_iff _ _).mp hv)
      (by rw [smul_zero, map_zero]), map_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "sp_eq_zero_iff'"

private theorem _root_.CerednikDrinfeld.ToricUniformization.mem_range_sp_iff' [Fact p.Prime] (ψ : ribbonComponentGroup D) : ψ ∈ 𝒰.sp.range ↔ p • ψ = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨u, x, g, hu, hpu, hg, hsp⟩ := 𝒰.sp_isSp t
    rw [hsp, ← map_nsmul, hg, proj_ribbonGram]
  · intro hψ
    obtain ⟨g', rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (ribbonGram D)) ψ

    have hmem : p • g' ∈ LinearMap.range (ribbonGram D) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_nsmul]
      exact hψ
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hmem

    obtain ⟨u', hu'⟩ := 𝒰.divisible (𝒰.periodEquiv x : 𝒰.U) p (Fact.out : p.Prime).pos
    have hpu : (p : ℤ) • u' = (𝒰.periodEquiv x : 𝒰.U) := by rw [natCast_zsmul, hu']

    have htp : 𝒰.π u' ∈ 𝒰.Tp := by
      rw [mem_Tp, ← map_nsmul, hu']
      exact (AddMonoidHom.mem_ker).mp (𝒰.periodEquiv x).2

    have hmodp : ribbonGramModP p D x = 0 := by
      ext y
      rw [ribbonGramModP_apply, hx, LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul, Int.cast_mul,
        Int.cast_natCast, ZMod.natCast_self, zero_mul]
    have hinv : (⟨𝒰.π u', htp⟩ : ↥𝒰.Tp) ∈ 𝒰.Inv := by
      rw [mem_Inv_iff]
      intro σ hσ
      obtain ⟨v, hv, hχ⟩ := 𝒰.kummer ⟨σ, hσ⟩ u' x hpu
      rw [hmodp, smul_zero] at hχ
      have hv0 : v = 0 := 𝒰.torsionEquiv.injective (by rw [hχ, map_zero])
      rw [hv0, ZeroMemClass.coe_zero, map_zero, add_zero] at hv
      exact hv
    refine ⟨⟨⟨𝒰.π u', htp⟩, hinv⟩, ?_⟩
    exact 𝒰.sp_eq_proj _ u' x g' rfl hpu hx.symm

p2m_export "CerednikDrinfeld.ToricUniformization" "mem_range_sp_iff'"

private theorem _root_.CerednikDrinfeld.ToricUniformization.sp_hecke' [Fact p.Prime] (ℓ : Nat.Primes) (t : ↥𝒰.Inv)
    (hℓt : 𝒰.heckeTp (heckeGen ℓ) (t : ↥𝒰.Tp) ∈ 𝒰.Inv) (φ : Module.Dual ℤ ↥(ribbonKernel D))
    (hφ : 𝒰.sp t = ribbonComponentGroupProj D φ) :
    𝒰.sp ⟨𝒰.heckeTp (heckeGen ℓ) (t : ↥𝒰.Tp), hℓt⟩ = ribbonComponentGroupProj D (φ ∘ₗ heckeKernelMap H ℓ) := by
  obtain ⟨u, x, g, hu, hpu, hg, hsp⟩ := 𝒰.sp_isSp t

  have hφg : φ - g ∈ LinearMap.range (ribbonGram D) := by
    rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
    exact (hφ.symm.trans hsp)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hφg
  have hφ' : φ = g + ribbonGram D w := by rw [hw]; abel

  obtain ⟨x', hx'1, hx'2⟩ := 𝒰.exists_period_hecke ℓ x
  obtain ⟨w', -, hw'2⟩ := 𝒰.exists_period_hecke ℓ w

  have key : 𝒰.sp ⟨𝒰.heckeTp (heckeGen ℓ) (t : ↥𝒰.Tp), hℓt⟩ =
      ribbonComponentGroupProj D (g ∘ₗ heckeKernelMap H ℓ) := by
    refine 𝒰.sp_eq_proj _ (𝒰.heckeU (heckeGen ℓ) u) x' (g ∘ₗ heckeKernelMap H ℓ) ?_ ?_ ?_
    · rw [𝒰.π_hecke, hu]
      rfl
    · rw [← map_zsmul, hpu, hx'1]
    · rw [← LinearMap.smul_comp, hg, hx'2]
  rw [key, hφ', LinearMap.add_comp, map_add, hw'2, proj_ribbonGram, add_zero]

p2m_export "CerednikDrinfeld.ToricUniformization" "sp_hecke'"

private theorem _root_.CerednikDrinfeld.ToricUniformization.hecke_mem_Inv
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (x : HeckeAlg) (t : ↥𝒰.Tp) (ht : t ∈ 𝒰.Inv) : 𝒰.heckeTp x t ∈ 𝒰.Inv := by
  rw [mem_Inv_iff] at ht ⊢
  intro σ hσ
  rw [coe_heckeTp, comm, ht σ hσ]

p2m_export "CerednikDrinfeld.ToricUniformization" "hecke_mem_Inv"

private theorem _root_.CerednikDrinfeld.ToricUniformization.sp_hecke_ringHom' [Fact p.Prime]
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (heckeΨ : HeckeAlg →+* Module.End ℤ (ribbonComponentGroup D))
    (hΨ : ∀ (ℓ : Nat.Primes) (φ : Module.Dual ℤ ↥(ribbonKernel D)),
      heckeΨ (heckeGen ℓ) (ribbonComponentGroupProj D φ) = ribbonComponentGroupProj D (φ ∘ₗ heckeKernelMap H ℓ))
    (x : HeckeAlg) (t : ↥𝒰.Inv) (ht : 𝒰.heckeTp x (t : ↥𝒰.Tp) ∈ 𝒰.Inv) :
    𝒰.sp ⟨𝒰.heckeTp x (t : ↥𝒰.Tp), ht⟩ = heckeΨ x (𝒰.sp t) := by
  revert t
  induction x using MvPolynomial.induction_on
  ·
    rename_i a
    intro t ht
    have e1 : (⟨𝒰.heckeTp (MvPolynomial.C a) (t : ↥𝒰.Tp), ht⟩ : ↥𝒰.Inv) = a • t := by
      apply Subtype.ext
      show 𝒰.heckeTp (MvPolynomial.C a) (t : ↥𝒰.Tp) = ((a • t : ↥𝒰.Inv) : ↥𝒰.Tp)
      rw [eq_intCast MvPolynomial.C a, map_intCast, Module.End.intCast_apply, AddSubgroup.coe_zsmul]
    rw [e1, map_zsmul, show (MvPolynomial.C a : HeckeAlg) = (a : HeckeAlg) from eq_intCast MvPolynomial.C a,
      map_intCast, Module.End.intCast_apply]
  · rename_i q q' hq hq'
    intro t ht
    have h1 := 𝒰.hecke_mem_Inv comm q _ t.2
    have h2 := 𝒰.hecke_mem_Inv comm q' _ t.2
    have e1 : (⟨𝒰.heckeTp (q + q') (t : ↥𝒰.Tp), ht⟩ : ↥𝒰.Inv) =
        ⟨𝒰.heckeTp q (t : ↥𝒰.Tp), h1⟩ + ⟨𝒰.heckeTp q' (t : ↥𝒰.Tp), h2⟩ := by
      apply Subtype.ext
      show 𝒰.heckeTp (q + q') (t : ↥𝒰.Tp) = 𝒰.heckeTp q (t : ↥𝒰.Tp) + 𝒰.heckeTp q' (t : ↥𝒰.Tp)
      rw [map_add, LinearMap.add_apply]
    rw [e1, map_add 𝒰.sp, hq t h1, hq' t h2, map_add heckeΨ, LinearMap.add_apply]
  · rename_i q n hq
    intro t ht
    have h2 := 𝒰.hecke_mem_Inv comm (heckeGen n) _ t.2
    have h1 := 𝒰.hecke_mem_Inv comm q _ h2
    have e1 : (⟨𝒰.heckeTp (q * MvPolynomial.X n) (t : ↥𝒰.Tp), ht⟩ : ↥𝒰.Inv) =
        ⟨𝒰.heckeTp q ((⟨𝒰.heckeTp (heckeGen n) (t : ↥𝒰.Tp), h2⟩ : ↥𝒰.Inv) : ↥𝒰.Tp), h1⟩ := by
      apply Subtype.ext
      show 𝒰.heckeTp (q * MvPolynomial.X n) (t : ↥𝒰.Tp) = 𝒰.heckeTp q (𝒰.heckeTp (heckeGen n) (t : ↥𝒰.Tp))
      rw [map_mul, Module.End.mul_apply]
      rfl

    obtain ⟨φ, hφ⟩ := Submodule.mkQ_surjective (LinearMap.range (ribbonGram D)) (𝒰.sp t)
    have hgen : 𝒰.sp ⟨𝒰.heckeTp (heckeGen n) (t : ↥𝒰.Tp), h2⟩ = heckeΨ (heckeGen n) (𝒰.sp t) := by
      rw [𝒰.sp_hecke' n t h2 φ hφ.symm, ← hΨ]
      exact congrArg _ hφ
    rw [e1, hq _ h1, hgen, map_mul heckeΨ, Module.End.mul_apply]
    rfl

p2m_export "CerednikDrinfeld.ToricUniformization" "sp_hecke_ringHom'"

private theorem _root_.CerednikDrinfeld.ToricUniformization.frobenius_toric' [Fact p.Prime] (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ r)
    (t : ↥𝒰.Tp) (ht : t ∈ 𝒰.toric) :
    𝒰.galTp φ t = 𝒰.heckeTp ((r : HeckeAlg) * heckeGen ⟨r, Fact.out⟩) t := by
  obtain ⟨v, hv, hπ⟩ := (𝒰.mem_toric_iff t).mp ht
  have hv'' : 𝒰.heckeU (heckeGen ⟨r, Fact.out⟩) v ∈ Submodule.torsionBy ℤ 𝒰.U (p : ℤ) := 𝒰.heckeU_mem_torsionBy _ hv
  obtain ⟨v', hgal, hχ⟩ := 𝒰.frob_toric φ hφ ⟨v, hv⟩
  have key : (v' : 𝒰.U) = (r : ℤ) • 𝒰.heckeU (heckeGen ⟨r, Fact.out⟩) v := by
    have h : v' = (r : ℤ) • ⟨𝒰.heckeU (heckeGen ⟨r, Fact.out⟩) v, hv''⟩ := by
      apply 𝒰.torsionEquiv.injective
      rw [map_zsmul, hχ]
      congr 1
      exact (𝒰.torsion_hecke ⟨r, Fact.out⟩ ⟨v, hv⟩ hv'').symm
    rw [h]
    rfl
  apply Subtype.ext
  show gal φ (t : T) = hecke ((r : HeckeAlg) * heckeGen ⟨r, Fact.out⟩) (t : T)
  rw [← hπ, show gal φ (𝒰.π v) = 𝒰.π v' from hgal, key, map_zsmul, 𝒰.π_hecke, map_mul hecke, Module.End.mul_apply,
    map_natCast, Module.End.natCast_apply, natCast_zsmul]

p2m_export "CerednikDrinfeld.ToricUniformization" "frobenius_toric'"

private theorem _root_.CerednikDrinfeld.ToricUniformization.frobenius_quot' (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ r)
    (t : ↥𝒰.Tp) : 𝒰.galTp φ t - 𝒰.heckeTp (heckeGen ⟨r, Fact.out⟩) t ∈ 𝒰.toric := by
  obtain ⟨u, hu⟩ := 𝒰.π_surj_torsion (t : T) t.2
  have hk := 𝒰.zsmul_lift_mem_ker t u hu
  have hpu : (p : ℤ) • u = (𝒰.periodEquiv (𝒰.periodEquiv.symm ⟨(p : ℤ) • u, hk⟩) : 𝒰.U) := by
    rw [AddEquiv.apply_symm_apply]
  obtain ⟨v, hv, hgal⟩ := 𝒰.frob_quot φ hφ u _ hpu
  have h2 : gal φ (𝒰.π u) = hecke (heckeGen ⟨r, Fact.out⟩) (𝒰.π u) + 𝒰.π v := by
    rw [← 𝒰.π_hecke]; exact hgal
  refine (𝒰.mem_toric_iff _).mpr ⟨v, (Submodule.mem_torsionBy_iff _ _).mpr hv, ?_⟩
  show 𝒰.π v = gal φ (t : T) - hecke (heckeGen ⟨r, Fact.out⟩) (t : T)
  rw [← hu, h2, add_sub_cancel_left]

p2m_export "CerednikDrinfeld.ToricUniformization" "frobenius_quot'"
end Laws
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization.InstFinite"

end ToricUniformization
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization.InstFinite P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization"

namespace JPrimeTorsionDatum p2m_export "CerednikDrinfeld.JPrimeTorsionDatum" "invariants comm pTorsion finiteLevel hecke toric instFinite T gal sp mk D toricEquiv H LocalLaws GoodReductionOutside" end JPrimeTorsionDatum
p2m_open_scoped "CerednikDrinfeld.JPrimeTorsionDatum" in

def JPrimeTorsionDatum.ofUniformization [Fact p.Prime] (𝒰 : ToricUniformization p r D H A hA T hecke gal)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t) :
    JPrimeTorsionDatum p E V A where
  D := D
  H := H
  T := ↥𝒰.Tp
  instFinite := 𝒰.finite_Tp
  pTorsion t := Subtype.ext t.2
  hecke := 𝒰.heckeTp
  gal := 𝒰.galTp
  comm σ x t := Subtype.ext (comm σ x t)
  finiteLevel := by
    obtain ⟨L, hL, h⟩ := finiteLevel
    exact ⟨L, hL, fun σ hσ => by ext t; exact h σ hσ t t.2⟩
  toric := 𝒰.toric
  toricEquiv := 𝒰.toricEquiv
  sp := 𝒰.sp

p2m_open_scoped "CerednikDrinfeld.JPrimeTorsionDatum" in

theorem JPrimeTorsionDatum.localLaws_ofUniformization [Fact p.Prime] (hpr : p ≠ r)
    (𝒰 : ToricUniformization p r D H A hA T hecke gal)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t) :
    (JPrimeTorsionDatum.ofUniformization 𝒰 comm finiteLevel).LocalLaws r where
  toric_hecke := 𝒰.toric_hecke'
  toricEquiv_hecke := 𝒰.toricEquiv_hecke'
  toric_le_invariants := fun t ht => 𝒰.toric_le_Inv t ht
  sp_eq_zero_iff := 𝒰.sp_eq_zero_iff'
  mem_range_sp_iff := 𝒰.mem_range_sp_iff'
  sp_hecke := 𝒰.sp_hecke'
  sp_hecke_ringHom := 𝒰.sp_hecke_ringHom' comm
  frobenius_toric := 𝒰.frobenius_toric'
  frobenius_quot := 𝒰.frobenius_quot'

namespace ToricUniformization
p2m_export "CerednikDrinfeld.ToricUniformization" "mk kummer frob_quot U torsionEquiv divisible frob_toric periodEquiv π_hecke period_adjoint torsion_hecke π_surj_torsion tame_surjective tame heckeU π"
p2m_open "CerednikDrinfeld.ToricUniformization"

variable [Fact p.Prime]

section TwoPlace

variable {M r₁ r₂ : ℕ} [Fact r₁.Prime] [Fact r₂.Prime]
  {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
  {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
  {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)} {hA₁ : A₁.LiesOverPrime r₁} {hA₂ : A₂.LiesOverPrime r₂}

def twoPlaceDatum
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t) :
    TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂ where
  T := ↥𝒰₁.Tp
  instFinite := (JPrimeTorsionDatum.ofUniformization 𝒰₁ comm finiteLevel).instFinite
  pTorsion t := Subtype.ext t.2
  hecke := 𝒰₁.heckeTp
  gal := 𝒰₁.galTp
  comm σ x t := Subtype.ext (comm σ x t)
  finiteLevel := by
    obtain ⟨L, hL, h⟩ := finiteLevel
    exact ⟨L, hL, fun σ hσ => by ext t; exact h σ hσ t t.2⟩
  toric₁ := 𝒰₁.toric
  toricEquiv₁ := 𝒰₁.toricEquiv
  sp₁ := 𝒰₁.sp
  toric₂ := 𝒰₂.toric
  toricEquiv₂ := 𝒰₂.toricEquiv
  sp₂ := 𝒰₂.sp

theorem twoPlaceDatum_fst
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t) :
    (twoPlaceDatum 𝒰₁ 𝒰₂ comm finiteLevel).fst = JPrimeTorsionDatum.ofUniformization 𝒰₁ comm finiteLevel := rfl

theorem twoPlaceDatum_snd
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t) :
    (twoPlaceDatum 𝒰₁ 𝒰₂ comm finiteLevel).snd = JPrimeTorsionDatum.ofUniformization 𝒰₂ comm finiteLevel := rfl

theorem goodReductionOutside_twoPlaceDatum
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t)
    (unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : T, p • t = 0 → gal σ t = t)
    (eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : T, p • t = 0 → gal σ (gal σ t) - hecke (heckeGen ⟨ℓ, hℓ⟩) (gal σ t) + ℓ • t = 0) :
    (twoPlaceDatum 𝒰₁ 𝒰₂ comm finiteLevel).fst.GoodReductionOutside M where
  unramified ℓ hℓ hM B hB σ hσ := by
    change 𝒰₁.galTp σ = 1
    ext t
    exact unramified ℓ hℓ hM B hB σ hσ (Subtype.val t) t.2
  eichlerShimura ℓ hℓ hM B hB σ hσ t := by
    revert t
    change ∀ t : ↥𝒰₁.Tp, 𝒰₁.galTp σ (𝒰₁.galTp σ t) - 𝒰₁.heckeTp (heckeGen ⟨ℓ, hℓ⟩) (𝒰₁.galTp σ t) + ℓ • t = 0
    intro t
    apply Subtype.ext
    rw [AddSubgroup.coe_add, AddSubgroup.coe_sub, AddSubgroupClass.coe_nsmul, ZeroMemClass.coe_zero]
    exact eichlerShimura ℓ hℓ hM B hB σ hσ (Subtype.val t) t.2

theorem twoPlaceDatum_laws (hpr₁ : p ≠ r₁) (hpr₂ : p ≠ r₂)
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t)
    (unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : T, p • t = 0 → gal σ t = t)
    (eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : T, p • t = 0 → gal σ (gal σ t) - hecke (heckeGen ⟨ℓ, hℓ⟩) (gal σ t) + ℓ • t = 0) :
    (twoPlaceDatum 𝒰₁ 𝒰₂ comm finiteLevel).Laws M r₁ r₂ where
  goodReduction := goodReductionOutside_twoPlaceDatum 𝒰₁ 𝒰₂ comm finiteLevel unramified eichlerShimura
  fst := by
    rw [twoPlaceDatum_fst]
    exact JPrimeTorsionDatum.localLaws_ofUniformization hpr₁ 𝒰₁ comm finiteLevel
  snd := by
    rw [twoPlaceDatum_snd]
    exact JPrimeTorsionDatum.localLaws_ofUniformization hpr₂ 𝒰₂ comm finiteLevel

end TwoPlace
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization.InstFinite P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization"

end ToricUniformization
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization.InstFinite P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization"

namespace TwoPlaceTorsionDatum p2m_export "CerednikDrinfeld.TwoPlaceTorsionDatum" "fst snd Laws toric₁ mk T toricEquiv₁ hecke finiteLevel toricEquiv₂ sp₂ pTorsion comm gal sp₁ toric₂ instFinite" end TwoPlaceTorsionDatum
p2m_open_scoped "CerednikDrinfeld.TwoPlaceTorsionDatum" in

theorem TwoPlaceTorsionDatum.exists_laws_of_toricUniformization'
    {p : ℕ} [Fact p.Prime] {M r₁ r₂ : ℕ} [Fact r₁.Prime] [Fact r₂.Prime] (hpr₁ : p ≠ r₁) (hpr₂ : p ≠ r₂)
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)} (hA₁ : A₁.LiesOverPrime r₁) (hA₂ : A₂.LiesOverPrime r₂)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t)
    (unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : T, p • t = 0 → gal σ t = t)
    (eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : T, p • t = 0 → gal σ (gal σ t) - hecke (heckeGen ⟨ℓ, hℓ⟩) (gal σ t) + ℓ • t = 0)
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal) :
    ∃ 𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂, 𝒥.Laws M r₁ r₂ :=
  ⟨ToricUniformization.twoPlaceDatum 𝒰₁ 𝒰₂ comm finiteLevel,
    ToricUniformization.twoPlaceDatum_laws hpr₁ hpr₂ 𝒰₁ 𝒰₂ comm finiteLevel unramified eichlerShimura⟩

end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization.InstFinite P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld"

theorem solution
    {p : ℕ} [Fact p.Prime] {M r₁ r₂ : ℕ} [Fact r₁.Prime] [Fact r₂.Prime] (hpr₁ : p ≠ r₁) (hpr₂ : p ≠ r₂)
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)} (hA₁ : A₁.LiesOverPrime r₁) (hA₂ : A₂.LiesOverPrime r₂)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T)
    (comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
      gal σ (hecke x t) = hecke x (gal σ t))
    (finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → ∀ t : T, p • t = 0 → gal σ t = t)
    (unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ t : T, p • t = 0 → gal σ t = t)
    (eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : T, p • t = 0 → gal σ (gal σ t) - hecke (heckeGen ⟨ℓ, hℓ⟩) (gal σ t) + ℓ • t = 0)
    (𝒰₁ : ToricUniformization p r₁ D₁ H₁ A₁ hA₁ T hecke gal) (𝒰₂ : ToricUniformization p r₂ D₂ H₂ A₂ hA₂ T hecke gal) :
    ∃ 𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂, 𝒥.Laws M r₁ r₂ :=
  CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_toricUniformization' hpr₁ hpr₂ hA₁ hA₂ T hecke gal comm finiteLevel
    unramified eichlerShimura 𝒰₁ 𝒰₂

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization.InstFinite P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld.ToricUniformization P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization.CerednikDrinfeld"

end S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization
end P2MW
export P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_toricUniformization (solution)
