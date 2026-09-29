-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e59335b4-da0b-56c1-ae86-0d0c35e3f670

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_existsUnique_quotientFamily_of_chartLaw
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_lift_of_valuationRing
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    (L : Type) [Field L] [Algebra V L] [IsFractionRing V L]
    (y : Spec (CommRingCat.of L) ⟶ Gl.Z n) (b : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hsq : Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ b = y ≫ Gl.zb n) :
    ∃ yV : Spec (CommRingCat.of V) ⟶ Gl.Z n, Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ yV = y ∧ yV ≫ Gl.zb n = b := by
  classical

  set φb : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* V := (Spec.preimage b).hom with hφb
  have hb : Spec.map (CommRingCat.ofHom φb) = b := by
    rw [hφb, CommRingCat.ofHom_hom, Spec.map_preimage]
  letI algV : Algebra 𝒪 V := (φb.comp (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}))).toAlgebra
  letI algL : Algebra 𝒪 L := ((algebraMap V L).comp (algebraMap 𝒪 V)).toAlgebra
  haveI : IsScalarTower 𝒪 V L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAV : ∀ a : 𝒪, algebraMap 𝒪 V a = φb (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) a) := fun _ => rfl
  have hπV : (algebraMap 𝒪 V π) ^ (n + 1) = 0 := by
    rw [hAV, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  have hπL : (algebraMap 𝒪 L π) ^ (n + 1) = 0 := by
    show ((algebraMap V L) (algebraMap 𝒪 V π)) ^ (n + 1) = 0
    rw [← map_pow, hπV, map_zero]
  have hV0 : algebraMap 𝒪 V π = 0 := pow_eq_zero_iff (Nat.succ_ne_zero n) |>.mp hπV

  obtain ⟨qf, hq_over, hq_nat, hq_chart, -⟩ :=
    CerednikDrinfeld.FormalOmega.MumfordGlue.existsUnique_quotientFamily_of_chartLaw 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl

  have key : ∃ P : DeligneDatum (K := K₀) π L, qf n L hπL P = y := by
    obtain ⟨S, hS⟩ := Gl.ζ_cover n
    obtain ⟨h, -, x0, hx0⟩ := hS (y.base default)
    have hrange : Set.range y.base ⊆ Set.range (Gl.ζ h n).base := by
      rintro _ ⟨p, rfl⟩
      rw [Subsingleton.elim p default]
      exact ⟨x0, hx0⟩
    haveI := Gl.ζ_isOpenImmersion h n
    set y' := IsOpenImmersion.lift (Gl.ζ h n) y hrange with hy'def
    have hy' : y' ≫ Gl.ζ h n = y := IsOpenImmersion.lift_fac _ _ _
    set xqR : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) →+* L := (Spec.preimage y').hom with hxqR
    have hxq : Spec.map (CommRingCat.ofHom xqR) = y' := by
      rw [hxqR, CommRingCat.ofHom_hom, Spec.map_preimage]

    have hSpecL : Spec.map (CommRingCat.ofHom (algebraMap 𝒪 L)) =
        Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ b ≫
          Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) := by
      rw [← hb, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    have hcompat : xqR.comp (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) = algebraMap 𝒪 L := by
      have h1 : Spec.map (CommRingCat.ofHom (xqR.comp (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))) =
          Spec.map (CommRingCat.ofHom (algebraMap 𝒪 L)) := by
        rw [hSpecL, ← Category.assoc, hsq, ← hy', Category.assoc, Category.assoc, Gl.ζ_over h n, ← hxq,
          ← Spec.map_comp]
        rfl
      have h2 := Spec.map_injective h1
      exact congrArg CommRingCat.Hom.hom h2
    let xq : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) →ₐ[𝒪] L :=
      { toRingHom := xqR
        commutes' := fun a => by
          have := congrArg (fun f : 𝒪 →+* L => f a) hcompat
          simpa using this }
    obtain ⟨d, hd1, hd2, hd3⟩ :=
      CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (K := K₀) π hπ r hres g₁ hg₁ L
        ⟨n + 1, hπL⟩ (xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
    refine ⟨DeligneDatum.pullback π L h⁻¹ d, ?_⟩
    rw [hq_chart n L hπL h xq d _ ⟨hd1, hd2, hd3⟩ (DeligneDatum.isPullback_pullback π L h⁻¹ d), ← hy', ← hxq]
  obtain ⟨P_L, hP_L⟩ := key

  obtain ⟨P_V, hbc⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero (K := K₀) π hπ V hV0 L P_L
  have hmap : (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 V L) P_V = P_L := by
    apply DeligneDatum.ext'
    funext M
    exact (hbc M).symm
  refine ⟨qf n V hπV P_V, ?_, ?_⟩
  · have := hq_nat n V L hπV hπL (IsScalarTower.toAlgHom 𝒪 V L) P_V
    rw [hmap, hP_L] at this
    rw [this]
    rfl
  · have h1 := hq_over n V hπV P_V
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap 𝒪 V)) =
        b ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) := by
      rw [← hb, ← Spec.map_comp]
      rfl
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc, h1, h2]

end S_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_lift_of_valuationRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_lift_of_valuationRing (solution)
