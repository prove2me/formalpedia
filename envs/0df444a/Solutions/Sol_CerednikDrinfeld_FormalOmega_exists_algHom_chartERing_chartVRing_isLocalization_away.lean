-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_algHom_chartERing_chartVRing_isLocalization_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d89a6b23-2dbf-5e93-bf7e-8bdad11c9530

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_algHom_chartERing_chartVRing_isLocalization_away

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace VertexInEdgeAux

noncomputable section

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (n : ℕ)

theorem ringHom_ext_E {T : Type} [CommRing T] {g₁ g₂ : chartERing 𝒪 π r →+* T}
    (h : g₁.comp (algebraMap 𝒪 (chartERing 𝒪 π r)) = g₂.comp (algebraMap 𝒪 (chartERing 𝒪 π r)))
    (hξ : g₁ (chartERing.ξ 𝒪 π r) = g₂ (chartERing.ξ 𝒪 π r))
    (hη : g₁ (chartERing.η 𝒪 π r) = g₂ (chartERing.η 𝒪 π r)) : g₁ = g₂ := by
  letI : Algebra 𝒪 T := (g₁.comp (algebraMap 𝒪 (chartERing 𝒪 π r))).toAlgebra
  let a₁ : chartERing 𝒪 π r →ₐ[𝒪] T := ⟨g₁, fun _ => rfl⟩
  let a₂ : chartERing 𝒪 π r →ₐ[𝒪] T := ⟨g₂, fun x => (RingHom.congr_fun h x).symm⟩
  have h12 : a₁ = a₂ :=
    (chartERing.corepEquiv 𝒪 π r T).injective (Subtype.ext (Prod.ext (by exact hξ) (by exact hη)))
  exact RingHom.ext fun z => AlgHom.congr_fun h12 z

theorem ringHom_ext_V {T : Type} [CommRing T] {g₁ g₂ : chartVRing 𝒪 r →+* T}
    (h : g₁.comp (algebraMap 𝒪 (chartVRing 𝒪 r)) = g₂.comp (algebraMap 𝒪 (chartVRing 𝒪 r)))
    (hζ : g₁ (chartVRing.ζ 𝒪 r) = g₂ (chartVRing.ζ 𝒪 r)) : g₁ = g₂ := by
  letI : Algebra 𝒪 T := (g₁.comp (algebraMap 𝒪 (chartVRing 𝒪 r))).toAlgebra
  let a₁ : chartVRing 𝒪 r →ₐ[𝒪] T := ⟨g₁, fun _ => rfl⟩
  let a₂ : chartVRing 𝒪 r →ₐ[𝒪] T := ⟨g₂, fun x => (RingHom.congr_fun h x).symm⟩
  have h12 : a₁ = a₂ :=
    (chartVRing.corepEquiv 𝒪 r T).injective (Subtype.ext (by exact hζ))
  exact RingHom.ext fun z => AlgHom.congr_fun h12 z

abbrev IE : Ideal (chartERing 𝒪 π r) := Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}

abbrev IV : Ideal (chartVRing 𝒪 r) := Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}

abbrev An : Type := chartERing 𝒪 π r ⧸ IE 𝒪 π r n

abbrev Pn : Type := chartVRing 𝒪 r ⧸ IV 𝒪 π r n

abbrev ξb : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)

abbrev ηb : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)

abbrev ζb : Pn 𝒪 π r n := Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)

theorem algebraMap_An_pow_eq_zero : (algebraMap 𝒪 (An 𝒪 π r n) π) ^ (n + 1) = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem algebraMap_Pn_pow_eq_zero : (algebraMap 𝒪 (Pn 𝒪 π r n) π) ^ (n + 1) = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem isNilpotent_algebraMap_Pn : IsNilpotent (algebraMap 𝒪 (Pn 𝒪 π r n) π) :=
  ⟨n + 1, algebraMap_Pn_pow_eq_zero 𝒪 π r n⟩

theorem isUnit_ζ (hr : 1 ≤ r) : IsUnit (chartVRing.ζ 𝒪 r) := by
  have h := chartVRing.isUnit_ζ_pow_sub 𝒪 r
  have hpow : chartVRing.ζ 𝒪 r ^ r = chartVRing.ζ 𝒪 r * chartVRing.ζ 𝒪 r ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  have hfac : chartVRing.ζ 𝒪 r ^ r - chartVRing.ζ 𝒪 r =
      chartVRing.ζ 𝒪 r * (chartVRing.ζ 𝒪 r ^ (r - 1) - 1) := by
    rw [hpow]; ring
  rw [hfac] at h
  exact isUnit_of_mul_isUnit_left h

theorem isUnit_ξ_pow_sub_one : IsUnit (chartERing.ξ 𝒪 π r ^ (r - 1) - 1) :=
  isUnit_of_mul_isUnit_left (chartERing.isUnit_discr 𝒪 π r)

theorem isUnit_ζb (hr : 1 ≤ r) : IsUnit (ζb 𝒪 π r n) := (isUnit_ζ 𝒪 r hr).map _

theorem isUnit_ζb_pow_sub : IsUnit (ζb 𝒪 π r n ^ r - ζb 𝒪 π r n) := by
  have h := (chartVRing.isUnit_ζ_pow_sub 𝒪 r).map (Ideal.Quotient.mk (IV 𝒪 π r n))
  rwa [map_sub, map_pow] at h

def xV (hr : 1 ≤ r) : (chartVUnit 𝒪 r).obj (Pn 𝒪 π r n) :=
  ⟨ζb 𝒪 π r n, isUnit_ζb_pow_sub 𝒪 π r n, isUnit_ζb 𝒪 π r n hr⟩

def xE (hr : 2 ≤ r) : (chartE 𝒪 π r).obj (Pn 𝒪 π r n) :=
  vertexToEdge π hr (Pn 𝒪 π r n) (isNilpotent_algebraMap_Pn 𝒪 π r n) (xV 𝒪 π r n (le_trans one_le_two hr))

def ι₀ (hr : 2 ≤ r) : chartERing 𝒪 π r →ₐ[𝒪] Pn 𝒪 π r n := chartERing.lift (xE 𝒪 π r n hr)

theorem ι₀_ξ (hr : 2 ≤ r) : ι₀ 𝒪 π r n hr (chartERing.ξ 𝒪 π r) = ζb 𝒪 π r n := chartERing.lift_ξ _

theorem ι₀_η (hr : 2 ≤ r) : ι₀ 𝒪 π r n hr (chartERing.η 𝒪 π r) =
    algebraMap 𝒪 (Pn 𝒪 π r n) π * ↑((isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).unit⁻¹) :=
  chartERing.lift_η _

theorem ι₀_η_mul_ζb (hr : 2 ≤ r) : ι₀ 𝒪 π r n hr (chartERing.η 𝒪 π r) * ζb 𝒪 π r n =
    algebraMap 𝒪 (Pn 𝒪 π r n) π := by
  rw [ι₀_η, mul_assoc]
  have : (↑((isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).unit⁻¹) : Pn 𝒪 π r n) * ζb 𝒪 π r n = 1 :=
    (isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).val_inv_mul
  rw [this, mul_one]

theorem ι₀_vanishes (hr : 2 ≤ r) : ∀ a ∈ IE 𝒪 π r n, ι₀ 𝒪 π r n hr a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_pow, AlgHom.commutes, algebraMap_Pn_pow_eq_zero, mul_zero]

def ι (hr : 2 ≤ r) : An 𝒪 π r n →ₐ[𝒪] Pn 𝒪 π r n :=
  Ideal.Quotient.liftₐ (IE 𝒪 π r n) (ι₀ 𝒪 π r n hr) (ι₀_vanishes 𝒪 π r n hr)

theorem ι_mk (hr : 2 ≤ r) (a : chartERing 𝒪 π r) :
    ι 𝒪 π r n hr (Ideal.Quotient.mk _ a) = ι₀ 𝒪 π r n hr a := by
  rw [ι, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem ι_ξb (hr : 2 ≤ r) : ι 𝒪 π r n hr (ξb 𝒪 π r n) = ζb 𝒪 π r n := by
  rw [ξb, ι_mk, ι₀_ξ]

theorem ι_ηb_mul_ζb (hr : 2 ≤ r) : ι 𝒪 π r n hr (ηb 𝒪 π r n) * ζb 𝒪 π r n = algebraMap 𝒪 (Pn 𝒪 π r n) π := by
  rw [ηb, ι_mk, ι₀_η_mul_ζb]

abbrev L : Type := Localization.Away (ξb 𝒪 π r n)

theorem isUnit_pow_sub_algebraMap_ξb (hr : 1 ≤ r) :
    IsUnit ((algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n)) ^ r -
      algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n)) := by
  set z := algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n) with hz
  have hzU : IsUnit z := IsLocalization.Away.algebraMap_isUnit (ξb 𝒪 π r n)
  have h2 : IsUnit (z ^ (r - 1) - 1) := by
    have h := ((isUnit_ξ_pow_sub_one 𝒪 π r).map (Ideal.Quotient.mk (IE 𝒪 π r n))).map
      (algebraMap (An 𝒪 π r n) (L 𝒪 π r n))
    rwa [map_sub, map_pow, map_one, map_sub, map_pow, map_one] at h
  have hpow : z ^ r = z * z ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  have hfac : z ^ r - z = z * (z ^ (r - 1) - 1) := by
    rw [hpow]; ring
  rw [hfac]
  exact hzU.mul h2

def g₀ (hr : 1 ≤ r) : chartVRing 𝒪 r →ₐ[𝒪] L 𝒪 π r n :=
  chartVRing.lift ⟨algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n), isUnit_pow_sub_algebraMap_ξb 𝒪 π r n hr⟩

theorem g₀_ζ (hr : 1 ≤ r) :
    g₀ 𝒪 π r n hr (chartVRing.ζ 𝒪 r) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n) :=
  chartVRing.lift_ζ _

theorem g₀_vanishes (hr : 1 ≤ r) : ∀ a ∈ IV 𝒪 π r n, g₀ 𝒪 π r n hr a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_pow, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝒪 (An 𝒪 π r n) (L 𝒪 π r n),
    ← map_pow, algebraMap_An_pow_eq_zero, map_zero, mul_zero]

def g (hr : 1 ≤ r) : Pn 𝒪 π r n →ₐ[𝒪] L 𝒪 π r n :=
  Ideal.Quotient.liftₐ (IV 𝒪 π r n) (g₀ 𝒪 π r n hr) (g₀_vanishes 𝒪 π r n hr)

theorem g_mk (hr : 1 ≤ r) (a : chartVRing 𝒪 r) :
    g 𝒪 π r n hr (Ideal.Quotient.mk _ a) = g₀ 𝒪 π r n hr a := by
  rw [g, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem g_ζb (hr : 1 ≤ r) :
    g 𝒪 π r n hr (ζb 𝒪 π r n) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n) := by
  rw [ζb, g_mk, g₀_ζ]

theorem isUnit_ι_ξb (hr : 2 ≤ r) : IsUnit ((ι 𝒪 π r n hr).toRingHom (ξb 𝒪 π r n)) := by
  show IsUnit (ι 𝒪 π r n hr (ξb 𝒪 π r n))
  rw [ι_ξb]
  exact isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)

def f (hr : 2 ≤ r) : L 𝒪 π r n →+* Pn 𝒪 π r n :=
  IsLocalization.Away.lift (ξb 𝒪 π r n) (isUnit_ι_ξb 𝒪 π r n hr)

theorem f_algebraMap (hr : 2 ≤ r) (a : An 𝒪 π r n) :
    f 𝒪 π r n hr (algebraMap (An 𝒪 π r n) (L 𝒪 π r n) a) = ι 𝒪 π r n hr a :=
  IsLocalization.Away.lift_eq _ _ a

theorem g_comp_ι (hr : 2 ≤ r) :
    (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom.comp (ι 𝒪 π r n hr).toRingHom =
      algebraMap (An 𝒪 π r n) (L 𝒪 π r n) := by
  apply Ideal.Quotient.ringHom_ext
  apply ringHom_ext_E 𝒪 π r
  · ext x
    show g 𝒪 π r n _ (ι 𝒪 π r n hr (Ideal.Quotient.mk _ (algebraMap 𝒪 (chartERing 𝒪 π r) x))) =
      algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (Ideal.Quotient.mk _ (algebraMap 𝒪 (chartERing 𝒪 π r) x))
    rw [Ideal.Quotient.mk_algebraMap, AlgHom.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply 𝒪 (An 𝒪 π r n) (L 𝒪 π r n)]
  · show g 𝒪 π r n _ (ι 𝒪 π r n hr (ξb 𝒪 π r n)) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n)
    rw [ι_ξb, g_ζb]
  · show g 𝒪 π r n _ (ι 𝒪 π r n hr (ηb 𝒪 π r n)) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ηb 𝒪 π r n)

    have hU : IsUnit (g 𝒪 π r n (le_trans one_le_two hr) (ζb 𝒪 π r n)) :=
      (isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).map _
    have h1 : g 𝒪 π r n (le_trans one_le_two hr) (ι 𝒪 π r n hr (ηb 𝒪 π r n)) *
        g 𝒪 π r n (le_trans one_le_two hr) (ζb 𝒪 π r n) = algebraMap 𝒪 (L 𝒪 π r n) π := by
      rw [← map_mul, ι_ηb_mul_ζb, AlgHom.commutes]
    have h2 : algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ηb 𝒪 π r n) *
        g 𝒪 π r n (le_trans one_le_two hr) (ζb 𝒪 π r n) = algebraMap 𝒪 (L 𝒪 π r n) π := by
      rw [g_ζb, ← map_mul]
      have : ηb 𝒪 π r n * ξb 𝒪 π r n = algebraMap 𝒪 (An 𝒪 π r n) π := by
        rw [ηb, ξb, ← map_mul, mul_comm, chartERing.ξ_mul_η, Ideal.Quotient.mk_algebraMap]
      rw [this, ← IsScalarTower.algebraMap_apply]
    exact (IsUnit.mul_left_injective hU) (h1.trans h2.symm)

theorem g_comp_f (hr : 2 ≤ r) :
    (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom.comp (f 𝒪 π r n hr) = RingHom.id (L 𝒪 π r n) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ξb 𝒪 π r n))
  rw [RingHom.comp_assoc, f, IsLocalization.Away.lift_comp, RingHom.id_comp]
  exact g_comp_ι 𝒪 π r n hr

theorem f_comp_g (hr : 2 ≤ r) :
    (f 𝒪 π r n hr).comp (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom = RingHom.id (Pn 𝒪 π r n) := by
  apply Ideal.Quotient.ringHom_ext
  apply ringHom_ext_V 𝒪 r
  · ext x
    show f 𝒪 π r n hr (g 𝒪 π r n _ (Ideal.Quotient.mk _ (algebraMap 𝒪 (chartVRing 𝒪 r) x))) =
      Ideal.Quotient.mk _ (algebraMap 𝒪 (chartVRing 𝒪 r) x)
    rw [Ideal.Quotient.mk_algebraMap, AlgHom.commutes,
      IsScalarTower.algebraMap_apply 𝒪 (An 𝒪 π r n) (L 𝒪 π r n), f_algebraMap, AlgHom.commutes]
  · show f 𝒪 π r n hr (g 𝒪 π r n _ (ζb 𝒪 π r n)) = ζb 𝒪 π r n
    rw [g_ζb, f_algebraMap, ι_ξb]

def e (hr : 2 ≤ r) : L 𝒪 π r n ≃+* Pn 𝒪 π r n :=
  RingEquiv.ofRingHom (f 𝒪 π r n hr) (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom
    (f_comp_g 𝒪 π r n hr) (g_comp_f 𝒪 π r n hr)

theorem isLocalization_away (hr : 2 ≤ r) :
    @IsLocalization.Away (An 𝒪 π r n) _ (ξb 𝒪 π r n) (Pn 𝒪 π r n) _ (ι 𝒪 π r n hr).toRingHom.toAlgebra := by
  letI : Algebra (An 𝒪 π r n) (Pn 𝒪 π r n) := (ι 𝒪 π r n hr).toRingHom.toAlgebra
  let e' : L 𝒪 π r n ≃ₐ[An 𝒪 π r n] Pn 𝒪 π r n :=
    AlgEquiv.ofRingEquiv (f := e 𝒪 π r n hr) (fun a => f_algebraMap 𝒪 π r n hr a)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (ξb 𝒪 π r n)) e'

end

end VertexInEdgeAux

open VertexInEdgeAux in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) {r : ℕ} [Fact r.Prime] (n : ℕ) :
    ∃ ι : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}),
      ι (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) = Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r) ∧
      ι (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)) * Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r) = algebraMap 𝒪 (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) π ∧
      @IsLocalization.Away ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) _ (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) _ ι.toRingHom.toAlgebra := by
  have hr : 2 ≤ r := (Fact.out : r.Prime).two_le
  exact ⟨VertexInEdgeAux.ι 𝒪 π r n hr, ι_ξb 𝒪 π r n hr, ι_ηb_mul_ζb 𝒪 π r n hr, isLocalization_away 𝒪 π r n hr⟩

end S_CerednikDrinfeld_FormalOmega_exists_algHom_chartERing_chartVRing_isLocalization_away
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_algHom_chartERing_chartVRing_isLocalization_away (solution)
