-- Prove2me | solution 1 for CerednikDrinfeld.Omega.pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/660a8099-ca25-5e21-b457-9e81c3b7ce67

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_eq_of_toValuationSubring_le
import Theorems.Thm_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace NatOmegaPLA

theorem deg_eq_one
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)]
    (L : Subgroup G) (F₁ : Type) [Field F₁] [Algebra K F₁] (e₁ : F₁ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L))
    (pt₁ : ↥(Omega.upperHalfPlane K₀ K) → Place K F₁)
    (hpt₁ : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : F₁),
        x ∈ (pt₁ z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((e₁ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt₁ z).evalAt (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt₁ z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))))
    (z : ↥(Omega.upperHalfPlane K₀ K)) : (pt₁ z).deg = 1 := by
  classical
  let ι₁ : F₁ →+* FractionRing (Omega.HolRingOf ϖ ρ) := (Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L).subtype.comp (e₁ : F₁ →ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L)).toRingHom
  have hι₁ : ∀ x : F₁, ι₁ x = ((e₁ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L)) : FractionRing (Omega.HolRingOf ϖ ρ)) := fun x => rfl
  have hι₁inj : Function.Injective ι₁ := (Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L).subtype_injective.comp e₁.injective
  have hrat : Function.Surjective (algebraMap K (pt₁ z).ResidueField) := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨g', h', hh, hhz, hxe⟩ := (hpt₁.1 z (a : F₁)).mp a.2
    rw [← hι₁] at hxe
    set gz : K := (show ↥(Omega.holRing ϖ) from g' : ↥(Omega.upperHalfPlane K₀ K) → K) z with hgz
    set hz : K := (show ↥(Omega.holRing ϖ) from h' : ↥(Omega.upperHalfPlane K₀ K) → K) z with hhzdef
    refine ⟨gz / hz, ?_⟩
    have hsub : a - algebraMap K _ (gz / hz) ∈ IsLocalRing.maximalIdeal ↥(pt₁ z).toValuationSubring := by
      rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
      let c' : Omega.HolRingOf ϖ ρ := algebraMap K (Omega.HolRingOf ϖ ρ) (gz / hz)
      have hmem1 : (1 : Omega.HolRingOf ϖ ρ) ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ) := one_mem _
      have hcoe : ι₁ (((a - algebraMap K _ (gz / hz) : ↥(pt₁ z).toValuationSubring) : F₁)) =
          Localization.mk (↑(⟨(1 : Omega.HolRingOf ϖ ρ), hmem1⟩ : ↥(nonZeroDivisors (Omega.HolRingOf ϖ ρ))) * g' - ↑(⟨h', hh⟩ : ↥(nonZeroDivisors (Omega.HolRingOf ϖ ρ))) * c') (⟨h', hh⟩ * ⟨1, hmem1⟩) := by
        rw [← Localization.sub_mk, ← hxe]
        simp only [AddSubgroupClass.coe_sub, map_sub, c']
        congr 1
        rw [hι₁]
        show ((e₁ (algebraMap K F₁ (gz / hz)) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk _ 1
        rw [AlgEquiv.commutes, Localization.mk_algebraMap]
        rfl
      have hx' : Localization.mk (↑(⟨(1 : Omega.HolRingOf ϖ ρ), hmem1⟩ : ↥(nonZeroDivisors (Omega.HolRingOf ϖ ρ))) * g' - ↑(⟨h', hh⟩ : ↥(nonZeroDivisors (Omega.HolRingOf ϖ ρ))) * c') (⟨h', hh⟩ * ⟨1, hmem1⟩) ∈
          Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) L := by
        rw [← hcoe, hι₁]; exact Subtype.coe_prop _
      have key := (hpt₁.2 z _ _ (mul_mem hh hmem1) hx' ?_).2
      · have : ((a - algebraMap K _ (gz / hz) : ↥(pt₁ z).toValuationSubring) : F₁) = e₁.symm ⟨_, hx'⟩ := by
          apply hι₁inj
          rw [hcoe, hι₁, AlgEquiv.apply_symm_apply]
        rw [this]
        apply key.mpr
        change ((1 : ↥(Omega.upperHalfPlane K₀ K) → K) * (show ↥(Omega.holRing ϖ) from g' : ↥(Omega.upperHalfPlane K₀ K) → K) -
          (show ↥(Omega.holRing ϖ) from h' : ↥(Omega.upperHalfPlane K₀ K) → K) *
            ((algebraMap K ↥(Omega.holRing ϖ) (gz / hz) : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K)) z = 0
        simp only [Pi.sub_apply, Pi.mul_apply, Pi.one_apply, Omega.algebraMap_holRing_apply]
        rw [← hgz, ← hhzdef]
        field_simp
        ring
      · change ((show ↥(Omega.holRing ϖ) from h' : ↥(Omega.upperHalfPlane K₀ K) → K) * (1 : ↥(Omega.upperHalfPlane K₀ K) → K)) z ≠ 0
        simpa only [Pi.mul_apply, Pi.one_apply, mul_one] using hhz
    rw [IsScalarTower.algebraMap_apply K ↥(pt₁ z).toValuationSubring (pt₁ z).ResidueField]
    exact ((Ideal.Quotient.eq).mpr hsub).symm
  have hdeg1 : (pt₁ z).deg = 1 := by
    unfold Place.deg
    have e : K ≃ₗ[K] (pt₁ z).ResidueField :=
      LinearEquiv.ofBijective (Algebra.linearMap K (pt₁ z).ResidueField)
        ⟨(algebraMap K (pt₁ z).ResidueField).injective, hrat⟩
    rw [← e.finrank_eq, Module.finrank_self]
  exact hdeg1

end NatOmegaPLA

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Λ₁ Λ₂ : Subgroup G) (hΛ : Λ₁ ≤ Λ₂)

    (F₁ : Type) [Field F₁] [Algebra K F₁] (e₁ : F₁ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁))
    (F₂ : Type) [Field F₂] [Algebra K F₂] (e₂ : F₂ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂))
    (φ : F₂ →ₐ[K] F₁)
    (hφ : ∀ x : F₂, ((e₁ (φ x) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) = ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : φ.toRingHom.IsIntegral)

    (pt₁ : ↥(Omega.upperHalfPlane K₀ K) → Place K F₁)
    (hpt₁ : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : F₁),
        x ∈ (pt₁ z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((e₁ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt₁ z).evalAt (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt₁ z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))))
    (pt₂ : ↥(Omega.upperHalfPlane K₀ K) → Place K F₂)
    (hpt₂ : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : F₂),
        x ∈ (pt₂ z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt₂ z).evalAt (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt₂ z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))))

    (hfib₁ : ∀ z z' : ↥(Omega.upperHalfPlane K₀ K), pt₁ z = pt₁ z' ↔ ∃ γ : ↥(Λ₁.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hfib₂ : ∀ z z' : ↥(Omega.upperHalfPlane K₀ K), pt₂ z = pt₂ z' ↔ ∃ γ : ↥(Λ₂.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hsurj₁ : Function.Surjective pt₁)

    [(Λ₁.subgroupOf Λ₂).FiniteIndex] [Fintype (↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂)]
    (s : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂ → ↥Λ₂)
    (hs : ∀ q, (QuotientGroup.mk (s q) : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂) = q)
    [IsCurveOver K F₁]

    (hord₁ : (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
      (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁),
      (pt₁ z).ord (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) *
          (Nat.card ↥(MulAction.stabilizer ↥(Λ₁.map ρ) z) : ℤ) =
        (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h) z : ℤ)))
    (hord₂ : (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
      (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂),
      (pt₂ z).ord (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) *
          (Nat.card ↥(MulAction.stabilizer ↥(Λ₂.map ρ) z) : ℤ) =
        (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h) z : ℤ)))
    (hker : ∀ γ : G, γ ∈ Λ₂ → ρ γ = 1 → γ ∈ Λ₁)

    (hFI : FundamentalIdentityAlong K φ hφC)
    (hdeg : finrankAlong K φ = Fintype.card (↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂))
    (z : ↥(Omega.upperHalfPlane K₀ K)) [Finite ↥(MulAction.stabilizer ↥(Λ₂.map ρ) z)] :
    Divisor.pullbackAlong φ hφC (Finsupp.single (pt₂ z) 1) =
      ∑ q : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂, Finsupp.single (pt₁ ((ρ ((s q : ↥Λ₂) : G))⁻¹ • z)) 1 := by
  classical
  letI instA : Algebra F₂ F₁ := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφC

  have hres : ∀ w₀ : ↥(Omega.upperHalfPlane K₀ K), (pt₁ w₀).restrictAlong φ hφC = pt₂ w₀ := by
    intro w₀
    have h := (Omega.restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff K₀ K ϖ G ρ Λ₁ Λ₂
      F₁ e₁ F₂ e₂ (1 : G) φ (fun x => by rw [one_smul]; exact hφ x) hφC pt₁ hpt₁ pt₂ hpt₂ w₀).1
    rwa [map_one, inv_one, one_smul] at h

  let V : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂ → Place K F₁ := fun q => pt₁ ((ρ ((s q : ↥Λ₂) : G))⁻¹ • z)

  have hVover : ∀ q, (V q).restrictAlong φ hφC = pt₂ z := by
    intro q
    rw [hres]
    exact ((hfib₂ z _).mpr ⟨⟨(ρ ((s q : ↥Λ₂) : G))⁻¹, by rw [← map_inv]; exact Subgroup.mem_map_of_mem _ (Λ₂.inv_mem (s q).2)⟩, rfl⟩).symm

  have hVsurj : ∀ w : Place K F₁, w.restrictAlong φ hφC = pt₂ z → ∃ q, V q = w := by
    intro w hw
    obtain ⟨w₀, rfl⟩ := hsurj₁ w
    rw [hres] at hw

    obtain ⟨γ', hw₀'⟩ := (hfib₂ z w₀).mp hw.symm
    obtain ⟨γ, hγ, hγρ⟩ := Subgroup.mem_map.mp γ'.2
    have hw₀ : w₀ = ρ γ • z := by rw [hw₀', ← hγρ]
    refine ⟨QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : ↥Λ₂), ?_⟩

    have hq := hs (QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : ↥Λ₂))
    have hlam0 : ((⟨γ, hγ⟩ : ↥Λ₂) * s (QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : ↥Λ₂)) : ↥Λ₂) ∈ Λ₁.subgroupOf Λ₂ := by
      have := (QuotientGroup.eq (s := Λ₁.subgroupOf Λ₂)).mp hq.symm
      simpa using this
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hlam0
    show pt₁ _ = pt₁ w₀
    apply (hfib₁ _ _).mpr
    refine ⟨⟨ρ (γ * ((s (QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : ↥Λ₂)) : ↥Λ₂) : G)), Subgroup.mem_map_of_mem _ hlam0⟩, ?_⟩
    show w₀ = ρ (γ * ((s (QuotientGroup.mk (⟨γ, hγ⟩⁻¹ : ↥Λ₂)) : ↥Λ₂) : G)) • _
    rw [hw₀, map_mul, mul_smul, smul_inv_smul]

  have hfiber : (pt₂ z).fiber F₁ = Finset.univ.image V := by
    ext w
    rw [Place.mem_fiber, Finset.mem_image]
    constructor
    · intro hw
      obtain ⟨q, rfl⟩ := hVsurj w hw
      exact ⟨q, Finset.mem_univ _, rfl⟩
    · rintro ⟨q, -, rfl⟩
      exact hVover q

  have hrat₁ : ∀ w₀ : ↥(Omega.upperHalfPlane K₀ K), (pt₁ w₀).deg = 1 :=
    fun w₀ => NatOmegaPLA.deg_eq_one K₀ K ϖ G ρ Λ₁ F₁ e₁ pt₁ hpt₁ w₀
  have hrat₂ : (pt₂ z).deg = 1 := NatOmegaPLA.deg_eq_one K₀ K ϖ G ρ Λ₂ F₂ e₂ pt₂ hpt₂ z

  set E := Divisor.pullbackAlong φ hφC (Finsupp.single (pt₂ z) 1) with hE
  have hEapply_of : ∀ q, E (V q) = ((V q).ramificationIndex F₂ : ℤ) := by
    intro q
    rw [hE]
    show Divisor.pullback F₁ (Finsupp.single (pt₂ z) 1) (V q) = _
    rw [Divisor.pullback_single_apply_of_restrict_eq (hVover q), one_mul]
  have hEapply_off : ∀ w, w.restrictAlong φ hφC ≠ pt₂ z → E w = 0 := by
    intro w hw
    rw [hE]
    show Divisor.pullback F₁ (Finsupp.single (pt₂ z) 1) w = _
    exact Divisor.pullback_single_apply_of_restrict_ne hw 1

  have hSfin : ∀ q₀ : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂, Finite ↥(MulAction.stabilizer ↥(Λ₂.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) := by
    intro q₀
    have hmem : (ρ ((s q₀ : ↥Λ₂) : G))⁻¹ ∈ Λ₂.map ρ := by
      rw [← map_inv]; exact Subgroup.mem_map_of_mem _ (Λ₂.inv_mem (s q₀).2)
    have heq : (ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z = (⟨(ρ ((s q₀ : ↥Λ₂) : G))⁻¹, hmem⟩ : ↥(Λ₂.map ρ)) • z := rfl
    rw [heq, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    apply Set.Finite.to_subtype
    rw [Subgroup.coe_map]
    exact (Set.toFinite _).image _

  have hram : ∀ q₀ : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂,
      ((V q₀).ramificationIndex F₂ : ℤ) * (Nat.card ↥(MulAction.stabilizer ↥(Λ₁.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) : ℤ) =
        (Nat.card ↥(MulAction.stabilizer ↥(Λ₂.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) : ℤ) := by
    intro q₀
    set u : ↥(Omega.upperHalfPlane K₀ K) := (ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z with hu
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(pt₂ u).toValuationSubring
    have hordπ : (pt₂ u).ord (π : F₂) = 1 := (pt₂ u).ord_coe_irreducible hπ
    obtain ⟨⟨g, ⟨h, hh⟩⟩, hgh⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (Omega.HolRingOf ϖ ρ)) ((e₂ (π : F₂) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ))
    have hmk : ((e₂ (π : F₂) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩ := by
      rw [Localization.mk_eq_mk']; exact hgh.symm
    have hπ0 : (π : F₂) ≠ 0 := by
      intro h0
      have := hordπ
      rw [h0, Place.ord_zero] at this
      exact zero_ne_one this
    have hg : g ≠ 0 := by
      intro hg0
      apply hπ0
      have : ((e₂ (π : F₂) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)) = 0 := by
        rw [hmk, hg0, Localization.mk_zero]
      have h1 : e₂ (π : F₂) = 0 := by exact_mod_cast this
      exact (map_eq_zero_iff e₂ e₂.injective).mp h1
    have hx₂ : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂ := hmk ▸ (e₂ (π : F₂)).2
    have hx₁ : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁ := by
      rw [← hmk, ← hφ]; exact (e₁ (φ (π : F₂))).2
    have e2 := hord₂ u g h hg hh hx₂
    have e1 := hord₁ u g h hg hh hx₁
    have hx₂' : e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx₂⟩ = (π : F₂) := by
      rw [AlgEquiv.symm_apply_eq]; exact Subtype.ext hmk.symm
    have hx₁' : e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx₁⟩ = φ (π : F₂) := by
      rw [AlgEquiv.symm_apply_eq]; exact Subtype.ext (by rw [hφ, hmk])
    rw [hx₂', hordπ, one_mul] at e2
    rw [hx₁', Place.ord_restrictAlong φ hφC, hres, hordπ, mul_one] at e1
    rw [e2, ← e1]
    rfl

  have hinj : ∀ q₀ : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂,
      (Finset.univ.filter (fun q => V q = V q₀)).card * Nat.card ↥(MulAction.stabilizer ↥(Λ₁.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) ≤
        Nat.card ↥(MulAction.stabilizer ↥(Λ₂.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) := by
    intro q₀
    haveI := hSfin q₀
    set u : ↥(Omega.upperHalfPlane K₀ K) := (ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z with hu

    have hch : ∀ t : {q : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂ // V q = V q₀}, ∃ γ : G, γ ∈ Λ₁ ∧ u = ρ γ • ((ρ ((s t.1 : ↥Λ₂) : G))⁻¹ • z) := by
      intro t
      obtain ⟨γ', hγ'⟩ := (hfib₁ _ _).mp t.2
      obtain ⟨γ, hγ, hγρ⟩ := Subgroup.mem_map.mp γ'.2
      exact ⟨γ, hγ, by rw [hu, hγ', ← hγρ]⟩
    choose γ hγΛ₁ hγu using hch

    have hxmem : ∀ t, ρ (((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t.1 : ↥Λ₂) : G) * (γ t)⁻¹) ∈ Λ₂.map ρ := fun t =>
      Subgroup.mem_map_of_mem _ (Λ₂.mul_mem (Λ₂.mul_mem (Λ₂.inv_mem (s q₀).2) (s t.1).2) (Λ₂.inv_mem (hΛ (hγΛ₁ t))))
    have hxstab : ∀ t, (⟨_, hxmem t⟩ : ↥(Λ₂.map ρ)) ∈ MulAction.stabilizer ↥(Λ₂.map ρ) u := by
      intro t
      rw [MulAction.mem_stabilizer_iff]
      show ρ (((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t.1 : ↥Λ₂) : G) * (γ t)⁻¹) • u = u
      conv_lhs => rw [hγu t]
      rw [map_mul, map_mul, map_inv, map_inv, mul_smul, mul_smul, inv_smul_smul, smul_inv_smul]
    have hS'le : ∀ σ : ↥(MulAction.stabilizer ↥(Λ₁.map ρ) u), ((σ : ↥(Λ₁.map ρ)) : PGL(2, K₀)) ∈ Λ₂.map ρ :=
      fun σ => Subgroup.map_mono hΛ (σ : ↥(Λ₁.map ρ)).2
    let F : {q : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂ // V q = V q₀} × ↥(MulAction.stabilizer ↥(Λ₁.map ρ) u) →
        ↥(MulAction.stabilizer ↥(Λ₂.map ρ) u) := fun p =>
      ⟨⟨_, hxmem p.1⟩ * ⟨_, hS'le p.2⟩, by
        refine (MulAction.stabilizer ↥(Λ₂.map ρ) u).mul_mem (hxstab p.1) ?_
        rw [MulAction.mem_stabilizer_iff]
        have := (MulAction.mem_stabilizer_iff).mp p.2.2
        exact this⟩
    have hF : Function.Injective F := by
      rintro ⟨t₁, σ₁⟩ ⟨t₂, σ₂⟩ h

      have hPGL : ρ (((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₁.1 : ↥Λ₂) : G) * (γ t₁)⁻¹) * ((σ₁ : ↥(Λ₁.map ρ)) : PGL(2, K₀)) =
          ρ (((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₂.1 : ↥Λ₂) : G) * (γ t₂)⁻¹) * ((σ₂ : ↥(Λ₁.map ρ)) : PGL(2, K₀)) := by
        have := congrArg (fun x : ↥(MulAction.stabilizer ↥(Λ₂.map ρ) u) => ((x : ↥(Λ₂.map ρ)) : PGL(2, K₀))) h
        simpa [F] using this

      have hquot : ρ ((((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₂.1 : ↥Λ₂) : G) * (γ t₂)⁻¹)⁻¹ * (((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₁.1 : ↥Λ₂) : G) * (γ t₁)⁻¹)) ∈ Λ₁.map ρ := by
        have : ρ ((((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₂.1 : ↥Λ₂) : G) * (γ t₂)⁻¹)⁻¹ * (((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₁.1 : ↥Λ₂) : G) * (γ t₁)⁻¹)) =
            ((σ₂ : ↥(Λ₁.map ρ)) : PGL(2, K₀)) * ((σ₁ : ↥(Λ₁.map ρ)) : PGL(2, K₀))⁻¹ := by
          rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
          exact hPGL
        rw [this]
        exact (Λ₁.map ρ).mul_mem (σ₂ : ↥(Λ₁.map ρ)).2 ((Λ₁.map ρ).inv_mem (σ₁ : ↥(Λ₁.map ρ)).2)
      obtain ⟨lam, hlam, hlamρ⟩ := Subgroup.mem_map.mp hquot
      set x₁ : G := ((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₁.1 : ↥Λ₂) : G) * (γ t₁)⁻¹ with hx₁
      set x₂ : G := ((s q₀ : ↥Λ₂) : G)⁻¹ * ((s t₂.1 : ↥Λ₂) : G) * (γ t₂)⁻¹ with hx₂
      have hx₁Λ₂ : x₁ ∈ Λ₂ := Λ₂.mul_mem (Λ₂.mul_mem (Λ₂.inv_mem (s q₀).2) (s t₁.1).2) (Λ₂.inv_mem (hΛ (hγΛ₁ t₁)))
      have hx₂Λ₂ : x₂ ∈ Λ₂ := Λ₂.mul_mem (Λ₂.mul_mem (Λ₂.inv_mem (s q₀).2) (s t₂.1).2) (Λ₂.inv_mem (hΛ (hγΛ₁ t₂)))
      have hkerel : x₂⁻¹ * x₁ * lam⁻¹ ∈ Λ₁ := by
        apply hker
        · exact Λ₂.mul_mem (Λ₂.mul_mem (Λ₂.inv_mem hx₂Λ₂) hx₁Λ₂) (Λ₂.inv_mem (hΛ hlam))
        · rw [map_mul, ← hlamρ, map_inv, mul_inv_cancel]
      have h21 : x₂⁻¹ * x₁ ∈ Λ₁ := by
        have : x₂⁻¹ * x₁ = (x₂⁻¹ * x₁ * lam⁻¹) * lam := by group
        rw [this]; exact Λ₁.mul_mem hkerel hlam

      have hss : (((s t₂.1)⁻¹ * (s t₁.1) : ↥Λ₂) : G) ∈ Λ₁ := by
        have : (((s t₂.1)⁻¹ * (s t₁.1) : ↥Λ₂) : G) = (γ t₂)⁻¹ * (x₂⁻¹ * x₁) * (γ t₁) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hx₁, hx₂]; group
        rw [this]
        exact Λ₁.mul_mem (Λ₁.mul_mem (Λ₁.inv_mem (hγΛ₁ t₂)) h21) (hγΛ₁ t₁)
      have ht : t₁ = t₂ := by
        apply Subtype.ext
        have := (QuotientGroup.eq (s := Λ₁.subgroupOf Λ₂)).mpr (Subgroup.mem_subgroupOf.mpr hss)
        rw [hs, hs] at this
        exact this.symm
      subst ht
      have hσ : ((σ₁ : ↥(Λ₁.map ρ)) : PGL(2, K₀)) = ((σ₂ : ↥(Λ₁.map ρ)) : PGL(2, K₀)) := mul_left_cancel hPGL
      congr 1
      exact Subtype.ext (Subtype.ext hσ)
    have hle := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_subtype] at hle
    exact hle
  have hcount : ∀ q₀, ((Finset.univ.filter (fun q => V q = V q₀)).card : ℤ) = ((V q₀).ramificationIndex F₂ : ℤ) := by

    have hle : ∀ q₀, ((Finset.univ.filter (fun q => V q = V q₀)).card : ℤ) ≤ ((V q₀).ramificationIndex F₂ : ℤ) := by
      intro q₀
      haveI := hSfin q₀
      have h1 := hram q₀
      have h2 := hinj q₀
      have hSpos : 0 < Nat.card ↥(MulAction.stabilizer ↥(Λ₂.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) := Nat.card_pos
      have h1' : (V q₀).ramificationIndex F₂ * Nat.card ↥(MulAction.stabilizer ↥(Λ₁.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) =
          Nat.card ↥(MulAction.stabilizer ↥(Λ₂.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) := by exact_mod_cast h1
      have hS'pos : 0 < Nat.card ↥(MulAction.stabilizer ↥(Λ₁.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z)) := by
        rcases Nat.eq_zero_or_pos (Nat.card ↥(MulAction.stabilizer ↥(Λ₁.map ρ) ((ρ ((s q₀ : ↥Λ₂) : G))⁻¹ • z))) with h0 | hpos
        · rw [h0, mul_zero] at h1'; omega
        · exact hpos
      rw [← h1'] at h2
      exact_mod_cast Nat.le_of_mul_le_mul_right h2 hS'pos

    have hsum_m : ∑ w ∈ Finset.univ.image V, ((Finset.univ.filter (fun q => V q = w)).card : ℤ) =
        Fintype.card (↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂) := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_image V Finset.univ]
      push_cast
      rfl
    have hsum_e : ∑ w ∈ Finset.univ.image V, ((w.ramificationIndex F₂ : ℕ) : ℤ) = Fintype.card (↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂) := by
      have hdegE : Divisor.degree E = (Fintype.card (↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂) : ℤ) := by
        rw [hE, Divisor.degree_pullbackAlong φ hφC hFI, Divisor.degree_single, hrat₂, hdeg]
        simp
      have hEsum : E = ∑ w ∈ Finset.univ.image V, Finsupp.single w ((1 : ℤ) * (w.ramificationIndex F₂ : ℕ)) := by
        rw [hE]
        show Divisor.pullback F₁ (Finsupp.single (pt₂ z) 1) = _
        rw [Divisor.pullback_single, hfiber]
      rw [← hdegE, hEsum, map_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hw
      rw [Divisor.degree_single]
      show _ = (1 : ℤ) * _ * _
      rw [show (V q).deg = 1 from hrat₁ _]
      simp
    have heq := (Finset.sum_eq_sum_iff_of_le (fun w hw => by
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hw
        exact hle q)).mp (hsum_m.trans hsum_e.symm)
    intro q₀
    exact heq (V q₀) (Finset.mem_image.mpr ⟨q₀, Finset.mem_univ _, rfl⟩)

  ext w
  rw [Finset.sum_apply']
  by_cases hw : w.restrictAlong φ hφC = pt₂ z
  · obtain ⟨q₀, rfl⟩ := hVsurj w hw
    rw [hEapply_of, ← hcount q₀]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_boole]
  · rw [hEapply_off w hw]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h; exact hw (h ▸ hVover q)

end S_CerednikDrinfeld_Omega_pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv (solution)
