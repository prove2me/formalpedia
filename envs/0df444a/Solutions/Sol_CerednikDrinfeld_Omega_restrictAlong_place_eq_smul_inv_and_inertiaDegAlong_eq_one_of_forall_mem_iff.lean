-- Prove2me | solution 1 for CerednikDrinfeld.Omega.restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c9bbee41-5b35-5d56-b9b5-7f98ff50b4fb

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_eq_of_toValuationSubring_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Λ₁ Λ₂ : Subgroup G)
    (F₁ : Type) [Field F₁] [Algebra K F₁] (e₁ : F₁ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁))
    (F₂ : Type) [Field F₂] [Algebra K F₂] (e₂ : F₂ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂))
    (g : G) (φ : F₂ →ₐ[K] F₁)
    (hφ : ∀ x : F₂, ((e₁ (φ x) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      g • ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)))
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
    (z : ↥(Omega.upperHalfPlane K₀ K)) :
    (pt₁ z).restrictAlong φ hφC = pt₂ ((ρ g)⁻¹ • z) ∧ (pt₁ z).inertiaDegAlong φ hφC = 1 ∧
      ∀ n : ℤ, Divisor.pushforwardAlong φ hφC (Finsupp.single (pt₁ z) n) = Finsupp.single (pt₂ ((ρ g)⁻¹ • z)) n := by
  classical

  let ι₁ : F₁ →+* FractionRing (Omega.HolRingOf ϖ ρ) := (Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁).subtype.comp (e₁ : F₁ →ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)).toRingHom
  have hι₁ : ∀ x : F₁, ι₁ x = ((e₁ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) := fun x => rfl
  have hι₁inj : Function.Injective ι₁ := (Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁).subtype_injective.comp e₁.injective

  have hsmul_ne : ∀ (H : Omega.HolRingOf ϖ ρ), H ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ) → g • H ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ) := by
    intro H hH
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    exact nonZeroDivisors.ne_zero hH ((smul_eq_zero_iff_eq g).mp h0)
  have hsmul_mk : ∀ (G₀ H : Omega.HolRingOf ϖ ρ) (hH : H ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
      g • (Localization.mk G₀ ⟨H, hH⟩ : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk (g • G₀) ⟨g • H, hsmul_ne H hH⟩ := by
    intro G₀ H hH
    rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div]
    show (MulSemiringAction.toRingHom G (FractionRing (Omega.HolRingOf ϖ ρ)) g) _ = _
    rw [map_div₀]
    simp only [MulSemiringAction.toRingHom_apply, Mumford.frac_smul_algebraMap]
  have hsmul_apply : ∀ (H : Omega.HolRingOf ϖ ρ) (w : ↥(Omega.upperHalfPlane K₀ K)),
      (show ↥(Omega.holRing ϖ) from (g • H) : ↥(Omega.upperHalfPlane K₀ K) → K) w =
        (show ↥(Omega.holRing ϖ) from H : ↥(Omega.upperHalfPlane K₀ K) → K) ((ρ g)⁻¹ • w) := by
    intro H w
    rw [HolRingOf.smul_def, Omega.coe_smul_holRing_apply]

  have h1 : (pt₁ z).restrictAlong φ hφC = pt₂ ((ρ g)⁻¹ • z) := by
    symm
    apply AlgebraicCurve.Place.eq_of_toValuationSubring_le
    intro x hx
    obtain ⟨G₀, H, hH, hHz, hxe⟩ := (hpt₂.1 _ x).mp hx
    have hφx : φ x ∈ (pt₁ z).toValuationSubring := by
      refine (hpt₁.1 z (φ x)).mpr ⟨g • G₀, g • H, hsmul_ne H hH, ?_, ?_⟩
      · rw [hsmul_apply]; exact hHz
      · rw [hφ, hxe, hsmul_mk]
    show x ∈ ((pt₁ z).restrictAlong φ hφC).toValuationSubring
    letI := algebraAlong φ
    exact hφx

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
        show ((e₁ (algebraMap K F₁ (gz / hz)) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk _ 1
        rw [AlgEquiv.commutes, Localization.mk_algebraMap]
        rfl
      have hx' : Localization.mk (↑(⟨(1 : Omega.HolRingOf ϖ ρ), hmem1⟩ : ↥(nonZeroDivisors (Omega.HolRingOf ϖ ρ))) * g' - ↑(⟨h', hh⟩ : ↥(nonZeroDivisors (Omega.HolRingOf ϖ ρ))) * c') (⟨h', hh⟩ * ⟨1, hmem1⟩) ∈
          Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁ := by
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
  have h2 : (pt₁ z).inertiaDegAlong φ hφC = 1 := by
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI := isIntegral_along φ hφC
    have hmul := Place.deg_restrict_mul_inertiaDeg (K := K) (F := F₂) (pt₁ z)
    rw [hdeg1] at hmul
    exact Nat.eq_one_of_mul_eq_one_left hmul
  refine ⟨h1, h2, fun n => ?_⟩
  rw [Divisor.pushforwardAlong_single, h1, h2]
  simp

end S_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff (solution)
