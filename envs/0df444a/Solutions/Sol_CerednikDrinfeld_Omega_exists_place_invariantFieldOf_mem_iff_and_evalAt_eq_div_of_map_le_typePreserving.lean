-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/00aedd2f-f04e-53cb-a183-b22099d99e46

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_sub_lt_of_finite_residueField
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

open WithZero

namespace PTLOC

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : Omega.PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

def evz (z : ↥(Omega.upperHalfPlane K₀ K)) : Omega.HolRingOf ϖ ρ →+* K where
  toFun f := (show ↥(Omega.holRing ϖ) from f : ↥(Omega.upperHalfPlane K₀ K) → K) z
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evz_apply (z : ↥(Omega.upperHalfPlane K₀ K)) (f : Omega.HolRingOf ϖ ρ) :
    evz ϖ ρ z f = (show ↥(Omega.holRing ϖ) from f : ↥(Omega.upperHalfPlane K₀ K) → K) z := rfl

def shift (z : ↥(Omega.upperHalfPlane K₀ K)) : ↥(Omega.upperHalfPlane K₀ K) :=
  ⟨(z : K) + 1, by
    rw [Omega.mem_upperHalfPlane_iff]
    intro a ha
    have hz := (Omega.mem_upperHalfPlane_iff K₀ (z : K)).mp z.2 (a - 1)
    apply hz
    rw [map_sub, map_one, ha, add_sub_cancel_right]⟩

theorem coordSub_ne_zero (z : ↥(Omega.upperHalfPlane K₀ K)) : (show Omega.HolRingOf ϖ ρ from Omega.coordSub ϖ z) ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : Omega.HolRingOf ϖ ρ => (show ↥(Omega.holRing ϖ) from f : ↥(Omega.upperHalfPlane K₀ K) → K) (shift z)) h
  simp only [shift, Omega.coordSub_apply] at h1
  have h2 : _ = (0 : K) := h1
  simp at h2

end PTLOC

namespace PTLOC

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : Omega.PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

theorem evz_algebraMap (z : ↥(Omega.upperHalfPlane K₀ K)) (c : K) :
    evz ϖ ρ z (algebraMap K (Omega.HolRingOf ϖ ρ) c) = c := rfl

variable [IsDomain (Omega.HolRingOf ϖ ρ)]

local notation "Fr" => FractionRing (Omega.HolRingOf ϖ ρ)

theorem alg_ne_zero {b : Omega.HolRingOf ϖ ρ} (hb : b ≠ 0) : algebraMap (Omega.HolRingOf ϖ ρ) Fr b ≠ 0 :=
  fun h => hb ((IsFractionRing.injective (Omega.HolRingOf ϖ ρ) Fr) (by rw [h, map_zero]))

theorem mk_eq_div (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)) :
    (Localization.mk a ⟨b, hb⟩ : Fr) = algebraMap _ Fr a / algebraMap _ Fr b := by
  rw [Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div]

theorem coe_sub_algebraMap (Δ : Subgroup G) (x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ))
    (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
    (hx : (x : Fr) = Localization.mk a ⟨b, hb⟩) (c : K) :
    ((x - algebraMap K _ c : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ)) : Fr) =
      Localization.mk (a - algebraMap K (Omega.HolRingOf ϖ ρ) c * b) ⟨b, hb⟩ := by
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [Subfield.coe_sub, hx, Mumford.algebraMap_invariantFieldOf_coe,
    IsScalarTower.algebraMap_apply K (Omega.HolRingOf ϖ ρ) Fr, mk_eq_div, mk_eq_div, map_sub, map_mul, sub_div,
    mul_div_cancel_right₀ _ (alg_ne_zero ϖ ρ hb0)]

end PTLOC

theorem PTLOC.coe_eFC_sub_algebraMap {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Δ : Subgroup G) {FC : Type} [Field FC] [Algebra K FC]
    (eFC : FC ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ)) (x : FC) (c : K) :
    eFC (x - algebraMap K FC c) = eFC x - algebraMap K _ c := by
  rw [map_sub, AlgEquiv.commutes]

theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]

    (FC : Type) [Field FC] [Algebra K FC]
    (eFC : FC ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ))
    (hnc : ∃ x : FC, x ∉ Set.range (algebraMap K FC)) :
    ∃ pt : ↥(Omega.upperHalfPlane K₀ K) → Place K FC,
      ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))) := by
  classical
  have hfin := CerednikDrinfeld.Omega.exists_finset_forall_v_sub_lt_of_finite_residueField K₀ K R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ
  have key : ∀ z : ↥(Omega.upperHalfPlane K₀ K), ∃ P : Place K FC,
      (∀ x : FC, x ∈ P.toValuationSubring ↔
        ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
          (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧
            ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          P.evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z /
              (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ P.toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0)) := by
    intro z

    have hfac : ∀ F : Omega.HolRingOf ϖ ρ, F ≠ 0 → ∃ (n : ℕ) (G' : Omega.HolRingOf ϖ ρ),
        F = (show Omega.HolRingOf ϖ ρ from Omega.coordSub ϖ z) ^ n * G' ∧ PTLOC.evz ϖ ρ z G' ≠ 0 := by
      intro F hF
      obtain ⟨G', h1, h2⟩ :=
        CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hfin F hF z
      exact ⟨_, G', h1, h2⟩

    obtain ⟨v, hv1, hv2, -, ψ, -⟩ := Valuation.exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
      (Omega.HolRingOf ϖ ρ) K (PTLOC.evz ϖ ρ z) _ (PTLOC.coordSub_ne_zero ϖ ρ z) (Omega.coordSub_apply_self ϖ z) hfac

    let w : Valuation FC ℤᵐ⁰ := v.comap ((Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ).subtype.comp (eFC : FC →+* ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)))
    have hw : ∀ x : FC, w x = v ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) := fun _ => rfl

    obtain ⟨y, hy0, hy1⟩ : ∃ y : FC, y ≠ 0 ∧ w y < 1 := by
      obtain ⟨x, hx⟩ := hnc
      by_cases hle : w x ≤ 1
      · rw [hw] at hle
        obtain ⟨a, b, hb, hφb, hxe⟩ := (hv1 _).mp hle
        refine ⟨x - algebraMap K _ (PTLOC.evz ϖ ρ z a / PTLOC.evz ϖ ρ z b),
          sub_ne_zero.mpr (fun h => hx ⟨_, h.symm⟩), ?_⟩
        rw [hw, PTLOC.coe_eFC_sub_algebraMap ϖ ρ Γ eFC, PTLOC.coe_sub_algebraMap ϖ ρ _ (eFC x) a b hb hxe]
        refine (hv2 _ b hb hφb).mpr ?_
        rw [map_sub, map_mul, PTLOC.evz_algebraMap, div_mul_cancel₀ _ hφb, sub_self]
      · push Not at hle
        have hx0 : x ≠ 0 := by
          rintro rfl
          rw [map_zero] at hle
          exact not_lt_zero hle
        refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ hle

    have hwy0 : w y ≠ 0 := (Valuation.ne_zero_iff w).mpr hy0
    haveI : Nontrivial ↥(MonoidWithZeroHom.valueGroup (.ofClass w)) :=
      ⟨⟨Units.mk0 (w y) hwy0, MonoidWithZeroHom.mem_valueGroup (.ofClass w) (b := Units.mk0 (w y) hwy0) ⟨y, rfl⟩⟩, 1,
        fun h => hy1.ne (by
        have := congrArg (fun u : ↥(MonoidWithZeroHom.valueGroup (.ofClass w)) => ((u : (ℤᵐ⁰)ˣ) : ℤᵐ⁰)) h
        simpa using this)⟩

    obtain ⟨P, hP⟩ : ∃ P : Place K FC, P.toValuationSubring = w.valuationSubring :=
     ⟨{ toValuationSubring := w.valuationSubring
        algebraMap_mem' := fun c => by
          show w (algebraMap K _ c) ≤ 1
          rw [hw]
          refine (hv1 _).mpr ⟨algebraMap K _ c, 1, Submonoid.one_mem _, ?_, ?_⟩
          · show PTLOC.evz ϖ ρ z 1 ≠ 0
            rw [map_one]; exact one_ne_zero
          · have h1 : (eFC (algebraMap K FC c) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) = algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ) c := AlgEquiv.commutes eFC c
            have h2 : ((eFC (algebraMap K FC c) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
                algebraMap K (FractionRing (Omega.HolRingOf ϖ ρ)) c := by
              rw [h1]; exact Mumford.algebraMap_invariantFieldOf_coe K G (Omega.HolRingOf ϖ ρ) Γ c
            rw [h2, IsScalarTower.algebraMap_apply K (Omega.HolRingOf ϖ ρ) _, PTLOC.mk_eq_div, map_one, div_one]
        ne_top' := by
          intro htop
          have hmem : y⁻¹ ∈ w.valuationSubring := by rw [htop]; exact ValuationSubring.mem_top _
          have h1 : w y⁻¹ ≤ 1 := hmem
          rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hwy0)] at h1
          exact absurd hy1 (not_lt.mpr h1)
        isPrincipalIdealRing' := Valuation.valuationSubring_isPrincipalIdealRing w }, rfl⟩
    have hequiv : w.IsEquiv P.toValuationSubring.valuation := by
      rw [hP]; exact Valuation.isEquiv_valuation_valuationSubring w
    have hmemP : ∀ x : FC, x ∈ P.toValuationSubring ↔
        ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
          (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧
            ((eFC x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩ := by
      intro x
      rw [hP]
      show w x ≤ 1 ↔ _
      rw [hw]
      exact hv1 _
    refine ⟨P, hmemP, fun g h hh hx hz => ?_⟩
    have hX : eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ P.toValuationSubring :=
      (hmemP _).mpr ⟨g, h, hh, hz, by rw [AlgEquiv.apply_symm_apply]⟩
    constructor
    ·
      rw [Place.evalAt_of_mem (v := P) hX]
      have hdiff : w (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ -
          algebraMap K _ (PTLOC.evz ϖ ρ z g / PTLOC.evz ϖ ρ z h)) < 1 := by
        rw [hw, PTLOC.coe_eFC_sub_algebraMap ϖ ρ Γ eFC, AlgEquiv.apply_symm_apply, PTLOC.coe_sub_algebraMap ϖ ρ _ _ g h hh rfl]
        refine (hv2 _ h hh hz).mpr ?_
        rw [map_sub, map_mul, PTLOC.evz_algebraMap, div_mul_cancel₀ _ (show PTLOC.evz ϖ ρ z h ≠ 0 from hz), sub_self]
      have hres : IsLocalRing.residue ↥P.toValuationSubring ⟨_, hX⟩ =
          algebraMap K P.ResidueField (PTLOC.evz ϖ ρ z g / PTLOC.evz ϖ ρ z h) := by
        rw [IsScalarTower.algebraMap_apply K ↥P.toValuationSubring P.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq]
        refine Ideal.Quotient.eq.mpr ((ValuationSubring.valuation_lt_one_iff _ _).mpr ?_)
        exact (hequiv.lt_one_iff_lt_one).mp hdiff
      rw [hres, Place.residueInv_algebraMap]
      rfl
    ·
      rw [ValuationSubring.mem_nonunits_iff, ← hequiv.lt_one_iff_lt_one, hw, AlgEquiv.apply_symm_apply]
      exact hv2 g h hh hz
  choose pt hpt using key
  exact ⟨pt, fun z => (hpt z).1, fun z => (hpt z).2⟩

end S_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving (solution)
