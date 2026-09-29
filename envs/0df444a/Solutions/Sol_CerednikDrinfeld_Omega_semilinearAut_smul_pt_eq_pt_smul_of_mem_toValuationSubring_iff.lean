-- Prove2me | solution 1 for CerednikDrinfeld.Omega.semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f98314d8-e500-5ac4-bbda-5b2f32cc08ce

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Theorems.Thm_AlgebraicCurve_Place_eq_of_toValuationSubring_le
import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve
open scoped Pointwise

namespace PtEquiv

open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem coeffMap_apply_val (ϖ : PseudoUniformizer K₀ K) (t : IsometricAut K₀ K) (f : ↥(holRing ϖ))
    (z : ↥(upperHalfPlane K₀ K)) :
    ((t.coeffMap ϖ f : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) ⟨t.toRingEquiv (z : K), t.mapsTo_upperHalfPlane z.2⟩ =
      t.toRingEquiv ((f : ↥(upperHalfPlane K₀ K) → K) z) := by
  exact congrArg t.toRingEquiv (congrArg (f : ↥(upperHalfPlane K₀ K) → K)
    (Subtype.ext (t.toRingEquiv.symm_apply_apply (z : K))))

end PtEquiv

open PtEquiv in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Γ : Subgroup G)
    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_mem : ∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩)
    (g : SemilinearAut A.valuation.Completion FC) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion)
    (hreal : ∀ y : FC, ((eFC (g • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) :
    ∀ z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion),
      g • pt z = pt ((ρ n) • ⟨t.toRingEquiv (z : A.valuation.Completion), t.mapsTo_upperHalfPlane z.2⟩) := by
  intro z

  refine AlgebraicCurve.Place.eq_of_toValuationSubring_le ?_
  intro x hx
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
  obtain ⟨g₁, h₁, hh₁, hz₁, hE⟩ := (hpt_mem z (g⁻¹ • x)).1 hx

  have hEx : ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) :
      FractionRing (Omega.HolRingOf ϖ ρ)) =
      n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) (Localization.mk g₁ ⟨h₁, hh₁⟩) := by
    rw [← hE, ← hreal, smul_inv_smul]

  have hh₀ : h₁ ≠ 0 := nonZeroDivisors.ne_zero hh₁
  have hth : (Omega.toAmbientOf ϖ ρ t).map h₁ ≠ 0 := by
    intro h0; exact hh₀ (by simpa using congrArg (Omega.toAmbientOf ϖ ρ t).map.symm h0)
  have hnth : n • (Omega.toAmbientOf ϖ ρ t).map h₁ ≠ 0 := by
    intro h0; exact hth ((smul_eq_zero_iff_eq n).1 h0)
  have hh₂ : n • (Omega.toAmbientOf ϖ ρ t).map h₁ ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ) :=
    mem_nonZeroDivisors_of_ne_zero hnth
  refine (hpt_mem _ x).2 ⟨n • (Omega.toAmbientOf ϖ ρ t).map g₁, n • (Omega.toAmbientOf ϖ ρ t).map h₁, hh₂, ?_, ?_⟩
  ·
    rw [Omega.HolRingOf.smul_def]
    show ((ρ n • (t.coeffMap ϖ h₁ : ↥(Omega.holRing ϖ)) : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion)
      ((ρ n) • ⟨t.toRingEquiv (z : A.valuation.Completion), t.mapsTo_upperHalfPlane z.2⟩) ≠ 0
    rw [Omega.coe_smul_holRing_apply, inv_smul_smul, coeffMap_apply_val]
    exact (t.toRingEquiv.map_ne_zero_iff).2 hz₁
  ·
    rw [hEx, Mumford.frac_smul_def, FractionRing.mk_eq_div, FractionRing.mk_eq_div, map_div₀, map_div₀,
      Mumford.AmbientSemilinearAut.fracMap_algebraMap, Mumford.AmbientSemilinearAut.fracMap_algebraMap,
      Mumford.fracAct_algebraMap, Mumford.fracAct_algebraMap]

end S_CerednikDrinfeld_Omega_semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_semilinearAut_smul_pt_eq_pt_smul_of_mem_toValuationSubring_iff (solution)
