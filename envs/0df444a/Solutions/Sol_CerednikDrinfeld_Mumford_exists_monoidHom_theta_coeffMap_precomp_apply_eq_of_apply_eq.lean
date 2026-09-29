-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0b5a4b7a-3618-5056-899e-0ff0985ad02f

import Theorems.Thm_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_theta_isometricAut
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq.CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle tree BruhatTits.tree Mumford.GraphAction Mumford.QuotEdge Mumford.QuotVert DegeneracyData ribbonKernel Mumford.vertexType Mumford.typePreserving Mumford.pathCycle Omega.theta_isometricAut Omega.PseudoUniformizer Omega.IsExhausted Omega.holRing Omega.IsometricAut Omega.HolRingOf Omega.toAmbientOf Omega.pmoebius Omega.upperHalfPlane Omega.pmoebius_mem_upperHalfPlane Omega.pmoebius_mul Omega.theta Mumford.smul_algebraMap_const Mumford.invariantFieldOf Mumford.algebraMap_invariantFieldOf_coe Mumford.AmbientSemilinearAut Mumford.AmbientSemilinearAut.fracMap Mumford.AmbientSemilinearAut.fracMap_algebraMap_const Mumford.mem_iff_of_mem_normalizer"
namespace ThetaPin21
p2m_open "CerednikDrinfeld"

open CerednikDrinfeld.Omega

def conjEquiv {P : Type} [Group P] (H : Subgroup P) (p : P)
    (h₁ : ∀ x : P, x ∈ H → p * x * p⁻¹ ∈ H) (h₂ : ∀ x : P, x ∈ H → p⁻¹ * x * p ∈ H) : ↥H ≃* ↥H where
  toFun x := ⟨p * x * p⁻¹, h₁ x x.2⟩
  invFun x := ⟨p⁻¹ * x * p, h₂ x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjEquiv_coe {P : Type} [Group P] (H : Subgroup P) (p : P)
    (h₁ : ∀ x : P, x ∈ H → p * x * p⁻¹ ∈ H) (h₂ : ∀ x : P, x ∈ H → p⁻¹ * x * p ∈ H) (x : ↥H) :
    ((conjEquiv H p h₁ h₂ x : ↥H) : P) = p * x * p⁻¹ := rfl

theorem conjEquiv_symm_coe {P : Type} [Group P] (H : Subgroup P) (p : P)
    (h₁ : ∀ x : P, x ∈ H → p * x * p⁻¹ ∈ H) (h₂ : ∀ x : P, x ∈ H → p⁻¹ * x * p ∈ H) (x : ↥H) :
    (((conjEquiv H p h₁ h₂).symm x : ↥H) : P) = p⁻¹ * x * p := rfl

theorem pmoebius_injOn {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : PGL(2, K₀)) {x y : K} (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K)
    (h : pmoebius K₀ g x = pmoebius K₀ g y) : x = y := by
  have := congrArg (pmoebius K₀ g⁻¹) h
  rwa [← pmoebius_mul K₀ hx, ← pmoebius_mul K₀ hy, inv_mul_cancel, pmoebius_one, pmoebius_one] at this

theorem theta_conj {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (φ : G ≃* G) (m : PGL(2, K₀))
    (hφ : ∀ g : G, ρ (φ g) = m * ρ g * m⁻¹)
    {a b w z : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hw : w ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) :
    theta ρ (pmoebius K₀ m a) (pmoebius K₀ m b) (pmoebius K₀ m w) (pmoebius K₀ m z) = theta ρ a b w z := by
  unfold theta
  rw [← Equiv.tprod_eq φ.toEquiv (fun γ => thetaFactor ρ (pmoebius K₀ m a) (pmoebius K₀ m b) (pmoebius K₀ m w) (pmoebius K₀ m z) γ)]
  refine tprod_congr fun g => ?_
  change thetaFactor ρ (pmoebius K₀ m a) (pmoebius K₀ m b) (pmoebius K₀ m w) (pmoebius K₀ m z) (φ g) = _
  have h1 : ∀ {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (m * ρ g * m⁻¹) (pmoebius K₀ m x) = pmoebius K₀ m (pmoebius K₀ (ρ g) x) := fun {x} hx => by
    rw [← pmoebius_mul K₀ hx, show m * ρ g * m⁻¹ * m = m * ρ g by group, pmoebius_mul K₀ hx]
  simp only [thetaFactor, hφ]
  rw [h1 ha, h1 hb]
  exact crossRatio_pmoebius m hz hw (pmoebius_mem_upperHalfPlane K₀ ha _) (pmoebius_mem_upperHalfPlane K₀ hb _)

end CerednikDrinfeld.ThetaPin21

open CerednikDrinfeld.ThetaPin21 in
theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)

    (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion) (hs : ∀ c, s c = (scalar σ) • c)
    (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion) (hn : n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G))
    (hreal : ∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)))

    (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
    (hz₀a : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) (hz₀b : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀)
    (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ) (hc : ∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀))
    (u : P.TorusPoints) (hu : ∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) :
    Omega.pmoebius K₀ (ρ n) (t.toRingEquiv a) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv b) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀) ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧
    (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv a)) ≠ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)) ∧
    (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv b)) ≠ Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)) ∧
    ∃ c' : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ,
      (∀ β : ↥(Γ.map ρ), ((c' β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv a)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv b)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀)))) ∧
      (∀ γ : ↥(Γ.map ρ),
        (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
          (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u))
          (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c' γ)) := by

  have hta : t.toRingEquiv a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := t.mapsTo_upperHalfPlane ha
  have htb : t.toRingEquiv b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := t.mapsTo_upperHalfPlane hb
  have htz₀ : t.toRingEquiv z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := t.mapsTo_upperHalfPlane hz₀
  have ha' := Omega.pmoebius_mem_upperHalfPlane K₀ hta (ρ n)
  have hb' := Omega.pmoebius_mem_upperHalfPlane K₀ htb (ρ n)
  have hz₀' := Omega.pmoebius_mem_upperHalfPlane K₀ htz₀ (ρ n)

  have h₁ : ∀ x : PGL(2, K₀), x ∈ Γ.map ρ → ρ n * x * (ρ n)⁻¹ ∈ Γ.map ρ := by
    rintro x ⟨g, hg, rfl⟩
    exact ⟨n * g * n⁻¹, (Mumford.mem_iff_of_mem_normalizer G Γ hn _).2 (by simpa [mul_assoc] using hg),
      by rw [map_mul, map_mul, map_inv]⟩
  have h₂ : ∀ x : PGL(2, K₀), x ∈ Γ.map ρ → (ρ n)⁻¹ * x * ρ n ∈ Γ.map ρ := by
    rintro x ⟨g, hg, rfl⟩
    exact ⟨n⁻¹ * g * n, (Mumford.mem_iff_of_mem_normalizer G Γ hn g).1 hg, by rw [map_mul, map_mul, map_inv]⟩
  obtain ⟨φ, hφ, hφs⟩ : ∃ φ : ↥(Γ.map ρ) ≃* ↥(Γ.map ρ),
      (∀ g : ↥(Γ.map ρ), ((φ g : ↥(Γ.map ρ)) : PGL(2, K₀)) = ρ n * (g : PGL(2, K₀)) * (ρ n)⁻¹) ∧
      (∀ g : ↥(Γ.map ρ), ((φ.symm g : ↥(Γ.map ρ)) : PGL(2, K₀)) = (ρ n)⁻¹ * (g : PGL(2, K₀)) * ρ n) :=
    ⟨conjEquiv (Γ.map ρ) (ρ n) h₁ h₂, fun _ => rfl, fun _ => rfl⟩
  have hφ' : ∀ g : ↥(Γ.map ρ), (Γ.map ρ).subtype (φ g) = ρ n * (Γ.map ρ).subtype g * (ρ n)⁻¹ := hφ

  have hst : ∀ x : A.valuation.Completion, s x = t.toRingEquiv x := by
    intro x
    have h := hreal (algebraMap A.valuation.Completion FC x)
    rw [AlgebraicCurve.SemilinearAut.smul_algebraMap, hgalFC_base σ x, ← hs x, AlgEquiv.commutes, AlgEquiv.commutes,
      Mumford.algebraMap_invariantFieldOf_coe, Mumford.algebraMap_invariantFieldOf_coe,
      Mumford.AmbientSemilinearAut.fracMap_algebraMap_const, Mumford.smul_algebraMap_const] at h
    exact (algebraMap A.valuation.Completion (FractionRing (Omega.HolRingOf ϖ ρ))).injective h

  have hnat := CerednikDrinfeld.Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle K₀ R₀ G ρ Γ htp E V D eE v₀ Φ hΦ
    n hn (πE σ) (sgn σ) (hπE σ n t hn hreal) (actZ σ) (hactZ σ)
  have hinv : ∀ γ : ↥(Γ.map ρ),
      ((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) (Φ (Additive.ofMul (Abelianization.of γ))) =
        Φ (Additive.ofMul (Abelianization.of (φ.symm γ))) := by
    intro γ
    have hconj : ((γ : ↥(Γ.map ρ)) : PGL(2, K₀)) = ρ n * ((φ.symm γ : ↥(Γ.map ρ)) : PGL(2, K₀)) * (ρ n)⁻¹ := by
      rw [hφs]; group
    rw [hnat (φ.symm γ) γ hconj]
    exact (actZ σ).symm_apply_apply _

  have hadm : ∀ {x : A.valuation.Completion}, x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion →
      (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ z₀) →
      ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (Omega.pmoebius K₀ (ρ n) (t.toRingEquiv x)) ≠
        Omega.pmoebius K₀ (ρ n) (t.toRingEquiv z₀) := by
    intro x hx hxz γ h
    have htx : t.toRingEquiv x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := t.mapsTo_upperHalfPlane hx
    apply hxz (φ.symm γ)
    apply t.toRingEquiv.injective
    rw [t.comm_pmoebius _ hx]
    apply pmoebius_injOn (ρ n) (Omega.pmoebius_mem_upperHalfPlane K₀ htx _) htz₀
    rw [← Omega.pmoebius_mul K₀ htx, hφs, show ρ n * ((ρ n)⁻¹ * (γ : PGL(2, K₀)) * ρ n) = (γ : PGL(2, K₀)) * ρ n by group,
      Omega.pmoebius_mul K₀ htx]
    exact h
  refine ⟨ha', hb', hz₀', hadm ha hz₀a, hadm hb hz₀b,
    (Units.map ((s : A.valuation.Completion →+* A.valuation.Completion) : A.valuation.Completion →* A.valuation.Completion)).comp
      (c.comp φ.symm.toMonoidHom), fun β => ?_, fun γ => ?_⟩
  ·
    change s (((c (φ.symm β)) : (A.valuation.Completion)ˣ) : A.valuation.Completion) = _
    rw [hc (φ.symm β), hst,
      ← Omega.theta_isometricAut (Γ.map ρ).subtype t ha hb hz₀ (Omega.pmoebius_mem_upperHalfPlane K₀ hz₀ _),
      t.comm_pmoebius _ hz₀,
      ← theta_conj (Γ.map ρ).subtype φ (ρ n) hφ' hta htb htz₀ (Omega.pmoebius_mem_upperHalfPlane K₀ htz₀ _)]
    congr 1
    rw [← Omega.pmoebius_mul K₀ htz₀, ← Omega.pmoebius_mul K₀ htz₀, hφs]
    congr 1
    group
  ·
    simp only [PeriodDatum.coeffMap_apply, PeriodDatum.precomp_apply, LinearEquiv.coe_coe, hinv, hu, toMul_ofMul]
    rfl

end S_CerednikDrinfeld_Mumford_exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_monoidHom_theta_coeffMap_precomp_apply_eq_of_apply_eq (solution)
