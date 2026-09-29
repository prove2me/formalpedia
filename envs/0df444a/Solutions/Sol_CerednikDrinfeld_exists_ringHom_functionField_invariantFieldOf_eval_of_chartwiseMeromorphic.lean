-- Prove2me | solution 1 for CerednikDrinfeld.exists_ringHom_functionField_invariantFieldOf_eval_of_chartwiseMeromorphic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4202de61-3756-5e8e-afb5-741b6ceb1386

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_injective
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Theorems.Thm_CerednikDrinfeld_exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group
import Theorems.Thm_CerednikDrinfeld_Omega_mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc
import Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_forall_finite_forall_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ringHom_functionField_invariantFieldOf_eval_of_chartwiseMeromorphic
p2m_attr_erase "instance" "AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqV AlgebraicCurve.TotallyDegenerateCovering.instFintypeV AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqE AlgebraicCurve.TotallyDegenerateCovering.instFintypeE instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_b AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_w AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_a AlgebraicCurve.TotallyDegenerateCovering.mk.sizeOf_spec AlgebraicCurve.TotallyDegenerateCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace LocAux

universe u

noncomputable def ev {C : Type u} [CommRing C] {X : Scheme.{u}} (q : Spec (CommRingCat.of C) ⟶ X)
    (O : X.Opens) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O) : Γ(X, O) →+* C :=
  ((q.appLE O ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom

theorem ev_apply {C : Type u} [CommRing C] {X : Scheme.{u}} (q : Spec (CommRingCat.of C) ⟶ X)
    (O : X.Opens) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O) (t : Γ(X, O)) :
    ev q O h t = (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
      (((Spec (CommRingCat.of C)).presheaf.map (homOfLE h).op).hom ((q.app O).hom t)) := rfl

theorem ev_res {C : Type u} [CommRing C] {X : Scheme.{u}} (q : Spec (CommRingCat.of C) ⟶ X)
    {O O' : X.Opens} (hO : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O) (hO' : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ O')
    (e : O' ≤ O) (t : Γ(X, O)) :
    ev q O' hO' ((X.presheaf.map (homOfLE e).op).hom t) = ev q O hO t := by
  show (X.presheaf.map (homOfLE e).op ≫ q.appLE O' ⊤ hO' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom t = _
  rw [Scheme.Hom.map_appLE_assoc]
  rfl

end LocAux

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪)) [IsProper f] [Flat f]

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ P : (Omega K₀ π).obj k, Θ k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
        ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)

    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    [CompleteSpace C] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (ψ₀ : Onr →ₐ[𝒪] R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε)
    (hex : Omega.IsExhausted ϖ) [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Φ : AdicPoint K₀ π R → {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R})
    (hΦ : (∀ (x : AdicPoint K₀ π R) (n : ℕ),
        Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ (Φ x).1 =
          (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1) ∧
      Function.Surjective Φ ∧
      (∀ x x' : AdicPoint K₀ π R, Φ x = Φ x' ↔ ∃ γ ∈ Γ', x' = x.act (σ γ)) ∧
      (Function.Injective (fun p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R} =>
          Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1) ∧
        ∀ cpt : Spec (CommRingCat.of C) ⟶ 𝒳, cpt ≫ f = Scheme.specOver C →
          ∃ p : {p : Spec (CommRingCat.of R) ⟶ 𝒳 // p ≫ f = Scheme.specOver R},
            Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1 = cpt))

    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪))
    (hsC : sC = Spec.map (CommRingCat.ofHom ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀))))
    [IsIntegral (Limits.pullback f sC)]

    (hmero : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
        ∃ F : ↥(Omega.upperHalfPlane K₀ C) → C,

          (∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
            ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
              q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
          q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
              ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
                F z = (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s))) ∧

          (∀ (γ : G), γ ∈ Γ' → ∀ z w : ↥(Omega.upperHalfPlane K₀ C),
            (w : C) = Omega.pmoebius K₀ (ρ γ) (z : C) → F w = F z) ∧

          (∀ n : ℕ, ∃ a b : ↥(Omega.affinoid ϖ n) → C, a ∈ Omega.holOn C (Omega.affinoid ϖ n) ∧ b ∈ Omega.holOn C (Omega.affinoid ϖ n) ∧
            (∃ z : ↥(Omega.affinoid ϖ n), b z ≠ 0) ∧
            ∀ z : ↥(Omega.affinoid ϖ n), b z ≠ 0 →
              b z * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ = a z) ∧

          (∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
            ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
              q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
          q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
              (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U →
              ∃ (N : ℕ) (hD : {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ⊆ Omega.upperHalfPlane K₀ C)
                (a b : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} → C),
                a ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ∧ b ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ∧
                (∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, (w : C) = (z : C) → b w ≠ 0) ∧
                ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, b w * F ⟨(w : C), hD w.2⟩ = a w)))

    (hfin : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (n : ℕ),
        Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)})) :
    ∃ e : ↑(Limits.pullback f sC).functionField →+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ'),
      (∀ c : C, e (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC) c) =
        algebraMap C ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') c) ∧
      (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
        (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
        ∃ (a b : Omega.HolRingOf ϖ ρ) (hb : b ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
          ((e (((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom s) : ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ')) : FractionRing (Omega.HolRingOf ϖ ρ)) =
              Localization.mk a ⟨b, hb⟩ ∧
          ∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
            ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
              q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
              q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
              ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
                (show ↥(Omega.holRing ϖ) from b : ↥(Omega.upperHalfPlane K₀ C) → C) z *
                    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s)) =
                  (show ↥(Omega.holRing ϖ) from a : ↥(Omega.upperHalfPlane K₀ C) → C) z) := by
  classical

  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) :=
    Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  have hϖπ : ϖ.ϖ = algebraMap 𝒪 K₀ π := by
    apply (algebraMap K₀ C).injective
    rw [← hF.unif, IsScalarTower.algebraMap_apply 𝒪 K₀ C]
  have hint : ∀ a : 𝒪, Valued.v (algebraMap K₀ C (algebraMap 𝒪 K₀ a)) ≤ 1 := fun a =>
    (hF.integers _).mpr ⟨a, rfl⟩
  have hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger 𝒪 a := fun a ha => by
    obtain ⟨b, hb⟩ := (hF.integers a).mp ha
    exact ⟨b, hb⟩
  have hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ C (algebraMap 𝒪 K₀ π)) ^ N ≤ ε := by
    intro ε hε
    obtain ⟨y, hy0, hy⟩ := hval ε hε
    obtain ⟨N, hN⟩ := hrk (algebraMap K₀ C (algebraMap 𝒪 K₀ π)) y (by rw [← hϖπ]; exact ϖ.lt_one) hy0
    exact ⟨N, hN.trans hy⟩
  have hholes := CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient 𝒪 K₀ π hπ C hint hv hq ϖ
  haveI hdom : IsDomain ↥(Omega.holRing ϖ) := (Omega.HolRingOf.isDomain_iff ϖ ρ).mp inferInstance
  have hsC' : sC = Scheme.specOver C := by
    rw [hsC, Scheme.specOver, ← IsScalarTower.algebraMap_eq 𝒪 K₀ C]

  have hqpt : ∀ y : AdicPoint K₀ π R, ∃ q' : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
      q' ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ y).1 ∧
      q' ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) := by
    intro y
    refine ⟨Limits.pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ y).1) (𝟙 _) ?_,
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
    rw [Category.assoc, (Φ y).2, Category.id_comp, hsC']
    exact Scheme.specMap_algHom_comp_specOver (IsScalarTower.toAlgHom 𝒪 R C)

  let Rep : (U : (Limits.pullback f sC).Opens) → ((Limits.pullback f sC).presheaf.obj (Opposite.op U)) →
      Omega.HolRingOf ϖ ρ → Omega.HolRingOf ϖ ρ → Prop := fun U s A B =>
    ∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
      ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
        q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
        q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
        ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
          B.1 z * LocAux.ev q U hqU s = A.1 z

  have hcoe_mul : ∀ A B : Omega.HolRingOf ϖ ρ, (A * B).1 = A.1 * B.1 := fun _ _ => rfl
  have hcoe_add : ∀ A B : Omega.HolRingOf ϖ ρ, (A + B).1 = A.1 + B.1 := fun _ _ => rfl
  have hcoe_sub : ∀ A B : Omega.HolRingOf ϖ ρ, (A - B).1 = A.1 - B.1 := fun _ _ => rfl

  have rep_exists : ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
      (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
      ∃ A B : Omega.HolRingOf ϖ ρ, B ≠ 0 ∧ Rep U s A B := by
    intro U hU s
    obtain ⟨F, hFval, hFinv, hFmer, hFloc⟩ := hmero U hU s
    obtain ⟨A, B, hB0, hAB⟩ :=
      CerednikDrinfeld.exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group
        𝒪 hdvr π hπ hcomplete hres hunr K₀ vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt ϖ hF hrk hval hex F hFinv hFmer
    refine ⟨A, B, hB0, ?_⟩
    intro x z hz q hq1 hq2 hqU
    obtain ⟨N, hD, a, b, ha, hb, hbz, hab⟩ := hFloc x z hz q hq1 hq2 hqU
    have hval := hFval x z hz q hq1 hq2 hqU
    rw [LocAux.ev_apply, ← hval]
    exact CerednikDrinfeld.Omega.mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc K₀ C ϖ hrk hex F A B hAB z N hD a b ha hb hbz hab

  have rep_restrict : ∀ (U V : (Limits.pullback f sC).Opens) (hVU : V ≤ U)
      (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)) (A B : Omega.HolRingOf ϖ ρ),
      Rep U s A B → Rep V (((Limits.pullback f sC).presheaf.map (homOfLE hVU).op).hom s) A B := by
    intro U V hVU s A B h x z hz q hq1 hq2 hqV
    have hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U := fun p hp => hVU (hqV hp)
    rw [LocAux.ev_res q hqU hqV hVU]
    exact h x z hz q hq1 hq2 hqU

  have rep_uniq : ∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
      (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)) (A B A' B' : Omega.HolRingOf ϖ ρ),
      Rep U s A B → Rep U s A' B' → A * B' = A' * B := by
    intro U hU s A B A' B' h h'
    rw [← sub_eq_zero]
    refine CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero K₀ C ϖ hrk hex hholes (A * B' - A' * B : Omega.HolRingOf ϖ ρ) fun n => ?_
    refine ⟨_, hfin U hU n, fun z hz => ?_⟩
    obtain ⟨x, -, hx⟩ := CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_surjOn ϖ hF (Omega.affinoid_subset_upperHalfPlane ϖ n z.2)
    obtain ⟨q, hq1, hq2⟩ := hqpt x
    have hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U := by
      by_contra hnot
      exact hz ⟨x, hx.symm, q, hq1, hq2, hnot⟩
    have e1 := h x ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ hx.symm q hq1 hq2 hqU
    have e2 := h' x ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ hx.symm q hq1 hq2 hqU
    rw [hcoe_sub, hcoe_mul, hcoe_mul, Pi.sub_apply, Pi.mul_apply, Pi.mul_apply, ← e1, ← e2]
    ring

  have rep_mul : ∀ (U : (Limits.pullback f sC).Opens) (s s' : (Limits.pullback f sC).presheaf.obj (Opposite.op U))
      (A B A' B' : Omega.HolRingOf ϖ ρ), Rep U s A B → Rep U s' A' B' → Rep U (s * s') (A * A') (B * B') := by
    intro U s s' A B A' B' h h' x z hz q hq1 hq2 hqU
    have e1 := h x z hz q hq1 hq2 hqU
    have e2 := h' x z hz q hq1 hq2 hqU
    rw [hcoe_mul, hcoe_mul, Pi.mul_apply, Pi.mul_apply, map_mul, ← e1, ← e2]
    ring
  have rep_add : ∀ (U : (Limits.pullback f sC).Opens) (s s' : (Limits.pullback f sC).presheaf.obj (Opposite.op U))
      (A B A' B' : Omega.HolRingOf ϖ ρ), Rep U s A B → Rep U s' A' B' → Rep U (s + s') (A * B' + A' * B) (B * B') := by
    intro U s s' A B A' B' h h' x z hz q hq1 hq2 hqU
    have e1 := h x z hz q hq1 hq2 hqU
    have e2 := h' x z hz q hq1 hq2 hqU
    rw [hcoe_add, hcoe_mul, hcoe_mul, hcoe_mul, Pi.add_apply, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, map_add, ← e1, ← e2]
    ring
  have rep_one : ∀ (U : (Limits.pullback f sC).Opens), Rep U 1 1 1 := by
    intro U x z hz q hq1 hq2 hqU
    rw [map_one, mul_one]
  have rep_zero : ∀ (U : (Limits.pullback f sC).Opens), Rep U 0 0 1 := by
    intro U x z hz q hq1 hq2 hqU
    rw [map_zero, mul_zero]
    rfl

  have rep_smul : ∀ (U : (Limits.pullback f sC).Opens) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U))
      (A B : Omega.HolRingOf ϖ ρ) (γ : G), γ ∈ Γ' → Rep U s A B → Rep U s (γ • A) (γ • B) := by
    intro U s A B γ hγ h x z hz q hq1 hq2 hqU
    rw [Omega.HolRingOf.smul_def, Omega.HolRingOf.smul_def, Omega.coe_smul_holRing_apply, Omega.coe_smul_holRing_apply]

    set x' : AdicPoint K₀ π R := x.act (σ γ⁻¹) with hx'
    have hz' : (((ρ γ)⁻¹ • z : ↥(Omega.upperHalfPlane K₀ C)) : C) = x'.toOmega C := by
      rw [Omega.coe_smul_upperHalfPlane, ← map_inv, hρ, hz, hx']
      exact (CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_act ϖ hF (σ γ⁻¹) x).symm
    have hΦx' : Φ x = Φ x' := (hΦ.2.2.1 x x').mpr ⟨γ⁻¹, inv_mem hγ, rfl⟩
    have hq1' : q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x').1 := by
      rw [← hΦx']; exact hq1
    exact h x' ((ρ γ)⁻¹ • z) hz' q hq1' hq2 hqU

  have rep_const : ∀ c : C, Rep ⊤ ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c))
      (algebraMap C (Omega.HolRingOf ϖ ρ) c) 1 := by
    intro c x z hz q hq1 hq2 hqT
    have hpV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have hWV : (⊤ : (Limits.pullback f sC).Opens) ≤ (Limits.pullback.fst f sC) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    obtain ⟨-, hE2⟩ := CerednikDrinfeld.eval_app_pullback_fst_eq_algebraMap_eval_app f sC (Φ x).1 q hq1 hq2 ⊤ hpV ⊤ hWV hqT
    have h2 := hE2 c
    rw [← LocAux.ev_apply, LocAux.ev_res q hqT hqT] at h2
    rw [h2]
    show (1 : ↥(Omega.upperHalfPlane K₀ C) → C) z * c = ((algebraMap C ↥(Omega.holRing ϖ) c : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ C) → C) z
    rw [Omega.algebraMap_holRing_apply, Pi.one_apply, one_mul]

  have mk_eq : ∀ (A B A' B' : Omega.HolRingOf ϖ ρ) (hB : B ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
      (hB' : B' ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)), A * B' = A' * B →
      (Localization.mk A ⟨B, hB⟩ : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk A' ⟨B', hB'⟩ := by
    intro A B A' B' hB hB' h
    rw [Localization.mk_eq_mk_iff]
    exact Localization.r_of_eq (by show B' * A = B * A'; rw [mul_comm, h, mul_comm])

  let Good : ↑(Limits.pullback f sC).functionField → FractionRing (Omega.HolRingOf ϖ ρ) → Prop := fun t y =>
    ∃ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U)
      (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)) (A B : Omega.HolRingOf ϖ ρ)
      (hB : B ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
      ((Limits.pullback f sC).presheaf.germ U (genericPoint (Limits.pullback f sC : Scheme.{0})) hU).hom s = t ∧
        y = Localization.mk A ⟨B, hB⟩ ∧ Rep U s A B
  have good_ex : ∀ t, ∃ y, Good t y := by
    intro t
    obtain ⟨U, hU, s, hs⟩ := TopCat.Presheaf.germ_exist (Limits.pullback f sC).presheaf t
    obtain ⟨A, B, hB0, hR⟩ := rep_exists U hU s
    exact ⟨_, U, hU, s, A, B, mem_nonZeroDivisors_of_ne_zero hB0, hs, rfl, hR⟩
  have good_uniq : ∀ t y y', Good t y → Good t y' → y = y' := by
    rintro t y y' ⟨U, hU, s, A, B, hB, hs, rfl, hR⟩ ⟨U', hU', s', A', B', hB', hs', rfl, hR'⟩
    obtain ⟨W, hW, iU, iU', hWs⟩ := TopCat.Presheaf.germ_eq (Limits.pullback f sC).presheaf
      (genericPoint (Limits.pullback f sC : Scheme.{0})) hU hU' s s' (hs.trans hs'.symm)
    apply mk_eq
    have h1 := rep_restrict U W iU.le s A B hR
    have h2 := rep_restrict U' W iU'.le s' A' B' hR'
    have hWs' : ((Limits.pullback f sC).presheaf.map (homOfLE iU.le).op).hom s =
        ((Limits.pullback f sC).presheaf.map (homOfLE iU'.le).op).hom s' := hWs
    rw [hWs'] at h1
    exact rep_uniq W hW _ A B A' B' h1 h2
  have good_mul : ∀ t t' y y', Good t y → Good t' y' → Good (t * t') (y * y') := by
    rintro t t' y y' ⟨U, hU, s, A, B, hB, hs, rfl, hR⟩ ⟨U', hU', s', A', B', hB', hs', rfl, hR'⟩
    refine ⟨U ⊓ U', ⟨hU, hU'⟩,
      ((Limits.pullback f sC).presheaf.map (homOfLE inf_le_left).op).hom s *
        ((Limits.pullback f sC).presheaf.map (homOfLE inf_le_right).op).hom s',
      A * A', B * B', Submonoid.mul_mem _ hB hB', ?_, ?_, ?_⟩
    · rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hs, hs']
    · rw [Localization.mk_mul]; rfl
    · exact rep_mul _ _ _ A B A' B' (rep_restrict U _ inf_le_left s A B hR) (rep_restrict U' _ inf_le_right s' A' B' hR')
  have good_add : ∀ t t' y y', Good t y → Good t' y' → Good (t + t') (y + y') := by
    rintro t t' y y' ⟨U, hU, s, A, B, hB, hs, rfl, hR⟩ ⟨U', hU', s', A', B', hB', hs', rfl, hR'⟩
    refine ⟨U ⊓ U', ⟨hU, hU'⟩,
      ((Limits.pullback f sC).presheaf.map (homOfLE inf_le_left).op).hom s +
        ((Limits.pullback f sC).presheaf.map (homOfLE inf_le_right).op).hom s',
      A * B' + A' * B, B * B', Submonoid.mul_mem _ hB hB', ?_, ?_, ?_⟩
    · rw [map_add, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hs, hs']
    · rw [Localization.add_mk]
      apply mk_eq
      simp only [Submonoid.coe_mul]
      ring
    · exact rep_add _ _ _ A B A' B' (rep_restrict U _ inf_le_left s A B hR) (rep_restrict U' _ inf_le_right s' A' B' hR')
  have good_one : Good 1 1 :=
    ⟨⊤, trivial, 1, 1, 1, Submonoid.one_mem _, by rw [map_one], Localization.mk_one.symm, rep_one ⊤⟩
  have good_zero : Good 0 0 :=
    ⟨⊤, trivial, 0, 0, 1, Submonoid.one_mem _, by rw [map_zero], (Localization.mk_zero _).symm, rep_zero ⊤⟩
  have good_inv : ∀ t y, Good t y → y ∈ Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ' := by
    rintro t y ⟨U, hU, s, A, B, hB, hs, rfl, hR⟩
    rw [Mumford.mem_invariantFieldOf_iff]
    intro γ hγ
    have hγB : γ • B ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ) :=
      mem_nonZeroDivisors_of_ne_zero fun h0 => nonZeroDivisors.ne_zero hB (by rw [← inv_smul_smul γ B, h0, smul_zero])
    have hsm : γ • (Localization.mk A ⟨B, hB⟩ : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk (γ • A) ⟨γ • B, hγB⟩ := by
      rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div,
        div_eq_mul_inv, div_eq_mul_inv, smul_mul', smul_inv'', Mumford.frac_smul_algebraMap, Mumford.frac_smul_algebraMap]
    rw [hsm]
    exact good_uniq t _ _ ⟨U, hU, s, γ • A, γ • B, hγB, hs, rfl, rep_smul U s A B γ hγ hR⟩ ⟨U, hU, s, A, B, hB, hs, rfl, hR⟩
  have good_const : ∀ c : C, Good (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f sC) c)
      (algebraMap C (FractionRing (Omega.HolRingOf ϖ ρ)) c) := by
    intro c
    refine ⟨⊤, trivial, (Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c),
      algebraMap C (Omega.HolRingOf ϖ ρ) c, 1, Submonoid.one_mem _, rfl, ?_, rep_const c⟩
    rw [IsScalarTower.algebraMap_apply C (Omega.HolRingOf ϖ ρ) (FractionRing (Omega.HolRingOf ϖ ρ)), ← Localization.mk_algebraMap]
    rfl

  choose eFun heFun using good_ex
  let e₀ : ↑(Limits.pullback f sC).functionField →+* FractionRing (Omega.HolRingOf ϖ ρ) :=
    { toFun := eFun
      map_one' := good_uniq _ _ _ (heFun 1) good_one
      map_mul' := fun t t' => good_uniq _ _ _ (heFun (t * t')) (good_mul _ _ _ _ (heFun t) (heFun t'))
      map_zero' := good_uniq _ _ _ (heFun 0) good_zero
      map_add' := fun t t' => good_uniq _ _ _ (heFun (t + t')) (good_add _ _ _ _ (heFun t) (heFun t')) }
  let e : ↑(Limits.pullback f sC).functionField →+* ↥(Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') :=
    e₀.codRestrict (Mumford.invariantFieldOf C G (Omega.HolRingOf ϖ ρ) Γ') fun t => good_inv t _ (heFun t)
  refine ⟨e, fun c => ?_, fun U hU s => ?_⟩
  · apply Subtype.ext
    rw [Mumford.algebraMap_invariantFieldOf_coe]
    exact good_uniq _ _ _ (heFun _) (good_const c)
  · obtain ⟨A, B, hB0, hR⟩ := rep_exists U hU s
    refine ⟨A, B, mem_nonZeroDivisors_of_ne_zero hB0, ?_, ?_⟩
    · exact good_uniq _ _ _ (heFun _) ⟨U, hU, s, A, B, mem_nonZeroDivisors_of_ne_zero hB0, rfl, rfl, hR⟩
    · intro x z hz q hq1 hq2 hqU
      exact hR x z hz q hq1 hq2 hqU

end S_CerednikDrinfeld_exists_ringHom_functionField_invariantFieldOf_eval_of_chartwiseMeromorphic
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ringHom_functionField_invariantFieldOf_eval_of_chartwiseMeromorphic (solution)
