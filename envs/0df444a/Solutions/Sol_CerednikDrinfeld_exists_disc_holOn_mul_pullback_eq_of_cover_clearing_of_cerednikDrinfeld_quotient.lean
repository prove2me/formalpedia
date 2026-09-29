-- Prove2me | solution 1 for CerednikDrinfeld.exists_disc_holOn_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/db745f20-dd6a-599c-a350-8195d04dc89d

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app
import Theorems.Thm_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine
import Theorems.Thm_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_injective
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_disc_holOn_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient

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

    (hclear : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U))
        (x : AdicPoint K₀ π R) (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
        q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
          q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
        ∃ (V : 𝒳.Opens) (hxV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ V)
          (W : (Limits.pullback f sC).Opens) (hWV : W ≤ (Limits.pullback.fst f sC) ⁻¹ᵁ V)
          (hqW : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ W) (hWη : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ W)
          (m : ℕ) (num : Fin m → 𝒳.presheaf.obj (Opposite.op V)) (cnum : Fin m → C)
          (m' : ℕ) (den : Fin m' → 𝒳.presheaf.obj (Opposite.op V)) (cden : Fin m' → C),

          (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
              ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j))) ≠ 0 ∧

          ((Limits.pullback f sC).presheaf.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op).hom s *
              ((Limits.pullback f sC).presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op).hom (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
                  ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j))) =
            ((Limits.pullback f sC).presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op).hom (∑ i, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cnum i))) *
                  ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (num i))) ∧

          ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U → ∃ (W' : (Limits.pullback f sC).Opens) (hW' : W' ≤ W) (hqW' : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ W'),
            IsUnit (((Limits.pullback f sC).presheaf.map (homOfLE hW').op).hom (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
                  ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j)))))))

    (htube : (∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (V : 𝒳.Opens) (p : 𝒳.presheaf.obj (Opposite.op V)),
        ∃ (m : ℕ) (L M : Fin m → Finset (C × C)),

          (∀ k, ∀ er ∈ L k, er.2 ≠ 0) ∧ (∀ k, ∀ er ∈ M k, er.2 ≠ 0) ∧

          (∀ (x : AdicPoint K₀ π R) (z : C), z = x.toOmega C →
            z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) →
            (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ V →
            ∃ k, z ∈ {z : C | z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) ∧
              (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1)) ∧
              (∀ er ∈ M k, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1) ≤ Valued.v er.2)}) ∧

          (∀ k, ∀ (x : AdicPoint K₀ π R) (z : C), z = x.toOmega C →
            z ∈ {z : C | z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) ∧
              (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1)) ∧
              (∀ er ∈ M k, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1) ≤ Valued.v er.2)} →
            (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ V) ∧

          (∀ k, ∃ F : ↥{z : C | z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) ∧
              (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1)) ∧
              (∀ er ∈ M k, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1) ≤ Valued.v er.2)} → C,
            F ∈ Omega.holOn C {z : C | z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) ∧
              (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1)) ∧
              (∀ er ∈ M k, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1) ≤ Valued.v er.2)} ∧
            ∀ (x : AdicPoint K₀ π R) (z : ↥{z : C | z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) ∧
              (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1)) ∧
              (∀ er ∈ M k, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z - er.1) ≤ Valued.v er.2)}), (z : C) = x.toOmega C →
              ∀ (hxV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ V),
                F z = algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
                  (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hxV).op).hom ((((Φ x).1).app V).hom p))))))

    (hfin : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (n : ℕ),
        Set.Finite {z : ↥(Omega.affinoid ϖ n) | ∃ x : AdicPoint K₀ π R, (z : C) = x.toOmega C ∧
          ∃ q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 ∧
            q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
            ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U)})) :
    (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U))
      (F : ↥(Omega.upperHalfPlane K₀ C) → C),

        (∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
          ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
          q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
            ∀ (hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U),
              F z = (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
                (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqU).op).hom ((q.app U).hom s))) →

        (∀ (x : AdicPoint K₀ π R) (z : ↥(Omega.upperHalfPlane K₀ C)), (z : C) = x.toOmega C →
          ∀ (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
            q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 →
          q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) →
            (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U →
            ∃ (N : ℕ) (hD : {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ⊆ Omega.upperHalfPlane K₀ C)
              (a b : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} → C),
              a ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ∧ b ∈ Omega.holOn C {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} ∧
              (∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, (w : C) = (z : C) → b w ≠ 0) ∧
              ∀ w : ↥{w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N}, b w * F ⟨(w : C), hD w.2⟩ = a w)) := by
  classical
  intro U hU s F hvalF x z hz q hq1 hq2 hqU

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
  set w₀ : C := algebraMap K₀ C ϖ.ϖ with hw₀
  have hw0 : 0 < Valued.v w₀ := ϖ.pos
  have hw1 : Valued.v w₀ < 1 := ϖ.lt_one
  have hwne : w₀ ≠ 0 := fun h => by rw [h, map_zero] at hw0; exact lt_irrefl _ hw0
  have hwanti : StrictAnti fun n : ℕ => Valued.v w₀ ^ n := pow_right_strictAnti₀ hw0 hw1

  have hDmono : ∀ {N N' : ℕ}, N ≤ N' → ∀ w : C, Valued.v (w - (z : C)) ≤ Valued.v w₀ ^ N' → Valued.v (w - (z : C)) ≤ Valued.v w₀ ^ N :=
    fun h w hw => hw.trans (hwanti.antitone h)

  have hPge : ∀ (d u₀ e t : C), d ≠ 0 → t ≠ 0 → Valued.v t ≤ Valued.v (u₀ - e) →
      ∃ N : ℕ, ∀ δ : C, Valued.v δ ≤ Valued.v w₀ ^ N → Valued.v t ≤ Valued.v (u₀ + δ / d - e) := by
    intro d u₀ e t hd ht hle
    have hue : u₀ - e ≠ 0 := by
      intro h0; rw [h0, map_zero, le_zero_iff] at hle; exact ht ((map_eq_zero _).mp hle)
    obtain ⟨N, hN⟩ := hrk w₀ (d * (u₀ - e)) hw1 (mul_ne_zero hd hue)
    refine ⟨N + 1, fun δ hδ => ?_⟩
    have hvd : 0 < Valued.v d := zero_lt_iff.mpr ((map_ne_zero _).mpr hd)
    have hlt : Valued.v (δ / d) < Valued.v (u₀ - e) := by
      rw [map_div₀, div_lt_iff₀ hvd]
      calc Valued.v δ ≤ Valued.v w₀ ^ (N + 1) := hδ
        _ < Valued.v w₀ ^ N := hwanti (Nat.lt_succ_self N)
        _ ≤ Valued.v (d * (u₀ - e)) := hN
        _ = Valued.v (u₀ - e) * Valued.v d := by rw [Valuation.map_mul, mul_comm]
    rw [show u₀ + δ / d - e = (u₀ - e) + δ / d by ring, Valuation.map_add_eq_of_lt_left _ hlt]
    exact hle
  have hPle : ∀ (d u₀ e t : C), d ≠ 0 → t ≠ 0 → Valued.v (u₀ - e) ≤ Valued.v t →
      ∃ N : ℕ, ∀ δ : C, Valued.v δ ≤ Valued.v w₀ ^ N → Valued.v (u₀ + δ / d - e) ≤ Valued.v t := by
    intro d u₀ e t hd ht hle
    obtain ⟨N, hN⟩ := hrk w₀ (d * t) hw1 (mul_ne_zero hd ht)
    refine ⟨N, fun δ hδ => ?_⟩
    have hvd : 0 < Valued.v d := zero_lt_iff.mpr ((map_ne_zero _).mpr hd)
    have hle' : Valued.v (δ / d) ≤ Valued.v t := by
      rw [map_div₀, div_le_iff₀ hvd]
      calc Valued.v δ ≤ Valued.v w₀ ^ N := hδ
        _ ≤ Valued.v (d * t) := hN
        _ = Valued.v t * Valued.v d := by rw [Valuation.map_mul, mul_comm]
    rw [show u₀ + δ / d - e = (u₀ - e) + δ / d by ring]
    exact (Valuation.map_add _ _ _).trans (max_le hle hle')

  have hcombine : ∀ (ι : Type) (T : Finset ι) (P : ι → C → Prop),
      (∀ i ∈ T, ∃ N : ℕ, ∀ w : C, Valued.v (w - (z : C)) ≤ Valued.v w₀ ^ N → P i w) →
      ∃ N : ℕ, ∀ w : C, Valued.v (w - (z : C)) ≤ Valued.v w₀ ^ N → ∀ i ∈ T, P i w := by
    intro ι T P
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨0, fun w _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a T haT ih =>
      intro h
      obtain ⟨Na, hNa⟩ := h a (Finset.mem_insert_self a T)
      obtain ⟨NT, hNT⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ⟨Na + NT, fun w hw i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact hNa w (hDmono (Nat.le_add_right Na NT) w hw)
      · exact hNT w (hDmono (Nat.le_add_left NT Na) w hw) i hi'

  obtain ⟨V, hxV, W, hWV, hqW, hWη, m, num, cnum, m', den, cden, hD0, hident, hunit⟩ := hclear U hU s x q hq1 hq2
  obtain ⟨W', hW'W, hqW', hDunit⟩ := hunit hqU

  have hm' : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h0 | h0
    · subst h0; exact absurd (by simp) hD0
    · exact h0
  set Dsec := (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
      ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j))) with hDsec
  set Nsec := (∑ i, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cnum i))) *
      ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (num i))) with hNsec

  obtain ⟨n₀, hzn₀⟩ := hex (z : C) z.2
  set n : ℕ := n₀ + 1 with hn
  have hzn : (z : C) ∈ Omega.affinoid ϖ n := Omega.affinoid_mono ϖ (Nat.le_succ n₀) hzn₀
  obtain ⟨cch, mch, gch, hgch, -, -, -, hzE⟩ :=
    (CerednikDrinfeld.Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion 𝒪 K₀ C ϖ π hπ hϖπ hint hv n
      (Nat.le_add_left 1 n₀)).2 (z : C) hzn
  set E : Set C := (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk gch) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk gch) ∪
    Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (gch * edgeFlip K₀ ϖ))) with hE
  obtain ⟨⟨H, ϱ, hϱ, hEiff⟩, hginv⟩ :=
    CerednikDrinfeld.Omega.exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine 𝒪 K₀ C ϖ π hπ hϖπ hint hv cch mch gch hgch
  set c₁ : C := algebraMap K₀ C cch with hc₁
  set d₁ : C := algebraMap K₀ C (ϖ.ϖ ^ (mch - 1)) with hd₁
  have hd₁0 : d₁ ≠ 0 := by
    rw [hd₁, map_ne_zero]
    exact zpow_ne_zero _ fun h => by have h0 := ϖ.pos; rw [h, map_zero, map_zero] at h0; exact lt_irrefl _ h0

  let Pc : Finset (C × C) → Finset (C × C) → Set C := fun L M =>
    {w : C | w ∈ E ∧ (∀ er ∈ L, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk gch)⁻¹ w - er.1)) ∧
      (∀ er ∈ M, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk gch)⁻¹ w - er.1) ≤ Valued.v er.2)}

  have hdisc : ∀ (L M : Finset (C × C)), (∀ er ∈ L, er.2 ≠ 0) → (∀ er ∈ M, er.2 ≠ 0) → (z : C) ∈ Pc L M →
      ∃ N : ℕ, ∀ w : C, Valued.v (w - (z : C)) ≤ Valued.v w₀ ^ N → w ∈ Pc L M := by
    intro L M hL hM hzP
    obtain ⟨hzE', hzL, hzM⟩ := hzP
    obtain ⟨hzc, hzH⟩ := (hEiff (z : C)).mp hzE'

    obtain ⟨N₁, hN₁⟩ := hPle 1 (z : C) c₁ d₁ one_ne_zero hd₁0 hzc

    obtain ⟨N₂, hN₂⟩ := hcombine C H (fun h w => Valued.v (ϱ h) ≤ Valued.v (w - h)) fun h hh => by
      obtain ⟨N, hN⟩ := hPge 1 (z : C) h (ϱ h) one_ne_zero (hϱ h hh) (hzH h hh)
      exact ⟨N, fun w hw => by simpa using hN (w - (z : C)) hw⟩

    obtain ⟨N₃, hN₃⟩ := hcombine (C × C) L
        (fun er w => Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk gch)⁻¹ w - er.1)) fun er her => by
      obtain ⟨N, hN⟩ := hPge d₁ (((z : C) - c₁) / d₁) er.1 er.2 hd₁0 (hL er her) (by rw [← hginv]; exact hzL er her)
      refine ⟨N, fun w hw => ?_⟩
      rw [hginv, show (w - c₁) / d₁ - er.1 = ((z : C) - c₁) / d₁ + (w - (z : C)) / d₁ - er.1 by ring]
      exact hN _ hw
    obtain ⟨N₄, hN₄⟩ := hcombine (C × C) M
        (fun er w => Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk gch)⁻¹ w - er.1) ≤ Valued.v er.2) fun er her => by
      obtain ⟨N, hN⟩ := hPle d₁ (((z : C) - c₁) / d₁) er.1 er.2 hd₁0 (hM er her) (by rw [← hginv]; exact hzM er her)
      refine ⟨N, fun w hw => ?_⟩
      rw [hginv, show (w - c₁) / d₁ - er.1 = ((z : C) - c₁) / d₁ + (w - (z : C)) / d₁ - er.1 by ring]
      exact hN _ hw
    refine ⟨N₁ + N₂ + N₃ + N₄, fun w hw => ⟨?_, ?_, ?_⟩⟩
    · refine (hEiff w).mpr ⟨?_, ?_⟩
      · simpa using hN₁ (w - (z : C)) (hDmono (by omega) w hw)
      · exact hN₂ w (hDmono (by omega) w hw)
    · exact hN₃ w (hDmono (by omega) w hw)
    · exact hN₄ w (hDmono (by omega) w hw)

  have hBnum := fun i : Fin m => htube gch V (num i)
  have hBden := fun j : Fin m' => htube gch V (den j)
  choose mN LN MN hLN hMN hcovN hoverN hholN using hBnum
  choose mD LD MD hLD hMD hcovD hoverD hholD using hBden
  have hkN := fun i : Fin m => hcovN i x (z : C) hz hzE hxV
  have hkD := fun j : Fin m' => hcovD j x (z : C) hz hzE hxV
  choose kN hzN using hkN
  choose kD hzD using hkD
  have hFN := fun i : Fin m => hholN i (kN i)
  have hFD := fun j : Fin m' => hholD j (kD j)
  choose FN hFNhol hFNval using hFN
  choose FD hFDhol hFDval using hFD

  obtain ⟨NN, hNN⟩ := hcombine (Fin m) Finset.univ (fun i w => w ∈ Pc (LN i (kN i)) (MN i (kN i))) fun i _ =>
    hdisc (LN i (kN i)) (MN i (kN i)) (hLN i (kN i)) (hMN i (kN i)) (hzN i)
  obtain ⟨ND, hND⟩ := hcombine (Fin m') Finset.univ (fun j w => w ∈ Pc (LD j (kD j)) (MD j (kD j))) fun j _ =>
    hdisc (LD j (kD j)) (MD j (kD j)) (hLD j (kD j)) (hMD j (kD j)) (hzD j)

  have hηW' : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ W' := by
    have hpt : (q.base (IsLocalRing.closedPoint C)) ∈ (W' : Set (Limits.pullback f sC : Scheme.{0})) :=
      hqW' (show IsLocalRing.closedPoint C ∈ (⊤ : (Spec (CommRingCat.of C)).Opens) from trivial)
    exact ((genericPoint_spec (Limits.pullback f sC : Scheme.{0})).mem_open_set_iff W'.isOpen).mpr ⟨_, trivial, hpt⟩
  have hηW'U : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ W' ⊓ U := ⟨hηW', hU⟩
  have hZfin := hfin (W' ⊓ U) hηW'U n
  set Z : Set ↥(Omega.affinoid ϖ n) := {ζ : ↥(Omega.affinoid ϖ n) | ∃ x' : AdicPoint K₀ π R, (ζ : C) = x'.toOmega C ∧
      ∃ q' : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC,
        q' ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x').1 ∧
        q' ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
        ¬ ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ (W' ⊓ U))} with hZ
  have hqWU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ (W' ⊓ U) := fun p hp => ⟨hqW' hp, hqU hp⟩
  have hZne : ∀ ζ ∈ Z, (ζ : C) ≠ (z : C) := by
    rintro ζ ⟨x', hζx', q', hq'1, hq'2, hnot⟩ hζz
    have hxx' : x' = x :=
      CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_injective ϖ hF (hζx'.symm.trans (hζz.trans hz))
    subst hxx'
    have hqq' : q' = q := Limits.pullback.hom_ext (by rw [hq'1, hq1]) (by rw [hq'2, hq2])
    subst hqq'
    exact hnot hqWU
  obtain ⟨NZ, hNZ⟩ := hcombine ↥(Omega.affinoid ϖ n) hZfin.toFinset (fun ζ w => w ≠ (ζ : C)) fun ζ hζ => by
    have hne : (ζ : C) - (z : C) ≠ 0 := sub_ne_zero.mpr (hZne ζ (hZfin.mem_toFinset.mp hζ))
    obtain ⟨N, hN⟩ := hrk w₀ _ hw1 hne
    refine ⟨N + 1, fun w hw hwζ => ?_⟩
    rw [hwζ] at hw
    exact (lt_irrefl _ ((hw.trans_lt (hwanti (Nat.lt_succ_self N))).trans_le hN))

  set N : ℕ := (n + 1) + NN + ND + NZ with hNdef
  set D : Set C := {w : C | Valued.v (w - (z : C)) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ N} with hDdef
  have hDaff : D ⊆ Omega.affinoid ϖ n := by
    intro w hw
    have hsmall : Valued.v (w - (z : C)) < Valued.v w₀ ^ n :=
      (hDmono (show n + 1 ≤ N by omega) w hw).trans_lt (hwanti (Nat.lt_succ_self n))
    obtain ⟨h₁, h₂⟩ := hzn
    have hle1 : Valued.v w₀ ^ n ≤ 1 := pow_le_one₀ zero_le' hw1.le
    have h1le : (1 : Γ₀) ≤ (Valued.v w₀)⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hw0).2 hw1.le)
    refine ⟨?_, fun a ha => ?_⟩
    · rw [show w = (z : C) + (w - (z : C)) by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h₁ (hsmall.le.trans (hle1.trans h1le)))
    · have hza : Valued.v w₀ ^ n ≤ Valued.v ((z : C) - algebraMap K₀ C a) := h₂ a ha
      rw [show w - algebraMap K₀ C a = ((z : C) - algebraMap K₀ C a) + (w - (z : C)) by ring,
        Valuation.map_add_eq_of_lt_left _ (hsmall.trans_le hza)]
      exact hza
  have hDΩ : D ⊆ Omega.upperHalfPlane K₀ C := hDaff.trans (Omega.affinoid_subset_upperHalfPlane ϖ n)
  have hDN : ∀ i : Fin m, D ⊆ Pc (LN i (kN i)) (MN i (kN i)) := fun i w hw =>
    hNN w (hDmono (show NN ≤ N by omega) w hw) i (Finset.mem_univ i)
  have hDD : ∀ j : Fin m', D ⊆ Pc (LD j (kD j)) (MD j (kD j)) := fun j w hw =>
    hND w (hDmono (show ND ≤ N by omega) w hw) j (Finset.mem_univ j)
  have hDZ : ∀ w ∈ D, ∀ ζ ∈ Z, w ≠ (ζ : C) := fun w hw ζ hζ =>
    hNZ w (hDmono (show NZ ≤ N by omega) w hw) ζ (hZfin.mem_toFinset.mpr hζ)

  let a : ↥D → C := fun w => ∑ i, cnum i * FN i ⟨(w : C), hDN i w.2⟩
  let b : ↥D → C := fun w => ∑ j, cden j * FD j ⟨(w : C), hDD j w.2⟩
  have hahol : a ∈ Omega.holOn C D := by
    have : a = ∑ i, (fun _ : ↥D => cnum i) * (fun w : ↥D => FN i ⟨(w : C), hDN i w.2⟩) := by
      funext w; simp only [a, Finset.sum_apply, Pi.mul_apply]
    rw [this]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (Omega.IsHolOn.const D (cnum i))
      (CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset C (hDN i) (hFNhol i))
  have hbhol : b ∈ Omega.holOn C D := by
    have : b = ∑ j, (fun _ : ↥D => cden j) * (fun w : ↥D => FD j ⟨(w : C), hDD j w.2⟩) := by
      funext w; simp only [b, Finset.sum_apply, Pi.mul_apply]
    rw [this]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (Omega.IsHolOn.const D (cden j))
      (CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset C (hDD j) (hFDhol j))

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

  have hvalsum : ∀ (y : AdicPoint K₀ π R) (q' : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC)
      (hq'1 : q' ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ y).1)
      (hq'2 : q' ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)))
      (hyV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ y).1) ⁻¹ᵁ V)
      (hq'W : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ W)
      (κ : ℕ) (sec : Fin κ → 𝒳.presheaf.obj (Opposite.op V)) (cst : Fin κ → C),
      LocAux.ev q' W hq'W (∑ k, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom
            ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cst k))) *
          ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (sec k))) =
        ∑ k, cst k * algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
          (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hyV).op).hom ((((Φ y).1).app V).hom (sec k)))) := by
    intro y q' hq'1 hq'2 hyV hq'W κ sec cst
    obtain ⟨hE1, hE2⟩ :=
      CerednikDrinfeld.eval_app_pullback_fst_eq_algebraMap_eval_app f sC (Φ y).1 q' hq'1 hq'2 V hyV W hWV hq'W
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, LocAux.ev_apply, LocAux.ev_apply, hE1, hE2]

  have hmain : ∀ w : ↥D, ∃ (y : AdicPoint K₀ π R) (q' : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC),
      q' ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ y).1 ∧
      q' ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)) ∧
      ((⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ y).1) ⁻¹ᵁ V) ∧
      ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ (W' ⊓ U)) ∧ (w : C) = y.toOmega C := by
    intro w
    obtain ⟨y, -, hy⟩ := CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_surjOn ϖ hF (hDΩ w.2)
    obtain ⟨q', hq'1, hq'2⟩ := hqpt y
    have hwy : (w : C) = y.toOmega C := hy.symm
    have hyV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ y).1) ⁻¹ᵁ V :=
      hoverD ⟨0, hm'⟩ (kD ⟨0, hm'⟩) y (w : C) hwy (hDD ⟨0, hm'⟩ w.2)
    refine ⟨y, q', hq'1, hq'2, hyV, ?_, hwy⟩
    by_contra hnot
    have hmem : (⟨(w : C), hDaff w.2⟩ : ↥(Omega.affinoid ϖ n)) ∈ Z := ⟨y, hwy, q', hq'1, hq'2, hnot⟩
    exact hDZ (w : C) w.2 _ hmem rfl

  refine ⟨N, hDΩ, a, b, hahol, hbhol, ?_, ?_⟩
  ·
    intro w hw
    have hb : b w = LocAux.ev q W hqW Dsec := by
      rw [hDsec, hvalsum x q hq1 hq2 hxV hqW m' den cden]
      simp only [b]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hFDval j x ⟨(w : C), hDD j w.2⟩ (hw.trans hz) hxV]
    rw [hb, ← LocAux.ev_res q hqW hqW' hW'W]
    exact (hDunit.map (LocAux.ev q W' hqW')).ne_zero
  ·
    intro w
    obtain ⟨y, q', hq'1, hq'2, hyV, hq'WU, hwy⟩ := hmain w
    have hq'U : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ U := fun p hp => (hq'WU hp).2
    have hq'W : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ W := fun p hp => hW'W (hq'WU hp).1
    have hq'WU2 : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q' ⁻¹ᵁ (W ⊓ U) :=
      fun p hp => ⟨hW'W (hq'WU hp).1, (hq'WU hp).2⟩
    have hFw : F ⟨(w : C), hDΩ w.2⟩ = LocAux.ev q' U hq'U s := by
      rw [LocAux.ev_apply]
      exact hvalF y ⟨(w : C), hDΩ w.2⟩ hwy q' hq'1 hq'2 hq'U
    have hb : b w = LocAux.ev q' W hq'W Dsec := by
      rw [hDsec, hvalsum y q' hq'1 hq'2 hyV hq'W m' den cden]
      simp only [b]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hFDval j y ⟨(w : C), hDD j w.2⟩ hwy hyV]
    have ha : a w = LocAux.ev q' W hq'W Nsec := by
      rw [hNsec, hvalsum y q' hq'1 hq'2 hyV hq'W m num cnum]
      simp only [a]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hFNval i y ⟨(w : C), hDN i w.2⟩ hwy hyV]
    have hev := congrArg (LocAux.ev q' (W ⊓ U) hq'WU2) hident
    rw [map_mul, LocAux.ev_res q' hq'U hq'WU2 inf_le_right, LocAux.ev_res q' hq'W hq'WU2 inf_le_left,
      LocAux.ev_res q' hq'W hq'WU2 inf_le_left] at hev
    rw [hFw, hb, ha, mul_comm]
    exact hev

end S_CerednikDrinfeld_exists_disc_holOn_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_exists_disc_holOn_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient (solution)
