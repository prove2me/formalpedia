-- Prove2me | solution 1 for CerednikDrinfeld.exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a1f81d38-7b96-526a-aa0a-1641e2e4362e

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_exists_polynomial_ne_zero_mul_pullback_mem_holOn_edgeRegion_of_cover_clearing_of_cerednikDrinfeld_quotient
import Theorems.Thm_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain
import Theorems.Thm_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
import Theorems.Thm_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset
import Theorems.Thm_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

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

    (hcover : (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U)),
        ∃ (ℓ : ℕ) (V : Fin ℓ → 𝒳.Opens),
          (∀ x : AdicPoint K₀ π R, ∃ a : Fin ℓ, (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ (V a)) ∧
          ∀ a : Fin ℓ, ∃ (W : (Limits.pullback f sC).Opens) (hWV : W ≤ (Limits.pullback.fst f sC) ⁻¹ᵁ (V a))
            (hWη : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ W)
            (m : ℕ) (num : Fin m → 𝒳.presheaf.obj (Opposite.op (V a))) (cnum : Fin m → C)
            (m' : ℕ) (den : Fin m' → 𝒳.presheaf.obj (Opposite.op (V a))) (cden : Fin m' → C),

            (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
                ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app (V a)).hom (den j))) ≠ 0 ∧

            ((Limits.pullback f sC).presheaf.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op).hom s *
                ((Limits.pullback f sC).presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op).hom (∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
                    ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app (V a)).hom (den j))) =
              ((Limits.pullback f sC).presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op).hom (∑ i, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cnum i))) *
                    ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app (V a)).hom (num i)))))

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

        (∀ n : ℕ, ∃ a b : ↥(Omega.affinoid ϖ n) → C, a ∈ Omega.holOn C (Omega.affinoid ϖ n) ∧ b ∈ Omega.holOn C (Omega.affinoid ϖ n) ∧
          (∃ z : ↥(Omega.affinoid ϖ n), b z ≠ 0) ∧
          ∀ z : ↥(Omega.affinoid ϖ n), b z ≠ 0 →
            b z * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ = a z)) := by
  classical
  intro U hU s F hvalF

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

  have hpoly : ∀ (N : ℕ) (p : Polynomial C),
      (fun z : ↥(Omega.affinoid ϖ N) => p.eval (z : C)) ∈ Omega.holOn C (Omega.affinoid ϖ N) := by
    intro N p
    have hpf : (⟨p, 1⟩ : Omega.RatPair C).IsPoleFreeOn (Omega.affinoid ϖ N) := fun z _ => by
      simp
    obtain ⟨b, hb⟩ := Omega.RatPair.exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid ϖ N ⟨p, 1⟩ hpf
    have h := Omega.isHolOn_ratPair (S := Omega.affinoid ϖ N) ⟨p, 1⟩ hpf ⟨b, hb⟩
    have heq : (fun z : ↥(Omega.affinoid ϖ N) => Omega.RatPair.evalAt (⟨p, 1⟩ : Omega.RatPair C) (z : C)) =
        fun z : ↥(Omega.affinoid ϖ N) => p.eval (z : C) := by
      funext z
      simp [Omega.RatPair.evalAt]
    rw [Omega.mem_holOn_iff, ← heq]
    exact h

  have hregion : ∀ (N : ℕ) (S : Set C) (c : K₀) (m : ℤ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀),
      (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1] →
      S = (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) →
      ∀ (hS : S ⊆ Omega.affinoid ϖ N), ∃ b : Polynomial C, b ≠ 0 ∧
        (fun z : ↥S => b.eval (z : C) * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ N (hS z.2)⟩) ∈ Omega.holOn C S := by
    intro N S c m g hg hSE hS
    subst hSE
    exact CerednikDrinfeld.exists_polynomial_ne_zero_mul_pullback_mem_holOn_edgeRegion_of_cover_clearing_of_cerednikDrinfeld_quotient
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd
      Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv ϖ hF ψ₀ hrk hval hex Φ hΦ sC hsC hcover htube hfin U hU s F hvalF
      c m g hg N hS

  have key : ∀ N : ℕ, 1 ≤ N → ∃ b : Polynomial C, b ≠ 0 ∧
      (fun z : ↥(Omega.affinoid ϖ N) => b.eval (z : C) * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ N z.2⟩) ∈
        Omega.holOn C (Omega.affinoid ϖ N) := by
    intro N hN
    obtain ⟨k, P, g, t, ϱ, Z, hP, haff, hsub, hcov, hϱ, hout, hin, hrim⟩ :=
      CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid 𝒪 K₀ C ϖ π hπ hϖπ hint hv N hN
    have hreg : ∀ j : Fin (k + 1), ∃ b : Polynomial C, b ≠ 0 ∧
        (fun z : ↥(P j) => b.eval (z : C) * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ N (hsub j z.2)⟩) ∈
          Omega.holOn C (P j) := by
      intro j
      obtain ⟨c, m, hg⟩ := haff j
      exact hregion N (P j) c m (g j) hg (hP j) (hsub j)
    choose b hb0 hb using hreg
    obtain ⟨q, hq0, hq⟩ :=
      CerednikDrinfeld.Omega.exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
        K₀ C ϖ N P hsub (fun z : ↥(Omega.affinoid ϖ N) => F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ N z.2⟩)
        b hb0 (fun j => fun z : ↥(P j) => (b j).eval (z : C) * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ N (hsub j z.2)⟩)
        hb (fun j z _ => rfl)
    refine ⟨q, hq0, ?_⟩
    exact CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_of_chain C (Omega.affinoid ϖ N) k P hsub hcov t ϱ Z hϱ hout hin hrim
      (fun z : ↥(Omega.affinoid ϖ N) => q.eval (z : C) * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ N z.2⟩) hq

  have hnonroot : ∀ (n : ℕ) (b : Polynomial C), b ≠ 0 → ∃ z : ↥(Omega.affinoid ϖ n), b.eval (z : C) ≠ 0 := by
    intro n b hb0
    obtain ⟨z₀, hz₀⟩ := CerednikDrinfeld.Omega.affinoid_nonempty_of_exists_finset_cover K₀ C ϖ n
      (CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient 𝒪 K₀ π hπ C hint hv hq ϖ n)

    set w : C := algebraMap K₀ C ϖ.ϖ with hw
    have hw0 : 0 < Valued.v w := ϖ.pos
    have hw1 : Valued.v w < 1 := ϖ.lt_one
    have hwne : w ≠ 0 := fun h => by rw [h, map_zero] at hw0; exact lt_irrefl _ hw0
    let e : ℕ → C := fun i => z₀ + w ^ (n + 1 + i)
    have hemem : ∀ i, e i ∈ Omega.affinoid ϖ n := by
      intro i
      obtain ⟨h₁, h₂⟩ := hz₀
      have hsmall : Valued.v (w ^ (n + 1 + i)) < Valued.v w ^ n := by
        rw [Valuation.map_pow]
        exact pow_lt_pow_right_of_lt_one₀ hw0 hw1 (by omega)
      have hle1 : Valued.v w ^ n ≤ 1 := pow_le_one₀ zero_le' hw1.le
      have h1le : (1 : Γ₀) ≤ (Valued.v w)⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hw0).2 hw1.le)
      refine ⟨?_, fun a ha => ?_⟩
      · calc Valued.v (z₀ + w ^ (n + 1 + i)) ≤ max (Valued.v z₀) (Valued.v (w ^ (n + 1 + i))) := Valuation.map_add _ _ _
          _ ≤ (Valued.v w)⁻¹ ^ n := max_le h₁ (hsmall.le.trans (hle1.trans h1le))
      · have hza : Valued.v w ^ n ≤ Valued.v (z₀ - algebraMap K₀ C a) := h₂ a ha
        have hlt : Valued.v (w ^ (n + 1 + i)) < Valued.v (z₀ - algebraMap K₀ C a) := hsmall.trans_le hza
        rw [show z₀ + w ^ (n + 1 + i) - algebraMap K₀ C a = (z₀ - algebraMap K₀ C a) + w ^ (n + 1 + i) by ring,
          Valuation.map_add_eq_of_lt_left _ hlt]
        exact hza
    have heinj : Function.Injective e := by
      intro i j hij
      have h : w ^ (n + 1 + i) = w ^ (n + 1 + j) := add_left_cancel hij
      have h' := congrArg Valued.v h
      rw [Valuation.map_pow, Valuation.map_pow] at h'
      have := (pow_right_strictAnti₀ hw0 hw1).injective h'
      omega
    by_contra hall
    have hroots : Set.range e ⊆ {x : C | b.IsRoot x} := by
      rintro x ⟨i, rfl⟩
      by_contra hx
      exact hall ⟨⟨e i, hemem i⟩, hx⟩
    exact hb0 (Polynomial.eq_zero_of_infinite_isRoot b ((Set.infinite_range_of_injective heinj).mono hroots))

  intro n
  obtain ⟨b, hb0, hb⟩ := key (n + 1) (Nat.le_add_left 1 n)
  have hmono : Omega.affinoid ϖ n ⊆ Omega.affinoid ϖ (n + 1) := Omega.affinoid_mono ϖ (Nat.le_succ n)
  refine ⟨fun z => b.eval (z : C) * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩, fun z => b.eval (z : C),
    ?_, hpoly n b, hnonroot n b hb0, fun z _ => rfl⟩
  exact CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset C hmono hb

end S_CerednikDrinfeld_exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient (solution)
