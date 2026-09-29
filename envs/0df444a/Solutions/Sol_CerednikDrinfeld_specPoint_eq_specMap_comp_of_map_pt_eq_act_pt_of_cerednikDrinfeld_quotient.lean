-- Prove2me | solution 1 for CerednikDrinfeld.specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9825e9d3-4c7e-5cd7-98ca-fbd3747d9970

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_cerednikDrinfeld_apply_eq_of_forall_fr_fr_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

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

    {R : Type} [CommRing R] [Algebra 𝒪 R] [IsLocalRing R] (hR : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (ψ₀ : Onr →ₐ[𝒪] R)

    (τ : R ≃ₐ[𝒪] R) (n : ℤ) (hψτ : ∀ y : Onr, Fr (Fr y) = y → τ (ψ₀ y) = ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y))
    (τn : ∀ k : ℕ, modPow π R k →ₐ[𝒪] modPow π R k)
    (hτn : ∀ (k : ℕ) (a : R), τn k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ a))

    (w : G) (hw : w ∈ Γ) (hw₁ : vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))

    (PX : AdicPoint K₀ π R → (Spec (CommRingCat.of R) ⟶ 𝒳))
    (hPX : ∀ (x : AdicPoint K₀ π R) (k : ℕ),
      Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) ≫ PX x =
        (Θ (modPow π R k) (isNilpotent_algebraMap_modPow π R k)
          (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)})).comp ψ₀), x.pt k)).1)
    (x x' : AdicPoint K₀ π R) (hx' : ∀ k : ℕ, DeligneDatum.map π (τn k) (x'.pt k) = (x.act (σ (w ^ (-n)))).pt k) :
    PX x = Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ PX x' := by
  classical

  set ψk : ∀ k : ℕ, Onr →ₐ[𝒪] modPow π R k := fun k => (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)})).comp ψ₀ with hψk

  have hlev : ∀ k : ℕ, Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) ≫ (Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ PX x') =
      Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) ≫ PX x := by
    intro k

    have hring : (algebraMap R (modPow π R k)).comp τ.toAlgHom.toRingHom = (τn k).toRingHom.comp (algebraMap R (modPow π R k)) := by
      apply RingHom.ext; intro a
      show Ideal.Quotient.mk _ (τ a) = τn k (Ideal.Quotient.mk _ a)
      rw [hτn]
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) ≫ Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) =
        Spec.map (CommRingCat.ofHom (τn k).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
    rw [← Category.assoc, e1, Category.assoc, hPX x' k, hPX x k]

    have e2 : Spec.map (CommRingCat.ofHom (τn k).toRingHom) ≫
        (Θ (modPow π R k) (isNilpotent_algebraMap_modPow π R k) (ψk k, x'.pt k)).1 =
        (Θ (modPow π R k) (isNilpotent_algebraMap_modPow π R k) ((τn k).comp (ψk k), DeligneDatum.map π (τn k) (x'.pt k))).1 := by
      have := hΘnat (modPow π R k) (modPow π R k) (isNilpotent_algebraMap_modPow π R k) (isNilpotent_algebraMap_modPow π R k)
        (τn k) (ψk k, x'.pt k)
      exact (congrArg Subtype.val this).symm
    rw [e2, hx' k]

    have hpar : ∀ y : Onr, Fr (Fr y) = y → ((τn k).comp (ψk k)) y = (frobTwist Onr Fr n (ψk k)) y := by
      intro y hy
      show τn k (Ideal.Quotient.mk _ (ψ₀ y)) = Ideal.Quotient.mk _ (ψ₀ (((Fr ^ n : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) y))
      rw [hτn, hψτ y hy]
      rfl
    rw [CerednikDrinfeld.cerednikDrinfeld_apply_eq_of_forall_fr_fr_eq 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max
      hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv
      (modPow π R k) (isNilpotent_algebraMap_modPow π R k) ((τn k).comp (ψk k)) (frobTwist Onr Fr n (ψk k)) hpar]

    have hv : vdet (σ (w ^ (-n))) = Multiplicative.ofAdd (-n) := by
      rw [map_zpow, map_zpow, hw₁, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    have htw : OmegaNr.IsTwistedAct π Onr Fr vdet (modPow π R k) (σ (w ^ (-n))) (ψk k, x.pt k)
        (frobTwist Onr Fr n (ψk k), (x.act (σ (w ^ (-n)))).pt k) := by
      constructor
      · show frobTwist Onr Fr n (ψk k) = frobTwist Onr Fr (-Multiplicative.toAdd (vdet (σ (w ^ (-n))))) (ψk k)
        rw [hv, toAdd_ofAdd, neg_neg]
      · intro M; rfl
    exact congrArg Subtype.val (hΘinv (modPow π R k) (isNilpotent_algebraMap_modPow π R k) (w ^ (-n)) (Γ.zpow_mem hw _) _ _ htw)

  have hsys : ∀ k : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R k).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R (k + 1)))) ≫ PX x) =
      Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) ≫ PX x := by
    intro k
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨y, hy, huniq⟩ := CerednikDrinfeld.FormalOmega.existsUnique_hom_comp_eq_of_compatible_modPow π R hR
    (fun k => Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R k))) ≫ PX x) hsys
  have h1 : PX x = y := huniq (PX x) (fun k => rfl)
  have h2 : Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ PX x' = y := huniq _ hlev
  rw [h1, h2]

end S_CerednikDrinfeld_specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_specPoint_eq_specMap_comp_of_map_pt_eq_act_pt_of_cerednikDrinfeld_quotient (solution)
