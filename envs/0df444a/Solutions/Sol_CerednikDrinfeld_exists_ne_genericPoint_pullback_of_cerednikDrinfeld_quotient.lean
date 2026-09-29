-- Prove2me | solution 1 for CerednikDrinfeld.exists_ne_genericPoint_pullback_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/daff7751-bf64-5c46-88ad-33c2b62a07b9

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Theorems.Thm_CerednikDrinfeld_BruhatTits_treeLattice_facts_map_evenPart
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Theorems.Thm_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ne_genericPoint_pullback_of_cerednikDrinfeld_quotient
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace N1Aux

theorem countable_of_fg {G : Type} [Group G] {H : Subgroup G} (h : H.FG) : Countable ↥H := by
  classical
  obtain ⟨S, hS⟩ := h
  let φ : FreeGroup ↥S →* G := FreeGroup.lift (fun s : ↥S => (s : G))
  have hrange : φ.range = H := by
    rw [FreeGroup.range_lift_eq_closure, ← hS]
    congr 1
    ext g
    simp
  haveI : Countable (FreeGroup ↥S) := by
    refine Function.Surjective.countable (f := (FreeGroup.mk : List (↥S × Bool) → FreeGroup ↥S)) ?_
    intro x
    induction x using Quot.ind with
    | mk L => exact ⟨L, rfl⟩
  rw [← hrange]
  exact Function.Surjective.countable (f := φ.rangeRestrict) φ.rangeRestrict_surjective

theorem exists_mem_upperHalfPlane
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (π : 𝒪) (hπ : Irreducible π)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (C : Type) [Field C] [Algebra K₀ C] [Algebra 𝒪 C] [IsScalarTower 𝒪 K₀ C] [IsAlgClosed C] :
    ∃ z : C, z ∈ Omega.upperHalfPlane K₀ C := by
  classical
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (algebraMap 𝒪 C π)
  refine ⟨s, ?_⟩
  rw [Omega.mem_upperHalfPlane_iff]
  intro x hx

  have hx2 : x * x = algebraMap 𝒪 K₀ π := by
    apply (algebraMap K₀ C).injective
    rw [map_mul, hx, ← hs, IsScalarTower.algebraMap_apply 𝒪 K₀ C]

  have hb : (IsFractionRing.den 𝒪 x : 𝒪) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  set a := IsFractionRing.num 𝒪 x with ha
  set b := (IsFractionRing.den 𝒪 x : 𝒪) with hb'
  have hxab : algebraMap 𝒪 K₀ a / algebraMap 𝒪 K₀ b = x := IsFractionRing.mk'_num_den' 𝒪 x
  have hinj := IsFractionRing.injective 𝒪 K₀
  have hab : a * a = π * (b * b) := by
    apply hinj
    have hbK : algebraMap 𝒪 K₀ b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    rw [map_mul, map_mul, map_mul, ← hx2, ← hxab]
    field_simp

  have hprime : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπ
  have hpa : π ∣ a := by
    have : π ∣ a * a := ⟨b * b, hab⟩
    exact (hprime.dvd_or_dvd this).elim id id
  obtain ⟨k, hk⟩ := hpa
  have hpb : π ∣ b := by
    have h2 : π * (k * k) = b * b := by
      have := hab
      rw [hk] at this
      have : π * (π * (k * k)) = π * (b * b) := by rw [← this]; ring
      exact mul_left_cancel₀ hprime.ne_zero this
    have : π ∣ b * b := ⟨k * k, h2.symm⟩
    exact (hprime.dvd_or_dvd this).elim id id
  have hrel : IsRelPrime a b := IsFractionRing.num_den_reduced 𝒪 x
  exact hπ.not_isUnit (hrel ⟨k, hk⟩ hpb)

end N1Aux

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

    (hvtf : ∃ Γ'' : Subgroup G, Γ'' ≤ Γ' ∧ Γ''.relIndex Γ' ≠ 0 ∧ ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1)
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

    (htame : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀,
      Valued.v ((Nat.card ↥{g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v} : ℕ) : C) = 1)
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
    :
    ∃ x : ↥(Limits.pullback f sC), x ≠ genericPoint (Limits.pullback f sC : Scheme.{0}) := by
  classical
  haveI : IsDiscreteValuationRing 𝒪 := hdvr

  obtain ⟨-, -, -, -, -, hFG, -⟩ :=
    CerednikDrinfeld.BruhatTits.treeLattice_facts_map_evenPart 𝒪 hdvr π hπ hres K₀ vdet hvdet G σ Γ Γ' hΓ' ρ hρ hdisc hcocpt
  haveI : Countable ↥(Γ'.map ρ) := N1Aux.countable_of_fg hFG

  obtain ⟨z, hz⟩ := N1Aux.exists_mem_upperHalfPlane 𝒪 π hπ K₀ C
  obtain ⟨-, z₀, -, hz₀, -, hzz₀, -⟩ :=
    CerednikDrinfeld.Omega.exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean K₀ C ϖ hrk
      ((Γ'.map ρ).subtype) hz

  obtain ⟨x, -, hx⟩ := CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_surjOn ϖ hF hz
  obtain ⟨x₀, -, hx₀⟩ := CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_surjOn ϖ hF hz₀

  have hne : Φ x ≠ Φ x₀ := by
    intro heq
    obtain ⟨γ, hγ, hx₀eq⟩ := (hΦ.2.2.1 x x₀).mp heq
    have hact := CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_act ϖ hF (σ γ) x
    rw [← hx₀eq, ← hρ] at hact
    have h1 : x₀.toOmega C = z₀ := hx₀
    have h2 : x.toOmega C = z := hx
    rw [h1, h2] at hact
    exact hzz₀ ⟨ρ γ, Subgroup.mem_map_of_mem ρ hγ⟩ hact.symm

  obtain ⟨-, -, -, hinjC, -⟩ := hΦ
  set c₁ := Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x).1 with hc₁
  set c₂ := Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (Φ x₀).1 with hc₂
  have hc : c₁ ≠ c₂ := fun h => hne (hinjC h)

  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ Scheme.specOver (𝒪 := 𝒪) R = sC := by
    rw [hsC, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← IsScalarTower.algebraMap_eq 𝒪 K₀ C, ← IsScalarTower.algebraMap_eq 𝒪 R C]
  have w₁ : c₁ ≫ f = 𝟙 _ ≫ sC := by rw [hc₁, Category.assoc, (Φ x).2, hSpec, Category.id_comp]
  have w₂ : c₂ ≫ f = 𝟙 _ ≫ sC := by rw [hc₂, Category.assoc, (Φ x₀).2, hSpec, Category.id_comp]
  set p₁ := Limits.pullback.lift c₁ (𝟙 _) w₁ with hp₁
  set p₂ := Limits.pullback.lift c₂ (𝟙 _) w₂ with hp₂
  have hp : p₁ ≠ p₂ := by
    intro h
    apply hc
    rw [show c₁ = p₁ ≫ Limits.pullback.fst f sC from (Limits.pullback.lift_fst _ _ _).symm,
      show c₂ = p₂ ≫ Limits.pullback.fst f sC from (Limits.pullback.lift_fst _ _ _).symm, h]

  haveI : LocallyOfFiniteType (Limits.pullback.snd f sC) := inferInstance
  obtain ⟨huniq, -, -⟩ := AlgebraicGeometry.eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed
    C (Limits.pullback.snd f sC)
  have hpts : p₁.base (IsLocalRing.closedPoint C) ≠ p₂.base (IsLocalRing.closedPoint C) := fun h =>
    hp (huniq p₁ p₂ (Limits.pullback.lift_snd _ _ _) (Limits.pullback.lift_snd _ _ _) h)
  by_cases h1 : p₁.base (IsLocalRing.closedPoint C) = genericPoint (Limits.pullback f sC : Scheme.{0})
  · exact ⟨p₂.base (IsLocalRing.closedPoint C), fun h2 => hpts (h1.trans h2.symm)⟩
  · exact ⟨p₁.base (IsLocalRing.closedPoint C), h1⟩

end S_CerednikDrinfeld_exists_ne_genericPoint_pullback_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ne_genericPoint_pullback_of_cerednikDrinfeld_quotient (solution)
