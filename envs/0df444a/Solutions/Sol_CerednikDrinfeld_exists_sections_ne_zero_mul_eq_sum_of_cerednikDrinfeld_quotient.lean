-- Prove2me | solution 1 for CerednikDrinfeld.exists_sections_ne_zero_mul_eq_sum_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a348e826-fa71-5497-adb4-c35a362ff57d

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_sections_ne_zero_mul_eq_sum_of_cerednikDrinfeld_quotient
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

namespace EDB

section Frame
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {π : 𝒪} {ϖ : PseudoUniformizer K C} {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C]
  [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]

theorem isUnit_iff_v_eq_one (hF : IsAdicFrame π ϖ R) (r : R) : IsUnit r ↔ Valued.v (algebraMap R C r) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    apply le_antisymm (hF.v_algebraMap_le_one _)
    have h1 := hF.v_algebraMap_le_one ((u⁻¹ : Rˣ) : R)
    have hmul : Valued.v (algebraMap R C (u : R)) * Valued.v (algebraMap R C ((u⁻¹ : Rˣ) : R)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : Γ₀) = Valued.v (algebraMap R C (u : R)) * Valued.v (algebraMap R C ((u⁻¹ : Rˣ) : R)) := hmul.symm
      _ ≤ Valued.v (algebraMap R C (u : R)) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _
  · intro h
    have hne : algebraMap R C r ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
    obtain ⟨s, hs⟩ := (hF.range_eq (algebraMap R C r)⁻¹).1 (by rw [map_inv₀, h, inv_one])
    refine ⟨⟨r, s, hF.injective ?_, hF.injective ?_⟩, rfl⟩
    · rw [map_mul, hs, mul_inv_cancel₀ hne, map_one]
    · rw [map_mul, hs, inv_mul_cancel₀ hne, map_one]

theorem v_lt_one_iff_not_isUnit (hF : IsAdicFrame π ϖ R) (r : R) : Valued.v (algebraMap R C r) < 1 ↔ ¬ IsUnit r := by
  rw [isUnit_iff_v_eq_one hF, lt_iff_le_and_ne]
  exact ⟨fun h => h.2, fun h => ⟨hF.v_algebraMap_le_one r, h⟩⟩

theorem nontrivial (hF : IsAdicFrame π ϖ R) : Nontrivial R :=
  ⟨⟨0, 1, fun h => by have := congrArg (algebraMap R C) h; rw [map_zero, map_one] at this; exact zero_ne_one this⟩⟩

theorem isLocalRing (hF : IsAdicFrame π ϖ R) : IsLocalRing R := by
  haveI := nontrivial hF
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  rw [mem_nonunits_iff, ← v_lt_one_iff_not_isUnit hF] at ha hb ⊢
  rw [map_add]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)

theorem not_isUnit_algebraMap_pi (hF : IsAdicFrame π ϖ R) : ¬ IsUnit (algebraMap 𝒪 R π) := by
  rw [← v_lt_one_iff_not_isUnit hF, ← IsScalarTower.algebraMap_apply]
  exact hF.v_algebraMap_lt_one

theorem exists_v_pi_pow_lt (hF : IsAdicFrame π ϖ R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (y : C) (hy : y ≠ 0) : ∃ n : ℕ, Valued.v (algebraMap 𝒪 C π) ^ n < Valued.v y := by
  have hπ0 : algebraMap 𝒪 C π ≠ 0 := fun h => by
    have := hF.v_algebraMap_pos; rw [h, map_zero] at this; exact lt_irrefl _ this
  obtain ⟨n, hn⟩ := hrk (algebraMap 𝒪 C π) (y * algebraMap 𝒪 C π) hF.v_algebraMap_lt_one (mul_ne_zero hy hπ0)
  refine ⟨n, lt_of_le_of_lt hn ?_⟩
  rw [map_mul]
  have hy' : 0 < Valued.v y := (Valuation.pos_iff _).2 hy
  calc Valued.v y * Valued.v (algebraMap 𝒪 C π) < Valued.v y * 1 := mul_lt_mul_of_pos_left hF.v_algebraMap_lt_one hy'
    _ = Valued.v y := mul_one _

end Frame
end EDB

namespace EDB

theorem eq_univ_of_isOpen_of_mem {R : Type} [CommRing R] [IsLocalRing R] (U : Set (PrimeSpectrum R))
    (hU : IsOpen U) (hm : (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈ U) : U = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hle : q ≤ ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ := IsLocalRing.le_maximalIdeal q.2.ne_top
  have hcl := (PrimeSpectrum.le_iff_mem_closure q _).1 hle
  rw [mem_closure_iff] at hcl
  obtain ⟨q', hq'U, hq'⟩ := hcl U hU hm
  rw [Set.mem_singleton_iff] at hq'
  exact hq' ▸ hq'U

theorem top_le_preimage_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)
    {X : Scheme.{0}} (P : Spec (CommRingCat.of R) ⟶ X) (U : X.Opens)
    (h : (⊤ : (Spec (CommRingCat.of (R ⧸ I))).Opens) ≤ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ P) ⁻¹ᵁ U) :
    (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ U := by
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ IsLocalRing.maximalIdeal R := by rw [Ideal.mk_ker]; exact hIm
  haveI hp : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  let q₀ : PrimeSpectrum (R ⧸ I) := ⟨(IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I), hp⟩
  have hq₀ : PrimeSpectrum.comap (Ideal.Quotient.mk I) q₀ = ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ := by
    ext1
    show Ideal.comap (Ideal.Quotient.mk I) ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)) = IsLocalRing.maximalIdeal R
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    change IsLocalRing.maximalIdeal R ⊔ RingHom.ker (Ideal.Quotient.mk I) = _
    exact sup_eq_left.2 hker
  have hm : (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈ SetLike.coe (P ⁻¹ᵁ U) := by
    have := h (show q₀ ∈ (⊤ : (Spec (CommRingCat.of (R ⧸ I))).Opens) from trivial)

    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ P).base q₀ ∈ (U : Set _) at this
    rw [Scheme.Hom.comp_base, TopCat.comp_app, Spec.map_base] at this
    change P.base (PrimeSpectrum.comap (Ideal.Quotient.mk I) q₀) ∈ (U : Set _) at this
    rwa [hq₀] at this
  intro q _
  have huniv := eq_univ_of_isOpen_of_mem (SetLike.coe (P ⁻¹ᵁ U)) (P ⁻¹ᵁ U).isOpen hm
  exact Set.eq_univ_iff_forall.1 huniv q

end EDB

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
    [IsIntegral (Limits.pullback f sC)] :
    (∀ (U : (Limits.pullback f sC).Opens) (hU : genericPoint (Limits.pullback f sC : Scheme.{0}) ∈ U) (s : (Limits.pullback f sC).presheaf.obj (Opposite.op U))
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
                ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j)))))) := by
  classical
  haveI := hdvr
  haveI hloc : IsLocalRing R := EDB.isLocalRing hF
  intro U hU s x q hqf hqs

  obtain ⟨y, hy⟩ := 𝒳.affineCover.covers ((Φ x).1.base (IsLocalRing.closedPoint R))
  let V : 𝒳.Opens := (𝒳.affineCover.f (𝒳.affineCover.idx ((Φ x).1.base (IsLocalRing.closedPoint R)))).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  have hxV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ V := by
    intro p _
    have huniv := EDB.eq_univ_of_isOpen_of_mem (SetLike.coe (((Φ x).1) ⁻¹ᵁ V)) (((Φ x).1) ⁻¹ᵁ V).isOpen
      (show (Φ x).1.base _ ∈ V from ⟨y, hy⟩)
    exact Set.eq_univ_iff_forall.1 huniv p

  obtain ⟨hW, hgen⟩ := AlgebraicGeometry.isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen
    ((algebraMap K₀ C).comp (algebraMap 𝒪 K₀)) f sC hsC V hV
  set W : (Limits.pullback f sC).Opens := (Limits.pullback.fst f sC) ⁻¹ᵁ V with hWdef
  have hWV : W ≤ (Limits.pullback.fst f sC) ⁻¹ᵁ V := le_rfl
  have hqW : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ W := by
    rw [hWdef, ← Scheme.Hom.comp_preimage, hqf, Scheme.Hom.comp_preimage]
    intro p _
    exact hxV (Set.mem_univ _)
  have hPW : q.base (IsLocalRing.closedPoint C) ∈ W := hqW (Set.mem_univ _)
  have hWη : genericPoint ((Limits.pullback f sC) : Scheme.{0}) ∈ W :=
    ((genericPoint_spec ((Limits.pullback f sC) : Scheme.{0})).mem_open_set_iff W.isOpen).2 ⟨_, Set.mem_univ _, hPW⟩
  haveI : Nonempty (W : Set ↥(Limits.pullback f sC)) := ⟨⟨_, hPW⟩⟩
  haveI : Nonempty W := ⟨⟨_, hPW⟩⟩
  haveI hfrac : IsFractionRing ↑((Limits.pullback f sC).presheaf.obj (Opposite.op W)) ↑(Limits.pullback f sC).functionField :=
    functionField_isFractionRing_of_isAffineOpen (Limits.pullback f sC) W hW

  set η := genericPoint ((Limits.pullback f sC) : Scheme.{0}) with hη
  set P := q.base (IsLocalRing.closedPoint C) with hP
  set sη := ((Limits.pullback f sC).presheaf.germ U η hU).hom s with hsη
  have hgermW : ∀ t : (Limits.pullback f sC).presheaf.obj (Opposite.op W),
      algebraMap _ ↑(Limits.pullback f sC).functionField t = ((Limits.pullback f sC).presheaf.germ W η hWη).hom t := fun t => rfl

  have key : ∃ (a b : (Limits.pullback f sC).presheaf.obj (Opposite.op W)), b ≠ 0 ∧
      sη * ((Limits.pullback f sC).presheaf.germ W η hWη).hom b = ((Limits.pullback f sC).presheaf.germ W η hWη).hom a ∧
      ((⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U → IsUnit (((Limits.pullback f sC).presheaf.germ W P hPW).hom b)) := by
    by_cases hqU : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ U
    · have hPU : P ∈ U := hqU (Set.mem_univ _)
      let P' : ↥W := ⟨P, hPW⟩
      letI := TopCat.Presheaf.algebra_section_stalk (Limits.pullback f sC).presheaf P'
      haveI := hW.isLocalization_stalk P'
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (M := (hW.primeIdealOf P').asIdeal.primeCompl)
        (S := (Limits.pullback f sC).presheaf.stalk (P' : ↥(Limits.pullback f sC))) (((Limits.pullback f sC).presheaf.germ U (P' : ↥(Limits.pullback f sC)) hPU).hom s)
      refine ⟨a, b, ?_, ?_, fun _ => ?_⟩
      · intro hb0
        apply b.2
        rw [hb0]; exact Ideal.zero_mem _
      ·
        have h2 := congrArg (algebraMap ((Limits.pullback f sC).presheaf.stalk (P' : ↥(Limits.pullback f sC))) ↑(Limits.pullback f sC).functionField) hab
        rw [map_mul] at h2
        have e1 : algebraMap ((Limits.pullback f sC).presheaf.stalk (P' : ↥(Limits.pullback f sC))) ↑(Limits.pullback f sC).functionField (((Limits.pullback f sC).presheaf.germ U (P' : ↥(Limits.pullback f sC)) hPU).hom s) = sη :=
          TopCat.Presheaf.germ_stalkSpecializes_apply _ hPU (genericPoint_specializes _) s
        have e2 : ∀ t : (Limits.pullback f sC).presheaf.obj (Opposite.op W),
            algebraMap ((Limits.pullback f sC).presheaf.stalk (P' : ↥(Limits.pullback f sC))) ↑(Limits.pullback f sC).functionField (algebraMap _ ((Limits.pullback f sC).presheaf.stalk (P' : ↥(Limits.pullback f sC))) t) =
              ((Limits.pullback f sC).presheaf.germ W η hWη).hom t := fun t =>
          TopCat.Presheaf.germ_stalkSpecializes_apply _ P'.2 (genericPoint_specializes _) t
        rw [e1, e2, e2] at h2
        exact h2
      · show IsUnit (algebraMap _ ((Limits.pullback f sC).presheaf.stalk (P' : ↥(Limits.pullback f sC))) (b : (Limits.pullback f sC).presheaf.obj (Opposite.op W)))
        exact (IsLocalization.AtPrime.isUnit_to_map_iff _ (hW.primeIdealOf P').asIdeal (b : _)).2 b.2
    · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := (Limits.pullback f sC).presheaf.obj (Opposite.op W)) sη
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      refine ⟨a, b, hb0, ?_, fun h => absurd h hqU⟩
      have hbK : algebraMap _ ↑(Limits.pullback f sC).functionField b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      show sη * algebraMap _ ↑(Limits.pullback f sC).functionField b = algebraMap _ ↑(Limits.pullback f sC).functionField a
      rw [← hab, div_mul_cancel₀ _ hbK]
  obtain ⟨a, b, hb0, hab, hunit⟩ := key
  obtain ⟨m, num, cnum, ha⟩ := hgen a
  obtain ⟨m', den, cden, hbsum⟩ := hgen b

  have hres : ∀ t : (Limits.pullback f sC).presheaf.obj (Opposite.op ((Limits.pullback.fst f sC) ⁻¹ᵁ V)),
      ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom t = t := by
    intro t
    have : (homOfLE hWV) = 𝟙 _ := homOfLE_refl _
    rw [this, op_id, CategoryTheory.Functor.map_id]; rfl
  have hSa : ∑ i, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom
        ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cnum i))) *
        ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (num i)) = a := by
    rw [ha]; refine Finset.sum_congr rfl fun i _ => ?_; rw [hres]
  have hSb : ∑ j, ((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom
        ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (cden j))) *
        ((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom (den j)) = b := by
    rw [hbsum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [hres]
  refine ⟨V, hxV, W, hWV, hqW, hWη, m, num, cnum, m', den, cden, ?_, ?_, ?_⟩
  · rw [hSb]; exact hb0
  · rw [hSa, hSb]
    have hηWU : η ∈ W ⊓ U := ⟨hWη, hU⟩
    apply germ_injective_of_isIntegral _ η hηWU
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact hab
  · intro hqU
    refine ⟨(Limits.pullback f sC).basicOpen b, ((Limits.pullback f sC).basicOpen_le b).trans le_rfl, ?_, ?_⟩
    · intro p _
      have hp : p = IsLocalRing.closedPoint C := Subsingleton.elim _ _
      show q.base p ∈ (Limits.pullback f sC).basicOpen b
      rw [hp, Scheme.mem_basicOpen _ b _ hPW]
      exact hunit hqU
    · rw [hSb]
      exact RingedSpace.isUnit_res_basicOpen _ b

end S_CerednikDrinfeld_exists_sections_ne_zero_mul_eq_sum_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_exists_sections_ne_zero_mul_eq_sum_of_cerednikDrinfeld_quotient (solution)
