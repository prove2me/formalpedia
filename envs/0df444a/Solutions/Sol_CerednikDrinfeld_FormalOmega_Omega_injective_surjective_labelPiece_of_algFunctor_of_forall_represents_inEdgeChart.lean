-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/72ad3c6a-b74b-5bd6-977b-81e203d32d45

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (PR : AlgFunctor C)
    (hsheaf : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i)

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      PR.obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (φ : S →ₐ[C] S') (x : PR.obj S),
      θ S' (PR.map φ x) = (Omega K₀ π).map (φ.restrictScalars 𝒪) (θ S x))

    {L : Type} (lab : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S],
      (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) → PR.obj S → L)
    (hlabnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [CommRing S'] [Algebra C S'] [IsNoetherianRing S']
      [Nontrivial S'] (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (hS' : ∀ e : S', IsIdempotentElem e → e = 0 ∨ e = 1)
      (g : S →ₐ[C] S') (x : PR.obj S), lab S' hS' (PR.map g x) = lab S hS x)
    (ℓ : L)
    (Pres : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S], PR.obj S → Prop)

    (hPa : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (hc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : PR.obj S), Pres S x → lab S hc x = ℓ)

    (hPb : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [IsLocalRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (hc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : PR.obj S), lab S hc x = ℓ → Pres S x)

    (hpts : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      (∀ x x' : PR.obj k, Pres k x → Pres k x' → θ k x = θ k x' → x = x') ∧
      (∀ d : (Omega K₀ π).obj k, ∃ x : PR.obj k, Pres k x ∧ θ k x = d))

    (het : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : PR.obj S₀) (d : (Omega K₀ π).obj S), Pres S₀ x₀ →
        θ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : PR.obj S, Pres S x ∧ PR.map p x = x₀ ∧ θ S x = d)

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (hrep : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) K₀,
      ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) (_ : LocallyOfFiniteType fX)
        (e : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
          (Scheme.nilpPoints fX).obj S → PR.obj S),

        (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
            (y : (Scheme.nilpPoints fX).obj S)
            (y' : (Scheme.nilpPoints fX).obj S'),
            y'.1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ y.1 → e S' y' = PR.map φ (e S y)) ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
            (y y' : (Scheme.nilpPoints fX).obj S), e S y = e S y' → y = y') ∧

        (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (x : PR.obj S),
            (∃ y : (Scheme.nilpPoints fX).obj S, e S y = x) ↔
              DeligneDatum.InEdgeChart π (θ S x) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
                (FullLattice.act γ (stdFullLattice K₀)))) :
    ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      (∀ x x' : PR.obj S,
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) (φ : S →ₐ[C] k),
            lab k hk (PR.map φ x) = ℓ) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) (φ : S →ₐ[C] k),
            lab k hk (PR.map φ x') = ℓ) →
          θ S x = θ S x' → x = x') ∧
      (∀ d : (Omega K₀ π).obj S, ∃ x : PR.obj S,
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) (φ : S →ₐ[C] k),
            lab k hk (PR.map φ x) = ℓ) ∧ θ S x = d) := by
  classical

  have hconn_local : ∀ (S : Type) [CommRing S] [IsLocalRing S] (e : S), IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro S _ _ e he
    by_cases hu : IsUnit e
    · right
      have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
      have h2 : 1 - e = 0 := (hu.mul_right_eq_zero).mp h1
      linear_combination -h2
    · by_cases hu' : IsUnit (1 - e)
      · left
        have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
        exact (hu'.mul_right_eq_zero).mp h1
      · exfalso
        have hm : e ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hu
        have hm' : 1 - e ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hu'
        have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
          have := Ideal.add_mem _ hm hm'; rwa [add_sub_cancel] at this
        exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

  have geomPt : ∀ (S : Type) [CommRing S] [Nontrivial S] [Algebra C S],
      ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra C k), Nonempty (S →ₐ[C] k) := by
    intro S _ _ _
    obtain ⟨m, hm⟩ := Ideal.exists_maximal S
    letI : Field (S ⧸ m) := Ideal.Quotient.field m
    let k := AlgebraicClosure (S ⧸ m)
    letI : Algebra S k := ((algebraMap (S ⧸ m) k).comp (Ideal.Quotient.mk m)).toAlgebra
    letI : Algebra C k := ((algebraMap S k).comp (algebraMap C S)).toAlgebra
    exact ⟨k, inferInstance, inferInstance, inferInstance, ⟨⟨algebraMap S k, fun _ => rfl⟩⟩⟩

  let good : ∀ (S : Type) [CommRing S] [Algebra C S], PR.obj S → Prop := fun S _ _ x =>
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) (φ : S →ₐ[C] k),
      lab k hk (PR.map φ x) = ℓ
  have good_map : ∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S') (x : PR.obj S),
      good S x → good S' (PR.map φ x) := by
    intro S S' _ _ _ _ φ x hx k _ _ _ hk φ'
    rw [← PR.map_comp]
    exact hx k hk (φ'.comp φ)
  have good_of_pres : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (hc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : PR.obj S), Pres S x → good S x := by
    intro S _ _ _ _ _ _ hc x hx k _ _ _ hk φ
    rw [hlabnat S k hc hk φ x]
    exact hPa S hc x hx
  have lab_of_good : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Nontrivial S]
      (hc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (x : PR.obj S), good S x → lab S hc x = ℓ := by
    intro S _ _ _ _ hc x hg
    obtain ⟨k, _, _, _, ⟨φ⟩⟩ := geomPt S
    rw [← hlabnat S k hc (hconn_local k) φ x]
    exact hg k (hconn_local k) φ
  have pres_of_good : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [IsLocalRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (x : PR.obj S), good S x → Pres S x := by
    intro S _ _ _ _ _ _ x hg
    exact hPb S (hconn_local S) x (lab_of_good S (hconn_local S) x hg)
  let PRℓ : AlgFunctor C :=
    { obj := fun S _ _ => {x : PR.obj S // good S x}
      map := fun φ x => ⟨PR.map φ x.1, good_map _ _ φ x.1 x.2⟩
      map_id := fun x => Subtype.ext (PR.map_id x.1)
      map_comp := fun f g' x => Subtype.ext (PR.map_comp f g' x.1) }
  let θℓ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      PRℓ.obj S → (Omega K₀ π).obj S := fun S _ _ _ _ _ y => θ S y.1
  have hnatℓ : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (φ : S →ₐ[C] S') (y : PRℓ.obj S),
      θℓ S' (PRℓ.map φ y) = (Omega K₀ π).map (φ.restrictScalars 𝒪) (θℓ S y) := by
    intro S S' _ _ _ _ _ _ _ _ _ _ φ y
    exact hnat S S' φ y.1

  have hptsℓ : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra C k] [Algebra 𝒪 k] [IsScalarTower 𝒪 C k],
      Function.Bijective (θℓ k) := by
    intro k _ _ _ _ _
    constructor
    · intro y y' h
      apply Subtype.ext
      exact (hpts k).1 y.1 y'.1 (pres_of_good k y.1 y.2) (pres_of_good k y'.1 y'.2) h
    · intro d
      obtain ⟨x, hx, hθx⟩ := (hpts k).2 d
      exact ⟨⟨x, good_of_pres k (hconn_local k) x hx⟩, hθx⟩
  have hetℓ : ∀ (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
      [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S₀] [Nontrivial S₀] [Algebra C S₀] [IsNoetherianRing S₀] [Algebra 𝒪 S₀] [IsScalarTower 𝒪 C S₀]
      (p : S →ₐ[C] S₀), Function.Surjective p → (∀ s t : S, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : PRℓ.obj S₀) (d : (Omega K₀ π).obj S),
        θℓ S₀ x₀ = (Omega K₀ π).map (p.restrictScalars 𝒪) d →
        ∃! x : PRℓ.obj S, PRℓ.map p x = x₀ ∧ θℓ S x = d := by
    intro S S₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp hsq x₀ d hθ₀
    haveI : IsLocalRing S₀ := IsLocalRing.of_surjective' (p : S →+* S₀) hp
    have hP₀ : Pres S₀ x₀.1 := pres_of_good S₀ x₀.1 x₀.2
    obtain ⟨x, ⟨hPx, hpx, hθx⟩, huniq⟩ := het S S₀ p hp hsq x₀.1 d hP₀ hθ₀
    refine ⟨⟨x, good_of_pres S (hconn_local S) x hPx⟩, ⟨Subtype.ext hpx, hθx⟩, ?_⟩
    rintro y ⟨hy1, hy2⟩
    apply Subtype.ext
    exact huniq y.1 ⟨pres_of_good S y.1 y.2, congrArg Subtype.val hy1, hy2⟩

  have hshℓ : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
          Ideal.span (Set.range f) = ⊤ →
          ∀ (Bc : Fin n → Type) [∀ i, CommRing (Bc i)] [∀ i, Algebra A (Bc i)] [∀ i, Algebra C (Bc i)]
            [∀ i, IsScalarTower C A (Bc i)] [∀ i, IsLocalization.Away (f i) (Bc i)] (s : ∀ i, PRℓ.obj (Bc i)),
          (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
              [IsLocalization.Away (f i * f j) D] (ρ₁ : Bc i →ₐ[A] D) (ρ₂ : Bc j →ₐ[A] D),
              PRℓ.map (ρ₁.restrictScalars C) (s i) = PRℓ.map (ρ₂.restrictScalars C) (s j)) →
          ∃! s₀ : PRℓ.obj A, ∀ i, PRℓ.map (IsScalarTower.toAlgHom C A (Bc i)) s₀ = s i := by
    intro A _ _ n f hf Bc _ _ _ _ _ s hcompat
    obtain ⟨s₀, hs₀, huniq⟩ := hsheaf A n f hf Bc (fun i => (s i).1)
      (fun i j D _ _ _ _ _ ρ₁ ρ₂ => congrArg Subtype.val (hcompat i j D ρ₁ ρ₂))
    have hgood : good A s₀ := by
      intro k _ _ _ hk φ

      have hex : ∃ i, (φ : A →+* k) (f i) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hle : Ideal.span (Set.range f) ≤ RingHom.ker (φ : A →+* k) :=
          Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (RingHom.mem_ker).mpr (hall i))
        rw [hf] at hle
        have h1 : (φ : A →+* k) 1 = 0 := (RingHom.mem_ker).mp (hle Submodule.mem_top)
        exact one_ne_zero ((map_one (φ : A →+* k)).symm.trans h1)
      obtain ⟨i, hi⟩ := hex
      have hu : IsUnit ((φ : A →+* k) (f i)) := isUnit_iff_ne_zero.mpr hi

      let ψr : Bc i →+* k := IsLocalization.Away.lift (f i) hu
      have hψr : ∀ a : A, ψr (algebraMap A (Bc i) a) = φ a := fun a => IsLocalization.Away.lift_eq (f i) hu a
      let ψ : Bc i →ₐ[C] k :=
        { toRingHom := ψr
          commutes' := fun c => by
            show ψr (algebraMap C (Bc i) c) = algebraMap C k c
            rw [IsScalarTower.algebraMap_apply C A (Bc i) c, hψr, AlgHom.commutes] }
      have hφ : φ = ψ.comp (IsScalarTower.toAlgHom C A (Bc i)) := by
        apply AlgHom.ext
        intro a
        exact (hψr a).symm
      rw [hφ, PR.map_comp, hs₀ i]
      exact (s i).2 k hk ψ
    refine ⟨⟨s₀, hgood⟩, fun i => Subtype.ext (hs₀ i), ?_⟩
    intro t ht
    apply Subtype.ext
    exact huniq t.1 (fun i => congrArg Subtype.val (ht i))

  have geomPt_at : ∀ (S : Type) [CommRing S] [Algebra C S] (q : ↥(Spec (CommRingCat.of S))),
      ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra C k) (φ : S →ₐ[C] k),
        ∀ pt : ↥(Spec (CommRingCat.of k)), (Spec.map (CommRingCat.ofHom (φ : S →+* k))).base pt = q := by
    intro S _ _ q
    let κ : Type := q.asIdeal.ResidueField
    let k : Type := AlgebraicClosure κ
    refine ⟨k, inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom C S k, ?_⟩
    intro pt
    have hψr : (algebraMap S k) = (algebraMap κ k).comp (algebraMap S κ) := IsScalarTower.algebraMap_eq S κ k
    have hpt : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime pt.asIdeal
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap S k) pt.asIdeal = q.asIdeal
    rw [hpt, ← RingHom.ker_eq_comap_bot, hψr, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap κ k).injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

  have hrepℓ : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) K₀,
        ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) (_ : LocallyOfFiniteType fX)
          (e : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
            (Scheme.nilpPoints fX).obj S → PRℓ.obj S),

          (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
              [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
              (y : (Scheme.nilpPoints fX).obj S)
              (y' : (Scheme.nilpPoints fX).obj S'),
              y'.1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ y.1 → e S' y' = PRℓ.map φ (e S y)) ∧

          (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
              (y y' : (Scheme.nilpPoints fX).obj S), e S y = e S y' → y = y') ∧

          (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (x : PRℓ.obj S),
              (∃ y : (Scheme.nilpPoints fX).obj S, e S y = x) ↔
                DeligneDatum.InEdgeChart π (θℓ S x) (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
                  (FullLattice.act γ (stdFullLattice K₀))) := by
    intro γ
    obtain ⟨X, fX, hlft, e, henat, heinj, heimg⟩ := hrep γ
    haveI := hlft

    let labX : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S],
        (∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) → (Scheme.nilpPoints fX).obj S → Bool :=
      fun S _ _ _ hc y =>
        letI : Algebra 𝒪 S := ((algebraMap C S).comp (algebraMap 𝒪 C)).toAlgebra
        letI : IsScalarTower 𝒪 C S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        decide (lab S hc (e S y) = ℓ)
    have hlabXnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [CommRing S'] [Algebra C S'] [IsNoetherianRing S']
        [Nontrivial S'] (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) (hS' : ∀ e : S', IsIdempotentElem e → e = 0 ∨ e = 1)
        (φ : S →ₐ[C] S') (y : (Scheme.nilpPoints fX).obj S),
        labX S' hS' ((Scheme.nilpPoints fX).map φ y) = labX S hS y := by
      intro S S' _ _ _ _ _ _ _ hS hS' φ y
      letI : Algebra 𝒪 S := ((algebraMap C S).comp (algebraMap 𝒪 C)).toAlgebra
      letI : IsScalarTower 𝒪 C S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      letI : Algebra 𝒪 S' := ((algebraMap C S').comp (algebraMap 𝒪 C)).toAlgebra
      letI : IsScalarTower 𝒪 C S' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      show decide (lab S' hS' (e S' ((Scheme.nilpPoints fX).map φ y)) = ℓ) = decide (lab S hS (e S y) = ℓ)
      rw [henat S S' φ y ((Scheme.nilpPoints fX).map φ y) (by rw [Scheme.nilpPoints_map_val, AlgHom.toRingHom_eq_coe]),
        hlabnat S S' hS hS' φ (e S y)]
    obtain ⟨U, hUdisj, hUcov, hUiff⟩ :=
      AlgebraicGeometry.Scheme.exists_opens_disjoint_forall_mem_iff_of_natural_nontrivial_of_connected X fX Bool labX hlabXnat

    let ι := Scheme.nilpPoints.mapHom ((U true).ι ≫ fX) fX (U true).ι rfl
    have hιmem : ∀ (S : Type) [CommRing S] [Algebra C S] (y' : (Scheme.nilpPoints ((U true).ι ≫ fX)).obj S)
        (p : ↥(Spec (CommRingCat.of S))), (ι.app S y').1.base p ∈ U true := by
      intro S _ _ y' p
      show ((y'.1 ≫ (U true).ι).base p) ∈ U true
      have hp : (y'.1 ≫ (U true).ι).base p = (U true).ι.base (y'.1.base p) := by simp
      rw [hp]
      exact (y'.1.base p).2
    have hιinj : ∀ (S : Type) [CommRing S] [Algebra C S] (y' y'' : (Scheme.nilpPoints ((U true).ι ≫ fX)).obj S),
        ι.app S y' = ι.app S y'' → y' = y'' := by
      intro S _ _ y' y'' h
      apply Subtype.ext
      have h1 : y'.1 ≫ (U true).ι = y''.1 ≫ (U true).ι := congrArg Subtype.val h
      exact (cancel_mono (U true).ι).mp h1
    have hιsurj : ∀ (S : Type) [CommRing S] [Algebra C S] (y : (Scheme.nilpPoints fX).obj S),
        (∀ p : ↥(Spec (CommRingCat.of S)), y.1.base p ∈ U true) → ∃ y' : (Scheme.nilpPoints ((U true).ι ≫ fX)).obj S, ι.app S y' = y := by
      intro S _ _ y hy
      have hrange : Set.range ⇑y.1 ⊆ Set.range ⇑(U true).ι := by
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hy p
      refine ⟨⟨IsOpenImmersion.lift (U true).ι y.1 hrange, ?_⟩, ?_⟩
      · show IsOpenImmersion.lift (U true).ι y.1 hrange ≫ ((U true).ι ≫ fX) = Scheme.specOver S
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact y.2
      · apply Subtype.ext
        show IsOpenImmersion.lift (U true).ι y.1 hrange ≫ (U true).ι = y.1
        exact IsOpenImmersion.lift_fac _ _ _

    have good_e : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (y' : (Scheme.nilpPoints ((U true).ι ≫ fX)).obj S), good S (e S (ι.app S y')) := by
      intro S _ _ _ _ _ y' k _ _ _ hk φ
      letI : Algebra 𝒪 k := ((algebraMap C k).comp (algebraMap 𝒪 C)).toAlgebra
      letI : IsScalarTower 𝒪 C k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      rw [← henat S k φ (ι.app S y') ((Scheme.nilpPoints fX).map φ (ι.app S y'))
        (by rw [Scheme.nilpPoints_map_val, AlgHom.toRingHom_eq_coe])]
      have hmem : ∀ p : ↥(Spec (CommRingCat.of k)), ((Scheme.nilpPoints fX).map φ (ι.app S y')).1.base p ∈ U true := by
        intro p
        show (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (y'.1 ≫ (U true).ι)).base p ∈ U true
        have hp : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (y'.1 ≫ (U true).ι)).base p =
            (U true).ι.base (y'.1.base ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base p)) := by simp
        rw [hp]
        exact (y'.1.base _).2
      have h := (hUiff k hk ((Scheme.nilpPoints fX).map φ (ι.app S y')) true).mpr hmem
      exact of_decide_eq_true h
    refine ⟨↑(U true), (U true).ι ≫ fX, inferInstance, fun S _ _ _ _ _ y' => ⟨e S (ι.app S y'), good_e S y'⟩, ?_, ?_, ?_⟩
    ·
      intro S S' _ _ _ _ _ _ _ _ _ _ φ y' y'' h
      apply Subtype.ext
      show e S' (ι.app S' y'') = PR.map φ (e S (ι.app S y'))
      refine henat S S' φ (ι.app S y') (ι.app S' y'') ?_
      show y''.1 ≫ (U true).ι = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (y'.1 ≫ (U true).ι)
      rw [h, Category.assoc]
    ·
      intro S _ _ _ _ _ y' y'' h
      exact hιinj S y' y'' (heinj S _ _ (congrArg Subtype.val h))
    ·
      intro S _ _ _ _ _ x
      constructor
      · rintro ⟨y', hy'⟩
        exact (heimg S x.1).mp ⟨ι.app S y', congrArg Subtype.val hy'⟩
      · intro hchart
        obtain ⟨y, hy⟩ := (heimg S x.1).mpr hchart
        have hmem : ∀ q : ↥(Spec (CommRingCat.of S)), y.1.base q ∈ U true := by
          intro q
          obtain ⟨k, _, _, _, φ, hφq⟩ := geomPt_at S q
          letI : Algebra 𝒪 k := ((algebraMap C k).comp (algebraMap 𝒪 C)).toAlgebra
          letI : IsScalarTower 𝒪 C k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
          have hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he
          have hlab : labX k hk ((Scheme.nilpPoints fX).map φ y) = true := by
            show decide (lab k hk (e k ((Scheme.nilpPoints fX).map φ y)) = ℓ) = true
            rw [henat S k φ y ((Scheme.nilpPoints fX).map φ y) (by rw [Scheme.nilpPoints_map_val, AlgHom.toRingHom_eq_coe]), hy]
            exact decide_eq_true (x.2 k hk φ)
          let pt : ↥(Spec (CommRingCat.of k)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
          have h2 := (hUiff k hk ((Scheme.nilpPoints fX).map φ y) true).mp hlab pt
          have h3 : ((Scheme.nilpPoints fX).map φ y).1.base pt = y.1.base q := by
            show (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ y.1).base pt = y.1.base q
            have : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ y.1).base pt = y.1.base ((Spec.map (CommRingCat.ofHom φ.toRingHom)).base pt) := by simp
            rw [this, AlgHom.toRingHom_eq_coe, hφq pt]
          rwa [h3] at h2
        obtain ⟨y', hy'⟩ := hιsurj S y hmem
        exact ⟨y', Subtype.ext ((congrArg (e S) hy').trans hy)⟩

  have hbij := CerednikDrinfeld.FormalOmega.Omega.bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart
    (K₀ := K₀) π hπ q hq C hC PRℓ hshℓ θℓ hnatℓ hetℓ hptsℓ g hg hrepℓ
  intro S _ _ _ _ _
  refine ⟨fun x x' hx hx' h => ?_, fun d => ?_⟩
  · exact congrArg Subtype.val ((hbij S).1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨x', hx'⟩) h)
  · obtain ⟨y, hy⟩ := (hbij S).2 d
    exact ⟨y.1, y.2, hy⟩

end S_CerednikDrinfeld_FormalOmega_Omega_injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_injective_surjective_labelPiece_of_algFunctor_of_forall_represents_inEdgeChart (solution)
