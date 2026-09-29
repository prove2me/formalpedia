-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e842849a-01ca-5065-8be7-e7e07bc5dabd

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace OmegaRepresentP10

section Points

variable {𝒪 : Type} [CommRing 𝒪] {C : Type} [CommRing C] [Algebra 𝒪 C] {A : Type} [CommRing A] [Algebra 𝒪 A]

abbrev fY (C A : Type) [CommRing C] [Algebra 𝒪 C] [CommRing A] [Algebra 𝒪 A] :
    Spec (CommRingCat.of (C ⊗[𝒪] A)) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] A))

variable {S : Type} [CommRing S] [Algebra C S]

def ψOf (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) : C ⊗[𝒪] A →+* S :=
  (Spec.preimage y.1).hom

theorem spec_map_ψOf (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) :
    Spec.map (CommRingCat.ofHom (ψOf y)) = y.1 := by
  rw [ψOf, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem ψOf_eq_of_spec_map_eq (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) (f : C ⊗[𝒪] A →+* S)
    (h : Spec.map (CommRingCat.ofHom f) = y.1) : ψOf y = f := by
  rw [ψOf, ← h, Spec.preimage_map, CommRingCat.hom_ofHom]

theorem eq_of_ψOf_eq {y y' : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S} (h : ψOf y = ψOf y') : y = y' := by
  apply Subtype.ext
  rw [← spec_map_ψOf y, ← spec_map_ψOf y', h]

theorem ψOf_comp_includeLeftRingHom (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) :
    (ψOf y).comp Algebra.TensorProduct.includeLeftRingHom = algebraMap C S := by
  have h2 := y.2
  rw [← spec_map_ψOf y, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h2
  have h3 := Spec.map_injective h2
  rw [← CommRingCat.hom_ofHom ((ψOf y).comp Algebra.TensorProduct.includeLeftRingHom), h3, CommRingCat.hom_ofHom]

theorem ψOf_tmul_one (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) (c : C) :
    ψOf y (c ⊗ₜ[𝒪] (1 : A)) = algebraMap C S c := by
  rw [← ψOf_comp_includeLeftRingHom y]
  rfl

variable [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]

def xOf (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) : A →ₐ[𝒪] S where
  toRingHom := (ψOf y).comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := C) (B := A)).toRingHom
  commutes' r := by
    show ψOf y (Algebra.TensorProduct.includeRight (R := 𝒪) (A := C) (B := A) (algebraMap 𝒪 A r)) = algebraMap 𝒪 S r
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, ψOf_tmul_one, ← IsScalarTower.algebraMap_apply]

theorem xOf_apply (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) (a : A) :
    xOf y a = ψOf y ((1 : C) ⊗ₜ[𝒪] a) := rfl

theorem ψOf_tmul (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) (c : C) (a : A) :
    ψOf y (c ⊗ₜ[𝒪] a) = algebraMap C S c * xOf y a := by
  rw [xOf_apply, ← ψOf_tmul_one y c, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem eq_of_xOf_eq {y y' : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S} (h : xOf y = xOf y') : y = y' := by
  apply eq_of_ψOf_eq
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c a => rw [ψOf_tmul, ψOf_tmul, h]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

def liftHom (x : A →ₐ[𝒪] S) : C ⊗[𝒪] A →ₐ[C] S :=
  Algebra.TensorProduct.lift (Algebra.ofId C S) x (fun _ _ => Commute.all _ _)

theorem liftHom_tmul (x : A →ₐ[𝒪] S) (c : C) (a : A) : liftHom (C := C) x (c ⊗ₜ[𝒪] a) = algebraMap C S c * x a :=
  Algebra.TensorProduct.lift_tmul _ _ _ c a

def yOf (x : A →ₐ[𝒪] S) : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S :=
  ⟨Spec.map (CommRingCat.ofHom (liftHom (C := C) x).toRingHom), by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun c => ?_
    show liftHom (C := C) x (c ⊗ₜ[𝒪] (1 : A)) = algebraMap C S c
    rw [liftHom_tmul, map_one, mul_one]⟩

theorem xOf_yOf (x : A →ₐ[𝒪] S) : xOf (yOf (C := C) x) = x := by
  ext a
  rw [xOf_apply, ψOf_eq_of_spec_map_eq (yOf x) (liftHom (C := C) x).toRingHom rfl]
  show liftHom (C := C) x ((1 : C) ⊗ₜ[𝒪] a) = x a
  rw [liftHom_tmul, map_one, one_mul]

omit [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] in
theorem ψOf_map {S' : Type} [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S')
    (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) :
    ψOf ((Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).map φ y) = φ.toRingHom.comp (ψOf y) := by
  apply ψOf_eq_of_spec_map_eq
  rw [Scheme.nilpPoints_map_val, CommRingCat.ofHom_comp, Spec.map_comp, spec_map_ψOf]

theorem xOf_map {S' : Type} [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
    (y : (Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).obj S) :
    xOf ((Scheme.nilpPoints (fY (𝒪 := 𝒪) C A)).map φ y) = (φ.restrictScalars 𝒪).comp (xOf y) := by
  ext a
  rw [xOf_apply, ψOf_map]
  rfl

end Points

section Datum

abbrev Matches {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    (π : 𝒪) (q : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (S : Type) [CommRing S] [Algebra 𝒪 S] (d : DeligneDatum (K := K₀) π S) (x : chartERing 𝒪 π q →ₐ[𝒪] S) :
    Prop :=
  d.line (stdFullLattice K₀) =
      Submodule.span S {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : S) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
    d.line (FullLattice.act g (stdFullLattice K₀)) =
      (Submodule.span S {(1 : S) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
        (actBaseChange S g (stdFullLattice K₀)).toLinearMap

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
  [IsFractionRing 𝒪 K₀] {π : 𝒪} {q : ℕ} {g : Matrix.GeneralLinearGroup (Fin 2) K₀}
  (hπ : Irreducible π) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
  (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

include hπ hq hg

def d0 (S : Type) [CommRing S] [Algebra 𝒪 S] (hS : IsNilpotent (algebraMap 𝒪 S π)) (x : chartERing 𝒪 π q →ₐ[𝒪] S) :
    DeligneDatum (K := K₀) π S :=
  ((DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart π hπ q hq g hg S hS).2.1 x).exists.choose

theorem d0_spec (S : Type) [CommRing S] [Algebra 𝒪 S] (hS : IsNilpotent (algebraMap 𝒪 S π)) (x : chartERing 𝒪 π q →ₐ[𝒪] S) :
    Matches π q g S (d0 hπ hq hg S hS x) x ∧
      (d0 hπ hq hg S hS x).InEdgeChart π (FullLattice.act g (stdFullLattice K₀)) (stdFullLattice K₀) :=
  ((DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart π hπ q hq g hg S hS).2.1 x).exists.choose_spec

theorem eq_d0 (S : Type) [CommRing S] [Algebra 𝒪 S] (hS : IsNilpotent (algebraMap 𝒪 S π)) (x : chartERing 𝒪 π q →ₐ[𝒪] S)
    (d : DeligneDatum (K := K₀) π S) (hd : Matches π q g S d x)
    (hd' : d.InEdgeChart π (FullLattice.act g (stdFullLattice K₀)) (stdFullLattice K₀)) : d = d0 hπ hq hg S hS x :=
  ((DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart π hπ q hq g hg S hS).2.1 x).unique
    ⟨hd, hd'⟩ (d0_spec hπ hq hg S hS x)

theorem x_unique (S : Type) [CommRing S] [Algebra 𝒪 S] (hS : IsNilpotent (algebraMap 𝒪 S π))
    (d : DeligneDatum (K := K₀) π S) (hd : d.InEdgeChart π (FullLattice.act g (stdFullLattice K₀)) (stdFullLattice K₀))
    (x x' : chartERing 𝒪 π q →ₐ[𝒪] S) (hx : Matches π q g S d x) (hx' : Matches π q g S d x') : x = x' :=
  ((DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart π hπ q hq g hg S hS).1 d hd).unique hx hx'

theorem matches_map (S : Type) [CommRing S] [Algebra 𝒪 S] (hS : IsNilpotent (algebraMap 𝒪 S π))
    (S' : Type) [CommRing S'] [Algebra 𝒪 S'] (φ : S →ₐ[𝒪] S')
    (d : DeligneDatum (K := K₀) π S) (x : chartERing 𝒪 π q →ₐ[𝒪] S) (hx : Matches π q g S d x) :
    Matches π q g S' ((Omega K₀ π).map φ d) (φ.comp x) :=
  (DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart π hπ q hq g hg S hS).2.2 S' φ d x hx

theorem map_d0 (S : Type) [CommRing S] [Algebra 𝒪 S] (hS : IsNilpotent (algebraMap 𝒪 S π))
    (S' : Type) [CommRing S'] [Algebra 𝒪 S'] (hS' : IsNilpotent (algebraMap 𝒪 S' π)) (φ : S →ₐ[𝒪] S')
    (x : chartERing 𝒪 π q →ₐ[𝒪] S) :
    (Omega K₀ π).map φ (d0 hπ hq hg S hS x) = d0 hπ hq hg S' hS' (φ.comp x) := by
  have h1 := matches_map hπ hq hg S hS S' φ _ x (d0_spec hπ hq hg S hS x).1
  have h2 := d0_spec hπ hq hg S' hS' (φ.comp x)
  exact DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ _ _ _ _ h2.2 (h1.1.trans h2.1.1.symm) (h1.2.trans h2.1.2.symm)

end Datum

section Action

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
  (S : Type) [CommRing S] [Algebra 𝒪 S]

theorem act_inv_act (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : (Omega K₀ π).obj S) :
    (Omega.action K₀ π).act S h⁻¹ ((Omega.action K₀ π).act S h d) = d := by
  rw [← (Omega.action K₀ π).act_mul, inv_mul_cancel, (Omega.action K₀ π).act_one]

theorem act_act_inv' (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : (Omega K₀ π).obj S) :
    (Omega.action K₀ π).act S h ((Omega.action K₀ π).act S h⁻¹ d) = d := by
  rw [← (Omega.action K₀ π).act_mul, mul_inv_cancel, (Omega.action K₀ π).act_one]

theorem pullback_eq_act_inv (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : (Omega K₀ π).obj S) :
    DeligneDatum.pullback π S h d = (Omega.action K₀ π).act S h⁻¹ d := by
  show DeligneDatum.pullback π S h d = DeligneDatum.pullback π S h⁻¹⁻¹ d
  rw [inv_inv]

theorem isPullback_act (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : (Omega K₀ π).obj S) :
    DeligneDatum.IsPullback (K := K₀) (π := π) S h ((Omega.action K₀ π).act S h d) d := by
  have := DeligneDatum.isPullback_pullback π S h ((Omega.action K₀ π).act S h d)
  rwa [pullback_eq_act_inv, act_inv_act] at this

theorem fullLattice_act_inv_act (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : FullLattice 𝒪 K₀) :
    FullLattice.act h⁻¹ (FullLattice.act h N) = N := by
  apply Subtype.ext
  have := act_act_inv h⁻¹ N
  rwa [inv_inv] at this

end Action

end OmegaRepresentP10

open OmegaRepresentP10

theorem solution

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))

    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (γ : Matrix.GeneralLinearGroup (Fin 2) K₀) :
    ∃ ι : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
        (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S → (Omega K₀ π).obj S,

      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          (φ : S →ₐ[C] S') (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S),
          ι S' ((Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).map φ y) =
            (Omega K₀ π).map (φ.restrictScalars 𝒪) (ι S y)) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S], Function.Injective (ι S)) ∧

      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S] (d : (Omega K₀ π).obj S),
          DeligneDatum.InEdgeChart π d (FullLattice.act γ (FullLattice.act g (stdFullLattice K₀)))
            (FullLattice.act γ (stdFullLattice K₀)) ↔ ∃ y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[𝒪] chartERing 𝒪 π q)))).obj S, ι S y = d) := by
  classical
  have hnil : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      IsNilpotent (algebraMap 𝒪 S π) := by
    intro S _ _ _ _
    rw [IsScalarTower.algebraMap_apply 𝒪 C S π]
    exact hC.map (algebraMap C S)

  refine ⟨fun S _ _ _ _ y => (Omega.action K₀ π).act S γ (d0 hπ hq hg S (hnil S) (xOf y)), ?_, ?_, ?_⟩
  ·
    intro S S' _ _ _ _ _ _ _ _ φ y
    show (Omega.action K₀ π).act S' γ (d0 hπ hq hg S' (hnil S') (xOf ((Scheme.nilpPoints (fY C _)).map φ y))) =
      (Omega K₀ π).map (φ.restrictScalars 𝒪) ((Omega.action K₀ π).act S γ (d0 hπ hq hg S (hnil S) (xOf y)))
    rw [(Omega.action K₀ π).act_map, map_d0 hπ hq hg S (hnil S) S' (hnil S'), xOf_map]
  ·
    intro S _ _ _ _ y y' hyy
    have h1 : d0 hπ hq hg S (hnil S) (xOf y) = d0 hπ hq hg S (hnil S) (xOf y') := by
      have := congrArg ((Omega.action K₀ π).act S γ⁻¹) hyy
      rwa [act_inv_act, act_inv_act] at this
    apply eq_of_xOf_eq
    have s := d0_spec hπ hq hg S (hnil S) (xOf y)
    have s' := d0_spec hπ hq hg S (hnil S) (xOf y')
    rw [← h1] at s'
    exact x_unique hπ hq hg S (hnil S) _ s.2 _ _ s.1 s'.1
  ·
    intro S _ _ _ _ d
    constructor
    · intro hd

      set d' := (Omega.action K₀ π).act S γ⁻¹ d with hd'def
      have hP : DeligneDatum.IsPullback (K := K₀) (π := π) S γ⁻¹ d' d := by
        rw [hd'def]; exact isPullback_act π S γ⁻¹ d
      have hd'' := DeligneDatum.inEdgeChart_act_of_isPullback γ⁻¹ hP hd
      rw [fullLattice_act_inv_act, fullLattice_act_inv_act] at hd''
      obtain ⟨x, hx, -⟩ :=
        (DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart π hπ q hq g hg S (hnil S)).1 d' hd''
      refine ⟨yOf x, ?_⟩
      show (Omega.action K₀ π).act S γ (d0 hπ hq hg S (hnil S) (xOf (yOf x))) = d
      rw [xOf_yOf, ← eq_d0 hπ hq hg S (hnil S) x d' hx hd'', hd'def, act_act_inv']
    · rintro ⟨y, rfl⟩
      exact DeligneDatum.inEdgeChart_act_of_isPullback γ (isPullback_act π S γ _) (d0_spec hπ hq hg S (hnil S) (xOf y)).2

end
end S_CerednikDrinfeld_FormalOmega_Omega_exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing (solution)
