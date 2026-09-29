-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_isOpen_forall_mem_iff_exists_uniformization_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1961cc82-5ed5-5a8b-836d-d10ce1eeae35

import Theorems.Thm_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_isOpen_forall_mem_iff_exists_uniformization_of_isPullback
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace OpenUniformizedLocus

section Span

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem lineBaseChange_span_singleton (M : FullLattice 𝒪 K) (v : latticeBaseChange 𝒪 K B M) :
    lineBaseChange f M (Submodule.span B {v}) =
      Submodule.span B' {LinearMap.rTensor (↥M.1) f.toLinearMap v} := by
  apply le_antisymm
  · rw [lineBaseChange, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [rTensor_smul_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨v, Submodule.subset_span (Set.mem_singleton v), rfl⟩

theorem lineBaseChange_map_actBaseChange (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange f (FullLattice.act g M) (N.map (actBaseChange B g M).toLinearMap) =
      (lineBaseChange f M N).map (actBaseChange B' g M).toLinearMap := by
  rw [lineBaseChange, lineBaseChange, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact rTensor_actBaseChange f g M x

theorem rTensor_tmul_add_tmul (M : FullLattice 𝒪 K) (a b : B) (v w : ↥M.1) :
    LinearMap.rTensor (↥M.1) f.toLinearMap (a ⊗ₜ[𝒪] v + b ⊗ₜ[𝒪] w) = f a ⊗ₜ[𝒪] v + f b ⊗ₜ[𝒪] w := by
  rw [map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]

end Span

section EdgeLocus

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem inEdgeChart_map (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (h : d.InEdgeChart π M' M) :
    (d.map π f).InEdgeChart π M' M := by
  intro 𝔭' h𝔭'
  haveI := h𝔭'
  obtain ⟨hle, hπM, h1, h2⟩ := h (Ideal.comap f 𝔭') (Ideal.IsPrime.comap f)
  refine ⟨hle, hπM, fun v hv => ?_, fun v' hv' => ?_⟩
  · rw [← rTensor_one_tmul f M v]
    exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) 𝔭' _ (h1 v hv)
  · rw [← rTensor_one_tmul f M' v']
    exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') 𝔭' _ (h2 v' hv')

end EdgeLocus

section Coordinates

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

omit [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem isInteger_apply (v : ↥(stdFullLattice (𝒪 := 𝒪) K).1) (i : Fin 2) :
    IsLocalization.IsInteger 𝒪 ((v : Fin 2 → K) i) := v.2 i

variable (𝒪 K) in

noncomputable def coord (i : Fin 2) : ↥(stdFullLattice (𝒪 := 𝒪) K).1 →ₗ[𝒪] 𝒪 where
  toFun v := (isInteger_apply v i).choose
  map_add' v w := by
    apply IsFractionRing.injective 𝒪 K
    rw [(isInteger_apply (v + w) i).choose_spec, map_add, (isInteger_apply v i).choose_spec,
      (isInteger_apply w i).choose_spec]
    rfl
  map_smul' r v := by
    apply IsFractionRing.injective 𝒪 K
    rw [(isInteger_apply (r • v) i).choose_spec, RingHom.id_apply, smul_eq_mul, map_mul,
      (isInteger_apply v i).choose_spec]
    show ((r • (v : Fin 2 → K)) i) = _
    rw [Pi.smul_apply, Algebra.smul_def]

omit [IsDomain 𝒪] in
theorem coord_eq_iff (i : Fin 2) (v : ↥(stdFullLattice (𝒪 := 𝒪) K).1) (a : 𝒪) :
    coord 𝒪 K i v = a ↔ (v : Fin 2 → K) i = algebraMap 𝒪 K a := by
  constructor
  · rintro rfl; exact ((isInteger_apply v i).choose_spec).symm
  · intro h; exact IsFractionRing.injective 𝒪 K (((isInteger_apply v i).choose_spec).trans h)

theorem coord_stdBasisVec_self (i : Fin 2) : coord 𝒪 K i (stdBasisVec (𝒪 := 𝒪) K i) = 1 := by
  rw [coord_eq_iff, show ((stdBasisVec (𝒪 := 𝒪) K i : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) = Pi.single i 1 from rfl,
    Pi.single_eq_same, map_one]

theorem coord_stdBasisVec_of_ne {i j : Fin 2} (h : j ≠ i) : coord 𝒪 K i (stdBasisVec (𝒪 := 𝒪) K j) = 0 := by
  rw [coord_eq_iff, show ((stdBasisVec (𝒪 := 𝒪) K j : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) = Pi.single j 1 from rfl,
    Pi.single_eq_of_ne h.symm, map_zero]

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

variable (𝒪 K) in

noncomputable def κ (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice K) →ₗ[B] B :=
  (TensorProduct.AlgebraTensorModule.rid 𝒪 B B).toLinearMap ∘ₗ (coord 𝒪 K i).baseChange B

omit [IsDomain 𝒪] in
theorem κ_tmul (i : Fin 2) (b : B) (v : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    κ 𝒪 K B i (b ⊗ₜ[𝒪] v) = algebraMap 𝒪 B (coord 𝒪 K i v) * b := by
  simp only [κ, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]

theorem κ_zero_tmul_add_tmul (a b : B) :
    κ 𝒪 K B 0 (a ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1) = a := by
  rw [map_add, κ_tmul, κ_tmul, coord_stdBasisVec_self, coord_stdBasisVec_of_ne (by decide), map_one, one_mul, map_zero,
    zero_mul, add_zero]

theorem κ_one_tmul_add_tmul (a b : B) :
    κ 𝒪 K B 1 (a ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1) = b := by
  rw [map_add, κ_tmul, κ_tmul, coord_stdBasisVec_of_ne (by decide), coord_stdBasisVec_self, map_zero, zero_mul, map_one,
    one_mul, zero_add]

theorem eq_of_span_tmul_zero_eq {a a' : B}
    (h : Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} =
      Submodule.span B {a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1}) : a = a' := by
  have hmem : a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1 ∈
      Submodule.span B {a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} :=
    h ▸ Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrArg (κ 𝒪 K B 1) hμ
  rw [map_smul, κ_one_tmul_add_tmul, κ_one_tmul_add_tmul, smul_eq_mul, mul_one] at h1
  have h0 := congrArg (κ 𝒪 K B 0) hμ
  rw [map_smul, κ_zero_tmul_add_tmul, κ_zero_tmul_add_tmul, h1, one_smul] at h0
  exact h0.symm

theorem eq_of_span_tmul_one_eq {a a' : B}
    (h : Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + a ⊗ₜ[𝒪] stdBasisVec K 1} =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + a' ⊗ₜ[𝒪] stdBasisVec K 1}) : a = a' := by
  have hmem : (1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + a ⊗ₜ[𝒪] stdBasisVec K 1 ∈
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + a' ⊗ₜ[𝒪] stdBasisVec K 1} :=
    h ▸ Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 := congrArg (κ 𝒪 K B 0) hμ
  rw [map_smul, κ_zero_tmul_add_tmul, κ_zero_tmul_add_tmul, smul_eq_mul, mul_one] at h0
  have h1 := congrArg (κ 𝒪 K B 1) hμ
  rw [map_smul, κ_one_tmul_add_tmul, κ_one_tmul_add_tmul, h0, one_smul] at h1
  exact h1.symm

end Coordinates

section Ring

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (r : ℕ) (C : Type) [CommRing C] [Algebra 𝒪 C]

abbrev Rch : Type := chartERing C (algebraMap 𝒪 C π) r

variable {π r C}
variable {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra C D] [IsScalarTower 𝒪 C D]

noncomputable def toOChart (x : Rch π r C →ₐ[C] D) : chartERing 𝒪 π r →ₐ[𝒪] D :=
  chartERing.lift
    (⟨(x (chartERing.ξ C (algebraMap 𝒪 C π) r), x (chartERing.η C (algebraMap 𝒪 C π) r)), by
      rw [← map_mul, chartERing.ξ_mul_η, AlgHom.commutes, ← IsScalarTower.algebraMap_apply], by
      have hu := (chartERing.isUnit_discr C (algebraMap 𝒪 C π) r).map x
      rw [map_mul, map_sub, map_sub, map_pow, map_pow, map_one] at hu
      exact ⟨isUnit_of_mul_isUnit_left hu, isUnit_of_mul_isUnit_right hu⟩⟩ : (chartE 𝒪 π r).obj D)

@[scoped simp] theorem toOChart_ξ (x : Rch π r C →ₐ[C] D) : toOChart x (chartERing.ξ 𝒪 π r) = x (chartERing.ξ C (algebraMap 𝒪 C π) r) :=
  chartERing.lift_ξ _

@[scoped simp] theorem toOChart_η (x : Rch π r C →ₐ[C] D) : toOChart x (chartERing.η 𝒪 π r) = x (chartERing.η C (algebraMap 𝒪 C π) r) :=
  chartERing.lift_η _

noncomputable def ofOChart (c : chartERing 𝒪 π r →ₐ[𝒪] D) : Rch π r C →ₐ[C] D :=
  chartERing.lift
    (⟨(c (chartERing.ξ 𝒪 π r), c (chartERing.η 𝒪 π r)), by
      rw [← map_mul, chartERing.ξ_mul_η, AlgHom.commutes, ← IsScalarTower.algebraMap_apply], by
      have hu := (chartERing.isUnit_discr 𝒪 π r).map c
      rw [map_mul, map_sub, map_sub, map_pow, map_pow, map_one] at hu
      exact ⟨isUnit_of_mul_isUnit_left hu, isUnit_of_mul_isUnit_right hu⟩⟩ : (chartE C (algebraMap 𝒪 C π) r).obj D)

@[scoped simp] theorem ofOChart_ξ (c : chartERing 𝒪 π r →ₐ[𝒪] D) : ofOChart (C := C) c (chartERing.ξ C (algebraMap 𝒪 C π) r) = c (chartERing.ξ 𝒪 π r) :=
  chartERing.lift_ξ _

@[scoped simp] theorem ofOChart_η (c : chartERing 𝒪 π r →ₐ[𝒪] D) : ofOChart (C := C) c (chartERing.η C (algebraMap 𝒪 C π) r) = c (chartERing.η 𝒪 π r) :=
  chartERing.lift_η _

omit [Algebra 𝒪 D] [IsScalarTower 𝒪 C D] in

theorem chartPoint_ext {x x' : Rch π r C →ₐ[C] D}
    (hξ : x (chartERing.ξ C (algebraMap 𝒪 C π) r) = x' (chartERing.ξ C (algebraMap 𝒪 C π) r))
    (hη : x (chartERing.η C (algebraMap 𝒪 C π) r) = x' (chartERing.η C (algebraMap 𝒪 C π) r)) : x = x' :=
  (chartERing.corepEquiv C (algebraMap 𝒪 C π) r D).injective (Subtype.ext (Prod.ext hξ hη))

end Ring

section ChartData

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (r : ℕ) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) [Fact r.Prime]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
variable (C : Type) [CommRing C] [Algebra 𝒪 C]

def ChartEqs (D : Type) [CommRing D] [Algebra 𝒪 D] [Algebra C D] (x : Rch π r C →ₐ[C] D) (d : DeligneDatum (K := K₀) π D) : Prop :=
  d.line (stdFullLattice K₀) =
      Submodule.span D {(x (chartERing.ξ C (algebraMap 𝒪 C π) r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : D) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
    d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span D {(1 : D) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (x (chartERing.η C (algebraMap 𝒪 C π) r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
        (actBaseChange D g₁ (stdFullLattice K₀)).toLinearMap ∧
    d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)

variable {C}
variable {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra C D] [IsScalarTower 𝒪 C D]

include hπ hres hg₁ in

theorem exists_chartEqs (hD : IsNilpotent (algebraMap 𝒪 D π)) (x : Rch π r C →ₐ[C] D) :
    ∃ d : DeligneDatum (K := K₀) π D, ChartEqs π K₀ r g₁ C D x d := by
  obtain ⟨d, h₀, h₁, hE⟩ :=
    CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (K := K₀) π hπ r hres g₁ hg₁ D hD (toOChart x)
  exact ⟨d, by rw [h₀, toOChart_ξ], by rw [h₁, toOChart_η], hE⟩

include hπ hres hg₁ in

theorem exists_chartEqs_of_inEdgeChart (hD : IsNilpotent (algebraMap 𝒪 D π)) (Q : DeligneDatum (K := K₀) π D)
    (hQ : Q.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) :
    ∃ x : Rch π r C →ₐ[C] D, ChartEqs π K₀ r g₁ C D x Q := by
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  obtain ⟨c, h₀, h₁⟩ :=
    DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite (K := K₀) π hπ r hres g₁ hg₁ D hD Q hQ
  exact ⟨ofOChart c, by rw [h₀, ofOChart_ξ], by rw [h₁, ofOChart_η], hQ⟩

variable [Algebra 𝒪 (Rch π r C)] [IsScalarTower 𝒪 C (Rch π r C)]

theorem chartEqs_map (dR : DeligneDatum (K := K₀) π (Rch π r C)) (hdR : ChartEqs π K₀ r g₁ C (Rch π r C) (AlgHom.id C _) dR)
    (x : Rch π r C →ₐ[C] D) : ChartEqs π K₀ r g₁ C D x (dR.map π (x.restrictScalars 𝒪)) := by
  obtain ⟨hU₀, hU₁, hUE⟩ := hdR
  refine ⟨?_, ?_, inEdgeChart_map π _ dR _ _ hUE⟩
  · show lineBaseChange (x.restrictScalars 𝒪) _ (dR.line _) = _
    rw [hU₀, lineBaseChange_span_singleton, rTensor_tmul_add_tmul, map_one]
    rfl
  · show lineBaseChange (x.restrictScalars 𝒪) _ (dR.line _) = _
    rw [hU₁, lineBaseChange_map_actBaseChange, lineBaseChange_span_singleton, rTensor_tmul_add_tmul, map_one]
    rfl

include hπ in

theorem map_eq_of_chartEqs (dR : DeligneDatum (K := K₀) π (Rch π r C)) (hdR : ChartEqs π K₀ r g₁ C (Rch π r C) (AlgHom.id C _) dR)
    (x : Rch π r C →ₐ[C] D) (d : DeligneDatum (K := K₀) π D) (hd : ChartEqs π K₀ r g₁ C D x d) :
    dR.map π (x.restrictScalars 𝒪) = d := by
  obtain ⟨h₀, h₁, -⟩ := chartEqs_map π K₀ r g₁ dR hdR x
  obtain ⟨hd₀, hd₁, hdE⟩ := hd
  exact DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d _ (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) hdE
    (h₀.trans hd₀.symm) (h₁.trans hd₁.symm)

end ChartData

section Points

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
variable (r : ℕ) [Fact r.Prime] (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)
variable (G : Type) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
variable (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
  (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
variable (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
variable [Algebra 𝒪 (Rch π r C)] [IsScalarTower 𝒪 C (Rch π r C)] (hR : IsNilpotent (algebraMap 𝒪 (Rch π r C) π))
variable (dR : DeligneDatum (K := K₀) π (Rch π r C)) (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀)

noncomputable def XR : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj (Rch π r C) :=
  (((IsScalarTower.toAlgHom 𝒪 C (Rch π r C)).comp ψ, (Omega.action K₀ π).act (Rch π r C) h dR), g)

variable {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra C D] [IsScalarTower 𝒪 C D]

noncomputable def Xpt (x : Rch π r C →ₐ[C] D) :
    (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj D :=
  (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (x.restrictScalars 𝒪)
    (XR π K₀ Onr r G C ψ dR g h)

theorem Xpt_fst_fst (x : Rch π r C →ₐ[C] D) :
    (Xpt π K₀ Onr r G C ψ dR g h x).1.1 = (IsScalarTower.toAlgHom 𝒪 C D).comp ψ := by
  refine AlgHom.ext fun y => ?_
  show x (algebraMap C (Rch π r C) (ψ y)) = algebraMap C D (ψ y)
  exact x.commutes _

theorem Xpt_fst_snd (x : Rch π r C →ₐ[C] D) :
    (Xpt π K₀ Onr r G C ψ dR g h x).1.2 = (Omega.action K₀ π).act D h (dR.map π (x.restrictScalars 𝒪)) :=
  (Omega.action K₀ π).act_map (x.restrictScalars 𝒪) h dR

theorem Xpt_snd (x : Rch π r C →ₐ[C] D) : (Xpt π K₀ Onr r G C ψ dR g h x).2 = g := rfl

variable {N : Scheme.{0}} (p₁ : N ⟶ M) (p₂ : N ⟶ Spec (CommRingCat.of C))
variable (θ : Spec (CommRingCat.of (Rch π r C)) ⟶ N)
variable (hθ₁ : θ ≫ p₁ = (Θf (Rch π r C) hR (XR π K₀ Onr r G C ψ dR g h)).1)
variable (hnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
    Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))

include hθ₁ hnat in

theorem theta_Xpt (hD : IsNilpotent (algebraMap 𝒪 D π)) (x : Rch π r C →ₐ[C] D) :
    (Θf D hD (Xpt π K₀ Onr r G C ψ dR g h x)).1 = Spec.map (CommRingCat.ofHom x.toRingHom) ≫ θ ≫ p₁ := by
  rw [hθ₁, Xpt, hnat (Rch π r C) D hR hD (x.restrictScalars 𝒪)]
  rfl

end Points

section Open

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
variable (r : ℕ) [Fact r.Prime] (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
variable (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
variable (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
variable (G : Type) {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
variable (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
  (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
variable (hnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
    Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))
variable (het : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
    Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
    ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
      ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y)
variable (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)
variable {N : Scheme.{0}} (p₁ : N ⟶ M) (p₂ : N ⟶ Spec (CommRingCat.of C)) (hN : IsPullback p₁ p₂ fM (Scheme.specOver C))

variable [Algebra 𝒪 (Rch π r C)] [IsScalarTower 𝒪 C (Rch π r C)]

noncomputable def g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀ :=
  diagFst K₀ (Units.mk0 (algebraMap 𝒪 K₀ π) (by
    intro h0
    exact hπ.ne_zero ((IsFractionRing.injective 𝒪 K₀) (h0.trans (map_zero _).symm))))

theorem g₁_coe : ((g₁ π hπ K₀ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
    Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1] := rfl

theorem base_comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (f' : Y ⟶ Z) (x : ↥X) : (f ≫ f').base x = f'.base (f.base x) := rfl

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
include hC in
theorem isNilpotent_of_isScalarTower (D : Type) [CommRing D] [Algebra 𝒪 D] [Algebra C D] [IsScalarTower 𝒪 C D] :
    IsNilpotent (algebraMap 𝒪 D π) := by
  obtain ⟨n, hn⟩ := hC
  exact ⟨n, by rw [IsScalarTower.algebraMap_apply 𝒪 C D, ← map_pow, hn, map_zero]⟩

variable (dR : DeligneDatum (K := K₀) π (Rch π r C)) (hdR : ChartEqs π K₀ r (g₁ π hπ K₀) C (Rch π r C) (AlgHom.id C _) dR)
variable (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
variable (θ : Spec (CommRingCat.of (Rch π r C)) ⟶ N)
variable (hθ₁ : θ ≫ p₁ = (Θf (Rch π r C) (isNilpotent_of_isScalarTower π C hC (Rch π r C)) (XR π K₀ Onr r G C ψ dR g h)).1)
variable (hθ₂ : θ ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C))))

include hres hunr hOnr_max hOnr_alg hnat het hN hdR hθ₁ hθ₂ in

theorem isOpenMap_theta [LocallyOfFiniteType fM] : IsOpenMap θ.base := by
  obtain ⟨hd₀, hd₁, hdE⟩ := hdR
  haveI : Etale θ :=
    CerednikDrinfeld.QM.etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine 𝒪 inferInstance π hπ hres hunr K₀ Onr
      hOnr_max hOnr_alg G M fM Θf hnat het (g₁ π hπ K₀) (g₁_coe π hπ K₀) C hC ψ N p₁ p₂ hN
      (isNilpotent_of_isScalarTower π C hC (Rch π r C)) dR hd₀ hd₁ hdE g h θ hθ₁ hθ₂
  haveI : LocallyOfFinitePresentation θ := (Etale.iff_flat_and_formallyUnramified.mp inferInstance).2.2
  haveI : Flat θ := (Etale.iff_flat_and_formallyUnramified.mp inferInstance).1
  exact θ.isOpenMap

include hnat hθ₁ hθ₂ in

theorem uniformised_of_mem_range (n : ↥N) (hn : n ∈ Set.range θ.base) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra 𝒪 k) (hk : IsNilpotent (algebraMap 𝒪 k π)) (φ : C →ₐ[𝒪] k)
      (z : Spec (CommRingCat.of k) ⟶ N),
      z ≫ p₂ = Spec.map (CommRingCat.ofHom φ.toRingHom) ∧ z.base (IsLocalRing.closedPoint k) = n ∧
      ∃ (P : (Omega K₀ π).obj k) (g' : G), (Θf k hk ((φ.comp ψ, P), g')).1 = z ≫ p₁ := by
  obtain ⟨s, rfl⟩ := hn

  let X : Scheme.{0} := Spec (CommRingCat.of (Rch π r C))
  let k : Type := ↥(X.residueField s)
  let ι : Spec (CommRingCat.of k) ⟶ X := X.fromSpecResidueField s
  let xr : Rch π r C →+* k := (Spec.preimage ι).hom
  have hxr : Spec.map (CommRingCat.ofHom xr) = ι := by rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage ι
  let φr : C →+* k := xr.comp (algebraMap C (Rch π r C))
  letI : Algebra C k := φr.toAlgebra
  letI : Algebra 𝒪 k := (φr.comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hk : IsNilpotent (algebraMap 𝒪 k π) := isNilpotent_of_isScalarTower π C hC k
  let x : Rch π r C →ₐ[C] k := AlgHom.mk xr (fun _ => rfl)
  let φ : C →ₐ[𝒪] k := AlgHom.mk φr (fun _ => rfl)
  refine ⟨k, inferInstance, inferInstance, hk, φ, ι ≫ θ, ?_, ?_, (Xpt π K₀ Onr r G C ψ dR g h x).1.2, g, ?_⟩
  · rw [Category.assoc, hθ₂, ← hxr, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rw [base_comp_apply]
    exact congrArg θ.base (Scheme.fromSpecResidueField_apply s _)
  · have hX : ((φ.comp ψ, (Xpt π K₀ Onr r G C ψ dR g h x).1.2), g) = Xpt π K₀ Onr r G C ψ dR g h x := by
      refine Prod.ext (Prod.ext ?_ rfl) (Xpt_snd π K₀ Onr r G C ψ dR g h x).symm
      rw [Xpt_fst_fst]
      rfl
    have h1 := theta_Xpt π K₀ Onr r G fM Θf C ψ _ dR g h p₁ θ hθ₁ hnat hk x
    have h2 := congrArg (fun X => (Θf k hk X).1) hX
    refine (h2.trans h1).trans ?_
    rw [← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom xr) ≫ θ = ι ≫ θ
    rw [hxr]

include hπ hres hnat hN hdR hθ₁ hθ₂ in

theorem mem_range_of_uniformised (k : Type) [Field k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (φ : C →ₐ[𝒪] k)
    (z : Spec (CommRingCat.of k) ⟶ N) (hz₂ : z ≫ p₂ = Spec.map (CommRingCat.ofHom φ.toRingHom))
    (P : (Omega K₀ π).obj k) (hΘ : (Θf k hk ((φ.comp ψ, P), g)).1 = z ≫ p₁)
    (d' : DeligneDatum (K := K₀) π k) (hPd' : DeligneDatum.IsPullback (K := K₀) (π := π) k h P d')
    (hd'E : d'.InEdgeChart π (FullLattice.act (g₁ π hπ K₀) (stdFullLattice K₀)) (stdFullLattice K₀)) :
    z.base (IsLocalRing.closedPoint k) ∈ Set.range θ.base := by
  letI : Algebra C k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪 C k := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)

  have e : (Omega.action K₀ π).act k h⁻¹ P = d' := by
    apply DeligneDatum.ext'
    funext L
    rw [hPd' L]
    show (P.line (FullLattice.act h⁻¹⁻¹ L)).comap (actBaseChange k h⁻¹⁻¹ L).toLinearMap =
      (P.line (FullLattice.act h L)).comap (actBaseChange k h L).toLinearMap
    rw [inv_inv]
  have hP : (Omega.action K₀ π).act k h d' = P := by
    rw [← e, ← (Omega.action K₀ π).act_mul, mul_inv_cancel, (Omega.action K₀ π).act_one]

  obtain ⟨x, hx⟩ := exists_chartEqs_of_inEdgeChart (C := C) π hπ K₀ r hres (g₁ π hπ K₀) (g₁_coe π hπ K₀) hk d' hd'E
  have hxd : dR.map π (x.restrictScalars 𝒪) = d' := map_eq_of_chartEqs π hπ K₀ r (g₁ π hπ K₀) dR hdR x d' hx
  have hX : Xpt π K₀ Onr r G C ψ dR g h x = ((φ.comp ψ, P), g) := by
    refine Prod.ext (Prod.ext ?_ ?_) (Xpt_snd π K₀ Onr r G C ψ dR g h x)
    · rw [Xpt_fst_fst]
      refine AlgHom.ext fun y => ?_
      rfl
    · rw [Xpt_fst_snd, hxd, hP]

  have hz : z = Spec.map (CommRingCat.ofHom x.toRingHom) ≫ θ := by
    apply hN.hom_ext
    · rw [Category.assoc, ← theta_Xpt π K₀ Onr r G fM Θf C ψ _ dR g h p₁ θ hθ₁ hnat hk x, ← hΘ]
      exact congrArg (fun X => (Θf k hk X).1) hX.symm
    · rw [Category.assoc, hθ₂, hz₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun c => (x.commutes c).symm
  rw [hz, base_comp_apply]
  exact ⟨_, rfl⟩

include hπ hres hunr hOnr_max hOnr_alg hnat het hC hN in

theorem exists_isOpen [LocallyOfFiniteType fM] :
    ∃ W : Set ↥N, IsOpen W ∧
      ∀ n : ↥N, n ∈ W ↔
        ∃ (k : Type) (_ : Field k) (_ : Algebra 𝒪 k) (hk : IsNilpotent (algebraMap 𝒪 k π)) (φ : C →ₐ[𝒪] k)
          (z : Spec (CommRingCat.of k) ⟶ N),
          z ≫ p₂ = Spec.map (CommRingCat.ofHom φ.toRingHom) ∧ z.base (IsLocalRing.closedPoint k) = n ∧
          ∃ (P : (Omega K₀ π).obj k) (g : G), (Θf k hk ((φ.comp ψ, P), g)).1 = z ≫ p₁ := by
  have hR : IsNilpotent (algebraMap 𝒪 (Rch π r C) π) := isNilpotent_of_isScalarTower π C hC (Rch π r C)

  obtain ⟨dR, hdR⟩ := exists_chartEqs (D := Rch π r C) π hπ K₀ r hres (g₁ π hπ K₀) (g₁_coe π hπ K₀) hR (AlgHom.id C _)

  have hw : ∀ (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀),
      (Θf (Rch π r C) hR (XR π K₀ Onr r G C ψ dR g h)).1 ≫ fM =
        Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C))) ≫ Scheme.specOver C := by
    intro g h
    rw [(Θf (Rch π r C) hR (XR π K₀ Onr r G C ψ dR g h)).2, Scheme.specOver, Scheme.specOver, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq 𝒪 C (Rch π r C)]
  let θ : G → Matrix.GeneralLinearGroup (Fin 2) K₀ → (Spec (CommRingCat.of (Rch π r C)) ⟶ N) := fun g h =>
    hN.lift (Θf (Rch π r C) hR (XR π K₀ Onr r G C ψ dR g h)).1 (Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C)))) (hw g h)
  have hθ₁ : ∀ g h, θ g h ≫ p₁ = (Θf (Rch π r C) hR (XR π K₀ Onr r G C ψ dR g h)).1 := fun g h => hN.lift_fst _ _ _
  have hθ₂ : ∀ g h, θ g h ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C))) := fun g h => hN.lift_snd _ _ _
  refine ⟨⋃ (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀), Set.range (θ g h).base, ?_, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · refine isOpen_iUnion fun g => isOpen_iUnion fun h => ?_
    exact (isOpenMap_theta π hπ K₀ Onr r hres hunr hOnr_max hOnr_alg G fM Θf hnat het C hC ψ p₁ p₂ hN dR hdR g h (θ g h)
      (hθ₁ g h) (hθ₂ g h)).isOpen_range
  · obtain ⟨g, h, hn⟩ : ∃ g h, n ∈ Set.range (θ g h).base := by
      simpa only [Set.mem_iUnion] using hn
    exact uniformised_of_mem_range π K₀ Onr r G fM Θf hnat C hC ψ p₁ p₂ dR g h (θ g h) (hθ₁ g h) (hθ₂ g h) n hn
  · obtain ⟨k, _, _, hk, φ, z, hz₂, rfl, P, g, hΘ⟩ := hn
    obtain ⟨h, d', hPd', hd'E⟩ :=
      DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing (K := K₀) π hπ (g₁ π hπ K₀) (g₁_coe π hπ K₀) k hk P
    have hmem := mem_range_of_uniformised π hπ K₀ Onr r hres G fM Θf hnat C hC ψ p₁ p₂ hN dR hdR g h (θ g h) (hθ₁ g h) (hθ₂ g h)
      k hk φ z hz₂ P hΘ d' hPd' hd'E
    exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨h, hmem⟩⟩

end Open

end OpenUniformizedLocus
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_isOpen_forall_mem_iff_exists_uniformization_of_isPullback.OpenUniformizedLocus"

theorem solution
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})

    (G : Type)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType fM]
    (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
    (hnat :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))
    (het :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y)

    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)
    (N : Scheme.{0}) (p₁ : N ⟶ M) (p₂ : N ⟶ Spec (CommRingCat.of C)) (hN : IsPullback p₁ p₂ fM (Scheme.specOver C)) :
    ∃ W : Set ↥N, IsOpen W ∧
      ∀ n : ↥N, n ∈ W ↔
        ∃ (k : Type) (_ : Field k) (_ : Algebra 𝒪 k) (hk : IsNilpotent (algebraMap 𝒪 k π)) (φ : C →ₐ[𝒪] k)
          (z : Spec (CommRingCat.of k) ⟶ N),
          z ≫ p₂ = Spec.map (CommRingCat.ofHom φ.toRingHom) ∧ z.base (IsLocalRing.closedPoint k) = n ∧
          ∃ (P : (Omega K₀ π).obj k) (g : G), (Θf k hk ((φ.comp ψ, P), g)).1 = z ≫ p₁ := by
  haveI := hdvr
  letI : Algebra 𝒪 (chartERing C (algebraMap 𝒪 C π) r) :=
    ((algebraMap C (chartERing C (algebraMap 𝒪 C π) r)).comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C (chartERing C (algebraMap 𝒪 C π) r) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact OpenUniformizedLocus.exists_isOpen π hπ K₀ Onr r hres hunr hOnr_max hOnr_alg G fM Θf hnat het C hC ψ p₁ p₂ hN

end S_CerednikDrinfeld_QM_exists_isOpen_forall_mem_iff_exists_uniformization_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_isOpen_forall_mem_iff_exists_uniformization_of_isPullback (solution)
