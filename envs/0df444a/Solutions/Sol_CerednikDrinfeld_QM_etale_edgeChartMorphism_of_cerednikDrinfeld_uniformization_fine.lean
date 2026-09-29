-- Prove2me | solution 1 for CerednikDrinfeld.QM.etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1d52b92e-9bab-501f-8af2-9828d153c16e

import Theorems.Thm_CerednikDrinfeld_Onr_algHom_eq_of_comp_eq_of_sq_zero
import Theorems.Thm_AlgebraicGeometry_Etale_of_forall_existsUnique_lift
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace EtaleEdgeChart

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

theorem rTensor_mem_lineBaseChange_sup (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M)) (𝔭 : Ideal B)
    (x : latticeBaseChange 𝒪 K B M) (hx : x ∈ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    LinearMap.rTensor (↥M.1) f.toLinearMap x ∈
      lineBaseChange f M N ⊔ ((𝔭.map f) • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  refine Submodule.mem_sup.mpr ⟨_, Submodule.subset_span ⟨y, hy, rfl⟩, _, ?_, rfl⟩
  refine Submodule.smul_induction_on
    (p := fun z => LinearMap.rTensor (↥M.1) f.toLinearMap z ∈ ((𝔭.map f) • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M))) hz
    (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · show LinearMap.rTensor (↥M.1) f.toLinearMap (r • n) ∈ _
    rw [rTensor_smul_left]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · show LinearMap.rTensor (↥M.1) f.toLinearMap (x + y) ∈ _
    rw [map_add]; exact Submodule.add_mem _ hx hy

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

theorem inEdgeChart_of_map_of_surjective (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (hf : Function.Surjective f) (hnil : ∀ s : B, f s = 0 → IsNilpotent s)
    (h : (d.map π f).InEdgeChart π M' M) : d.InEdgeChart π M' M := by
  intro 𝔭 h𝔭
  haveI := h𝔭
  have hker : RingHom.ker (f : B →+* B') ≤ 𝔭 := by
    intro s hs
    obtain ⟨n, hn⟩ := hnil s hs
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n (by rw [hn]; exact 𝔭.zero_mem)
  haveI : (𝔭.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  obtain ⟨hle, hπM, h1, h2⟩ := h (𝔭.map f) inferInstance
  refine ⟨hle, hπM, fun v hv hmem => h1 v hv ?_, fun v' hv' hmem => h2 v' hv' ?_⟩
  · rw [← rTensor_one_tmul f M v]
    exact rTensor_mem_lineBaseChange_sup f M (d.line M) 𝔭 _ hmem
  · rw [← rTensor_one_tmul f M' v']
    exact rTensor_mem_lineBaseChange_sup f M' (d.line M') 𝔭 _ hmem

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

theorem finitePresentation_Rch : Algebra.FinitePresentation C (Rch π r C) := by
  haveI : Algebra.FinitePresentation C (edgeQuot C (algebraMap 𝒪 C π)) := by
    change Algebra.FinitePresentation C (MvPolynomial (Fin 2) C ⧸ Ideal.span {edgeRel C (algebraMap 𝒪 C π)})
    exact Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  exact Algebra.FinitePresentation.trans C (edgeQuot C (algebraMap 𝒪 C π)) (Rch π r C)

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

include hπ in

theorem chartEqs_unique {x x' : Rch π r C →ₐ[C] D} {d : DeligneDatum (K := K₀) π D}
    (h : ChartEqs π K₀ r g₁ C D x d) (h' : ChartEqs π K₀ r g₁ C D x' d) : x = x' := by
  obtain ⟨h₀, h₁, -⟩ := h
  obtain ⟨h₀', h₁', -⟩ := h'
  refine chartPoint_ext (eq_of_span_tmul_zero_eq (𝒪 := 𝒪) (K := K₀) D (h₀.symm.trans h₀'))
    (eq_of_span_tmul_one_eq (𝒪 := 𝒪) (K := K₀) D ?_)
  have := h₁.symm.trans h₁'
  exact Submodule.map_injective_of_injective (actBaseChange D g₁ (stdFullLattice K₀)).injective this

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

theorem Xpt_comp {D' : Type} [CommRing D'] [Algebra 𝒪 D'] [Algebra C D'] [IsScalarTower 𝒪 C D']
    (x : Rch π r C →ₐ[C] D) (p : D →ₐ[C] D') :
    Xpt π K₀ Onr r G C ψ dR g h (p.comp x) =
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (p.restrictScalars 𝒪)
        (Xpt π K₀ Onr r G C ψ dR g h x) := by
  rw [Xpt, Xpt, ← AlgFunctor.map_comp]
  rfl

variable (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
variable (hdR : ChartEqs π K₀ r g₁ C (Rch π r C) (AlgHom.id C _) dR)

include hπ hdR in

theorem Xpt_injective {x x' : Rch π r C →ₐ[C] D}
    (hxx : Xpt π K₀ Onr r G C ψ dR g h x = Xpt π K₀ Onr r G C ψ dR g h x') : x = x' := by
  have h2 := congrArg (fun X => (Omega.action K₀ π).act D h⁻¹ X.1.2) hxx
  simp only [Xpt_fst_snd, ← (Omega.action K₀ π).act_mul, inv_mul_cancel, (Omega.action K₀ π).act_one] at h2
  exact chartEqs_unique π hπ K₀ r g₁ (chartEqs_map π K₀ r g₁ dR hdR x) (h2 ▸ chartEqs_map π K₀ r g₁ dR hdR x')

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

section Core

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
variable (r : ℕ) [Fact r.Prime] (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
variable (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
variable (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
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
variable [Algebra 𝒪 (Rch π r C)] [IsScalarTower 𝒪 C (Rch π r C)] (hR : IsNilpotent (algebraMap 𝒪 (Rch π r C) π))
variable (dR : DeligneDatum (K := K₀) π (Rch π r C)) (hdR : ChartEqs π K₀ r g₁ C (Rch π r C) (AlgHom.id C _) dR)
variable (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
variable (θ : Spec (CommRingCat.of (Rch π r C)) ⟶ N)
variable (hθ₁ : θ ≫ p₁ = (Θf (Rch π r C) hR (XR π K₀ Onr r G C ψ dR g h)).1)
variable (hθ₂ : θ ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C))))

omit [IsDomain 𝒪] in
include hC in
theorem isNilpotent_of_isScalarTower (D : Type) [CommRing D] [Algebra 𝒪 D] [Algebra C D] [IsScalarTower 𝒪 C D] :
    IsNilpotent (algebraMap 𝒪 D π) := by
  obtain ⟨n, hn⟩ := hC
  exact ⟨n, by rw [IsScalarTower.algebraMap_apply 𝒪 C D, ← map_pow, hn, map_zero]⟩

include hπ hres hunr hOnr_max hOnr_alg hg₁ hnat het hC hN hdR hθ₁ hθ₂ in

theorem existsUnique_lift (D D₀ : Type) [CommRing D] [CommRing D₀] [Algebra 𝒪 D] [Algebra C D] [IsScalarTower 𝒪 C D]
    [Algebra 𝒪 D₀] [Algebra C D₀] [IsScalarTower 𝒪 C D₀]
    (p : D →ₐ[C] D₀) (hp : Function.Surjective p) (hsq : ∀ s t : D, p s = 0 → p t = 0 → s * t = 0)
    (x₀ : Rch π r C →ₐ[C] D₀) (z : Spec (CommRingCat.of D) ⟶ N) (hz : z ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C D)))
    (hcomm : Spec.map (CommRingCat.ofHom p.toRingHom) ≫ z = Spec.map (CommRingCat.ofHom x₀.toRingHom) ≫ θ) :
    ∃! x : Rch π r C →ₐ[C] D, p.comp x = x₀ ∧ Spec.map (CommRingCat.ofHom x.toRingHom) ≫ θ = z := by
  have hD : IsNilpotent (algebraMap 𝒪 D π) := isNilpotent_of_isScalarTower π C hC D
  have hD₀ : IsNilpotent (algebraMap 𝒪 D₀ π) := isNilpotent_of_isScalarTower π C hC D₀

  have hyD : (z ≫ p₁) ≫ fM = Scheme.specOver D := by
    rw [Category.assoc, hN.w, ← Category.assoc, hz, Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  let yD : (Scheme.nilpPoints fM).obj D := ⟨z ≫ p₁, hyD⟩

  have hy : (Scheme.nilpPoints fM).map (p.restrictScalars 𝒪) yD = Θf D₀ hD₀ (Xpt π K₀ Onr r G C ψ dR g h x₀) := by
    apply Subtype.ext
    rw [Scheme.nilpPoints_map_val, theta_Xpt π K₀ Onr r G fM Θf C ψ hR dR g h p₁ θ hθ₁ hnat hD₀ x₀]
    show Spec.map (CommRingCat.ofHom p.toRingHom) ≫ z ≫ p₁ = _
    rw [← Category.assoc, hcomm, Category.assoc]
  obtain ⟨X', ⟨hX'₁, hX'₂⟩, huniq⟩ := het D D₀ (p.restrictScalars 𝒪) hD hD₀ hp hsq (Xpt π K₀ Onr r G C ψ dR g h x₀) yD hy

  have hgood : ∀ x : Rch π r C →ₐ[C] D,
      Xpt π K₀ Onr r G C ψ dR g h x = X' ↔ (p.comp x = x₀ ∧ Spec.map (CommRingCat.ofHom x.toRingHom) ≫ θ = z) := by
    intro x
    constructor
    · intro hx
      constructor
      · apply Xpt_injective π hπ K₀ Onr r g₁ G C ψ dR g h hdR
        rw [Xpt_comp, hx, hX'₁]
      · apply hN.hom_ext
        · rw [Category.assoc, ← theta_Xpt π K₀ Onr r G fM Θf C ψ hR dR g h p₁ θ hθ₁ hnat hD x, hx, hX'₂]
        · rw [Category.assoc, hθ₂, hz, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          exact RingHom.ext fun c => x.commutes c
    · rintro ⟨hx₁, hx₂⟩
      apply huniq
      constructor
      · rw [← Xpt_comp, hx₁]
      · apply Subtype.ext
        rw [theta_Xpt π K₀ Onr r G fM Θf C ψ hR dR g h p₁ θ hθ₁ hnat hD x]
        show _ = z ≫ p₁
        rw [← Category.assoc, hx₂]

  obtain ⟨⟨ψ', P'⟩, g'⟩ := X'
  have e₁ : (p.restrictScalars 𝒪).comp ψ' = (Xpt π K₀ Onr r G C ψ dR g h x₀).1.1 := congrArg (fun X => X.1.1) hX'₁
  have e₂ : (Omega K₀ π).map (p.restrictScalars 𝒪) P' = (Xpt π K₀ Onr r G C ψ dR g h x₀).1.2 := congrArg (fun X => X.1.2) hX'₁
  have e₃ : g' = g := congrArg (fun X => X.2) hX'₁

  have hunr' : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
  have hψ' : ψ' = (IsScalarTower.toAlgHom 𝒪 C D).comp ψ := by
    apply CerednikDrinfeld.Onr.algHom_eq_of_comp_eq_of_sq_zero 𝒪 π hres hunr' Onr hOnr_max.isPrime hOnr_alg D D₀ hD
      (p.restrictScalars 𝒪) hsq
    rw [e₁, Xpt_fst_fst]
    refine AlgHom.ext fun y => ?_
    show algebraMap C D₀ (ψ y) = p (algebraMap C D (ψ y))
    rw [p.commutes]

  have hQmap : (Omega K₀ π).map (p.restrictScalars 𝒪) ((Omega.action K₀ π).act D h⁻¹ P') = dR.map π (x₀.restrictScalars 𝒪) := by
    rw [(Omega.action K₀ π).act_map, e₂, Xpt_fst_snd, ← (Omega.action K₀ π).act_mul, inv_mul_cancel, (Omega.action K₀ π).act_one]
  have hQE : ((Omega.action K₀ π).act D h⁻¹ P').InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) := by
    apply inEdgeChart_of_map_of_surjective π (p.restrictScalars 𝒪) _ _ _ hp (fun s hs => ⟨2, by rw [pow_two]; exact hsq s s hs hs⟩)
    change ((Omega K₀ π).map (p.restrictScalars 𝒪) ((Omega.action K₀ π).act D h⁻¹ P')).InEdgeChart π _ _
    rw [hQmap]
    exact (chartEqs_map π K₀ r g₁ dR hdR x₀).2.2
  obtain ⟨x, hx⟩ := exists_chartEqs_of_inEdgeChart (C := C) π hπ K₀ r hres g₁ hg₁ hD _ hQE
  have hxQ : dR.map π (x.restrictScalars 𝒪) = (Omega.action K₀ π).act D h⁻¹ P' := map_eq_of_chartEqs π hπ K₀ r g₁ dR hdR x _ hx
  have hXx : Xpt π K₀ Onr r G C ψ dR g h x = ((ψ', P'), g') := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · rw [Xpt_fst_fst, hψ']
    · rw [Xpt_fst_snd, hxQ, ← (Omega.action K₀ π).act_mul, mul_inv_cancel, (Omega.action K₀ π).act_one]
    · rw [Xpt_snd, e₃]
  refine ⟨x, (hgood x).mp hXx, fun x' hx' => ?_⟩
  exact Xpt_injective π hπ K₀ Onr r g₁ G C ψ dR g h hdR (((hgood x').mpr hx').trans hXx.symm)

include hθ₂ in

theorem locallyOfFinitePresentation_theta [LocallyOfFiniteType p₂] : LocallyOfFinitePresentation θ := by
  classical
  haveI := finitePresentation_Rch π r C
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.FinitePresentation := by
    intro A S T _ _ _ _ s _ f hf
    exact hf.comp (RingHom.finitePresentation_holdsForLocalizationAway S s)
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation) hQ]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp N.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (θ x))
  obtain ⟨V, ⟨s, rfl⟩, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (AlgebraicGeometry.isBasis_basicOpen (Spec (.of (Rch π r C)))) (show x ∈ θ ⁻¹ᵁ U from hxU)
  have hV : IsAffineOpen ((Spec (.of (Rch π r C))).basicOpen s) := (isAffineOpen_top (Spec (.of (Rch π r C)))).basicOpen s
  refine ⟨⟨U, hU⟩, ⟨(Spec (.of (Rch π r C))).basicOpen s, hV⟩, hxV, hVU, ?_⟩
  set φ : Γ(N, U) ⟶ Γ(Spec (.of (Rch π r C)), (Spec (.of (Rch π r C))).basicOpen s) :=
    θ.appLE U ((Spec (.of (Rch π r C))).basicOpen s) hVU with hφdef
  let ιC : C →+* Γ(N, U) := (p₂.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of C)).inv.hom
  let ρ : Rch π r C →+* Γ(Spec (.of (Rch π r C)), (Spec (.of (Rch π r C))).basicOpen s) :=
    ((Spec (.of (Rch π r C))).presheaf.map (homOfLE le_top).op).hom.comp (Scheme.ΓSpecIso (.of (Rch π r C))).inv.hom

  have htri : φ.hom.comp ιC = ρ.comp (algebraMap C (Rch π r C)) := by
    have h1 : p₂.appLE ⊤ U le_top ≫ φ = (θ ≫ p₂).appLE ⊤ ((Spec (.of (Rch π r C))).basicOpen s) le_top := by
      rw [hφdef, Scheme.Hom.appLE_comp_appLE]
    have h2gen : ∀ (q : Spec (.of (Rch π r C)) ⟶ Spec (.of C)), q = Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C))) →
        ∀ e, q.appLE ⊤ ((Spec (.of (Rch π r C))).basicOpen s) e =
          (Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C)))).appTop ≫ (Spec (.of (Rch π r C))).presheaf.map (homOfLE le_top).op := by
      rintro q rfl e; rfl
    have h2 := h2gen _ hθ₂ le_top
    have h3 : (Scheme.ΓSpecIso (.of C)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap C (Rch π r C)))).appTop =
        CommRingCat.ofHom (algebraMap C (Rch π r C)) ≫ (Scheme.ΓSpecIso (.of (Rch π r C))).inv :=
      (Scheme.ΓSpecIso_inv_naturality _).symm
    have h4 : (Scheme.ΓSpecIso (.of C)).inv ≫ p₂.appLE ⊤ U le_top ≫ φ =
        CommRingCat.ofHom (algebraMap C (Rch π r C)) ≫ (Scheme.ΓSpecIso (.of (Rch π r C))).inv ≫
          (Spec (.of (Rch π r C))).presheaf.map (homOfLE le_top).op := by
      rw [h1, h2, ← Category.assoc, h3, Category.assoc]
    have h5 := congrArg (fun f : CommRingCat.of C ⟶ Γ(Spec (.of (Rch π r C)), (Spec (.of (Rch π r C))).basicOpen s) => f.hom) h4
    simp only [CommRingCat.hom_comp] at h5
    change (φ.hom.comp (p₂.appLE ⊤ U le_top).hom).comp (Scheme.ΓSpecIso (.of C)).inv.hom =
      ((((Spec (.of (Rch π r C))).presheaf.map (homOfLE le_top).op).hom.comp (Scheme.ΓSpecIso (.of (Rch π r C))).inv.hom).comp
        (algebraMap C (Rch π r C)))
    rw [RingHom.comp_assoc]
    exact h5
  change φ.hom.FinitePresentation
  apply RingHom.FinitePresentation.of_comp_finiteType ιC
  · rw [htri]
    apply RingHom.FinitePresentation.comp
    · apply RingHom.FinitePresentation.comp
      · exact RingHom.finitePresentation_holdsForLocalizationAway.{0} _ s
      · exact RingHom.FinitePresentation.of_bijective (Scheme.ΓSpecIso (.of (Rch π r C))).symm.commRingCatIsoToRingEquiv.bijective
    · exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · apply RingHom.FiniteType.comp
    · exact HasRingHomProperty.appLE @LocallyOfFiniteType p₂ inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    · exact RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (.of C)).symm.commRingCatIsoToRingEquiv.surjective

include hπ hres hunr hOnr_max hOnr_alg hg₁ hnat het hC hN hdR hθ₁ hθ₂ in

theorem etale_theta [LocallyOfFiniteType fM] : Etale θ := by
  haveI : LocallyOfFiniteType p₂ := MorphismProperty.of_isPullback hN inferInstance
  haveI : LocallyOfFinitePresentation θ := locallyOfFinitePresentation_theta π r C p₂ θ hθ₂
  apply AlgebraicGeometry.Etale.of_forall_existsUnique_lift
  intro R' S _ _ φ hφ hker a b hab

  let cR' : CommRingCat.of C ⟶ CommRingCat.of R' := Spec.preimage (b ≫ p₂)
  have hcR' : Spec.map cR' = b ≫ p₂ := Spec.map_preimage _
  letI : Algebra C R' := cR'.hom.toAlgebra
  letI : Algebra 𝒪 R' := (cR'.hom.comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra C S := (φ.comp cR'.hom).toAlgebra
  letI : Algebra 𝒪 S := ((φ.comp cR'.hom).comp (algebraMap 𝒪 C)).toAlgebra
  haveI : IsScalarTower 𝒪 C S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let p : R' →ₐ[C] S := AlgHom.mk φ (fun _ => rfl)
  have hsq : ∀ s t : R', p s = 0 → p t = 0 → s * t = 0 := by
    intro s t hs ht
    have hst : s * t ∈ RingHom.ker φ ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hs ht
    rwa [hker, Ideal.mem_bot] at hst

  let α : CommRingCat.of (Rch π r C) ⟶ CommRingCat.of S := Spec.preimage a
  have hα : Spec.map α = a := Spec.map_preimage _
  have hαC : ∀ c, α.hom (algebraMap C (Rch π r C) c) = algebraMap C S c := by
    have h1 : a ≫ θ ≫ p₂ = Spec.map (CommRingCat.ofHom φ) ≫ b ≫ p₂ := by rw [← Category.assoc, hab, Category.assoc]
    rw [hθ₂, ← hcR', ← hα, ← Spec.map_comp, ← Spec.map_comp] at h1
    have h2 := congrArg (fun f => CommRingCat.Hom.hom f) (Spec.map_injective h1)
    intro c
    exact congrFun (congrArg DFunLike.coe h2) c
  let x₀ : Rch π r C →ₐ[C] S := AlgHom.mk α.hom hαC
  have hz : b ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C R')) := by
    show b ≫ p₂ = Spec.map (CommRingCat.ofHom cR'.hom)
    rw [CommRingCat.ofHom_hom, hcR']
  have hcomm : Spec.map (CommRingCat.ofHom p.toRingHom) ≫ b = Spec.map (CommRingCat.ofHom x₀.toRingHom) ≫ θ := by
    show Spec.map (CommRingCat.ofHom φ) ≫ b = Spec.map (CommRingCat.ofHom α.hom) ≫ θ
    rw [CommRingCat.ofHom_hom, hα, hab]
  obtain ⟨x, ⟨hx₁, hx₂⟩, huniq⟩ := existsUnique_lift π hπ K₀ Onr r hres hunr hOnr_max hOnr_alg g₁ hg₁ G fM Θf hnat het C hC ψ p₁ p₂ hN
    hR dR hdR g h θ hθ₁ hθ₂ R' S p hφ hsq x₀ b hz hcomm
  refine ⟨Spec.map (CommRingCat.ofHom x.toRingHom), ⟨?_, hx₂⟩, ?_⟩
  · rw [← Spec.map_comp, ← hα]
    show Spec.map (CommRingCat.ofHom (p.comp x).toRingHom) = Spec.map (CommRingCat.ofHom x₀.toRingHom)
    rw [hx₁]
  · rintro l ⟨hl₁, hl₂⟩
    let β : CommRingCat.of (Rch π r C) ⟶ CommRingCat.of R' := Spec.preimage l
    have hβ : Spec.map β = l := Spec.map_preimage _
    have hβC : ∀ c, β.hom (algebraMap C (Rch π r C) c) = algebraMap C R' c := by
      have h1 : l ≫ θ ≫ p₂ = b ≫ p₂ := by rw [← Category.assoc, hl₂]
      rw [hθ₂, ← hcR', ← hβ, ← Spec.map_comp] at h1
      have h2 := congrArg (fun f => CommRingCat.Hom.hom f) (Spec.map_injective h1)
      intro c
      exact congrFun (congrArg DFunLike.coe h2) c
    let x' : Rch π r C →ₐ[C] R' := AlgHom.mk β.hom hβC
    have hx' : x' = x := by
      apply huniq
      constructor
      · apply AlgHom.coe_ringHom_injective
        show φ.comp β.hom = α.hom
        have h1 : Spec.map (CommRingCat.ofHom φ) ≫ l = a := hl₁
        rw [← hβ, ← hα, ← Spec.map_comp] at h1
        exact congrArg (fun f => CommRingCat.Hom.hom f) (Spec.map_injective h1)
      · show Spec.map (CommRingCat.ofHom β.hom) ≫ θ = b
        rw [CommRingCat.ofHom_hom, hβ, hl₂]
    rw [← hβ, ← hx']
    rfl

end Core

end EtaleEdgeChart
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine.EtaleEdgeChart"

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

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)
    (N : Scheme.{0}) (p₁ : N ⟶ M) (p₂ : N ⟶ Spec (CommRingCat.of C)) (hN : IsPullback p₁ p₂ fM (Scheme.specOver C))

    [Algebra 𝒪 (chartERing C (algebraMap 𝒪 C π) r)] [IsScalarTower 𝒪 C (chartERing C (algebraMap 𝒪 C π) r)]
    (hR : IsNilpotent (algebraMap 𝒪 (chartERing C (algebraMap 𝒪 C π) r) π))

    (d : DeligneDatum (K := K₀) π (chartERing C (algebraMap 𝒪 C π) r))
    (hd₀ : d.line (stdFullLattice K₀) =
      Submodule.span (chartERing C (algebraMap 𝒪 C π) r)
        {(chartERing.ξ C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : chartERing C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 1})
    (hd₁ : d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span (chartERing C (algebraMap 𝒪 C π) r)
        {(1 : chartERing C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (chartERing.η C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
        (actBaseChange (chartERing C (algebraMap 𝒪 C π) r) g₁ (stdFullLattice K₀)).toLinearMap)
    (hdE : d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))

    (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (θ : Spec (CommRingCat.of (chartERing C (algebraMap 𝒪 C π) r)) ⟶ N)
    (hθ₁ : θ ≫ p₁ = (Θf (chartERing C (algebraMap 𝒪 C π) r) hR
      (((IsScalarTower.toAlgHom 𝒪 C (chartERing C (algebraMap 𝒪 C π) r)).comp ψ,
        (Omega.action K₀ π).act (chartERing C (algebraMap 𝒪 C π) r) h d), g)).1)
    (hθ₂ : θ ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C (chartERing C (algebraMap 𝒪 C π) r)))) :
    Etale θ := by
  haveI := hdvr
  exact EtaleEdgeChart.etale_theta π hπ K₀ Onr r hres hunr hOnr_max hOnr_alg g₁ hg₁ G fM Θf hnat het C hC ψ p₁ p₂ hN hR d
    ⟨hd₀, hd₁, hdE⟩ g h θ hθ₁ hθ₂

end S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
end P2MW
export P2MW.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine (solution)
