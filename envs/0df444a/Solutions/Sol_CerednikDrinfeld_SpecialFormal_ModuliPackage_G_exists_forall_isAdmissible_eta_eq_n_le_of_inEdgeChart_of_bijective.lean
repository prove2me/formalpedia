-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.G.exists_forall_isAdmissible_eta_eq_n_le_of_inEdgeChart_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/941352c9-00ef-57a1-ac89-830453d94ff7

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_eta_eq_of_isLocalRing
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_iff_of_isBaseChange_of_isLocalHom
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap
import Theorems.Thm_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_exists_forall_isAdmissible_eta_eq_n_le_of_inEdgeChart_of_bijective
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

namespace ChartN
namespace Degenerate

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem inVertexChart_of_inEdgeChart_self (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K)
    (h : d.InEdgeChart π M M) : d.InVertexChart π M :=
  fun 𝔭 h𝔭 v hv => (h 𝔭 h𝔭).2.2.2 v hv

theorem inVertexChart_of_inEdgeChart_of_eq_smul (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (hM' : ∀ v : Fin 2 → K, v ∈ M'.1 → ∃ w : ↥M.1, v = (algebraMap 𝒪 K π) • (w : Fin 2 → K))
    (h : d.InEdgeChart π M' M) : d.InVertexChart π M :=
  fun 𝔭 h𝔭 v hv => (h 𝔭 h𝔭).2.2.1 v (fun hmem => hv (hM' v hmem))

theorem inEdgeChart_of_inVertexChart (d : DeligneDatum (K := K) π B) (M₁ M : FullLattice 𝒪 K)
    (hle : M₁.1 ≤ M.1) (hπM : ∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M₁.1)
    (h : d.InVertexChart π M) : d.InEdgeChart π M₁ M := by
  intro 𝔭 h𝔭
  refine ⟨hle, hπM, ?_, ?_⟩
  · intro v hv
    exact h 𝔭 h𝔭 v (fun ⟨w, hw⟩ => hv (hw ▸ hπM w))
  · intro v' hv' hmem
    have hv'M : (v' : Fin 2 → K) ∈ M.1 := hle v'.2
    apply h 𝔭 h𝔭 ⟨(v' : Fin 2 → K), hv'M⟩ (fun ⟨w, hw⟩ => hv' ⟨w, hw⟩)
    have himg : (d.line M₁ ⊔ 𝔭 • ⊤).map (inclBaseChange B hle) ≤ d.line M ⊔ 𝔭 • ⊤ := by
      rw [Submodule.map_sup]
      refine sup_le_sup (d.mono hle) ?_
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    have h1 : inclBaseChange B hle ((1 : B) ⊗ₜ[𝒪] v') = (1 : B) ⊗ₜ[𝒪] (⟨(v' : Fin 2 → K), hv'M⟩ : ↥M.1) := by
      simp only [inclBaseChange, LinearMap.baseChange_tmul]
      rfl
    rw [← h1]
    exact himg (Submodule.mem_map_of_mem hmem)

theorem exists_strict_neighbour [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] (hπ : Irreducible π)
    (M : FullLattice 𝒪 K) :
    ∃ M₁ : FullLattice 𝒪 K,
      latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M₁.1 ∧ M₁.1 < M.1 := by
  obtain ⟨c, n, β, g, -, hL⟩ :=
    LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice 𝒪 K π hπ M.1 M.2
  refine ⟨FullLattice.act (scalarGL c * g) (FullLattice.act (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdFullLattice K)),
    ?_, ?_⟩
  · show latticeMap _ M.1 < latticeMap (scalarGL c * g) (latticeMap (diagSnd _) (stdLattice 𝒪 K))
    conv_lhs => rw [hL, ← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
    rw [latticeMap_lt_latticeMap_iff]
    exact lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hπ) (latticeMap_scalarGL_ne_latticeMap_diagSnd hπ)
  · show latticeMap (scalarGL c * g) (latticeMap (diagSnd _) (stdLattice 𝒪 K)) < M.1
    conv_rhs => rw [hL]
    rw [latticeMap_lt_latticeMap_iff]
    exact latticeMap_diagSnd_lt_stdLattice hπ

theorem exists_strict_forall_inEdgeChart_of_not_strict [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K]
    (hπ : Irreducible π) (M' M : FullLattice 𝒪 K) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, (algebraMap 𝒪 K π) • v ∈ M'.1)
    (hns : ¬ (latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 ∧ M'.1 < M.1)) :
    ∃ M₁ : FullLattice 𝒪 K,
      latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M₁.1 ∧ M₁.1 < M.1 ∧
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B),
        d.InEdgeChart π M' M → d.InEdgeChart π M₁ M := by
  obtain ⟨M₁, h₁, h₂⟩ := exists_strict_neighbour π hπ M
  have hπle : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [unitOfNeZero_coe]
    exact hπM w hw
  have hπM₁ : ∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M₁.1 := fun v =>
    h₁.1 (mem_latticeMap_scalarGL.mpr ⟨v, v.2, by rw [unitOfNeZero_coe]⟩)
  refine ⟨M₁, h₁, h₂, fun B _ _ d hd => inEdgeChart_of_inVertexChart π d M₁ M h₂.le hπM₁ ?_⟩
  by_cases hMM : M'.1 = M.1
  · have e : M' = M := Subtype.ext hMM
    rw [e] at hd
    exact inVertexChart_of_inEdgeChart_self π d M hd
  · have hπeq : M'.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 := by
      by_contra hne
      exact hns ⟨lt_of_le_of_ne hπle (Ne.symm hne), lt_of_le_of_ne hle hMM⟩
    refine inVertexChart_of_inEdgeChart_of_eq_smul π d M' M ?_ hd
    intro v hv
    rw [hπeq] at hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    exact ⟨⟨w, hw⟩, by rw [unitOfNeZero_coe]⟩

end ChartN.Degenerate

namespace COREP

theorem isNoetherianRing_tensor_chartERing (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (q : ℕ)
    (C : Type) [Field C] [Algebra 𝒪 C] : IsNoetherianRing (C ⊗[𝒪] chartERing 𝒪 π q) := by

  haveI h1 : Algebra.FiniteType 𝒪 (edgeQuot 𝒪 π) :=
    Algebra.FiniteType.of_surjective (edgeQuot.mk 𝒪 π) (by
      unfold edgeQuot.mk edgeQuot
      exact Ideal.Quotient.mkₐ_surjective 𝒪 _)
  haveI : Algebra.FinitePresentation (edgeQuot 𝒪 π) (chartERing 𝒪 π q) :=
    IsLocalization.Away.finitePresentation (edgeQuot.discr 𝒪 π q)
  haveI h2 : Algebra.FiniteType (edgeQuot 𝒪 π) (chartERing 𝒪 π q) := Algebra.FiniteType.of_finitePresentation
  haveI h3 : Algebra.FiniteType 𝒪 (chartERing 𝒪 π q) := h1.trans h2
  haveI : IsNoetherianRing C := inferInstance
  exact Algebra.FiniteType.isNoetherianRing C (C ⊗[𝒪] chartERing 𝒪 π q)

theorem exists_gl_diag {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : π ≠ 0) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1] := by
  have hdet : Matrix.det (Matrix.diagonal ![algebraMap 𝒪 K π, 1]) ≠ 0 := by
    rw [Matrix.det_diagonal]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    exact fun h => hπ ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h)
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl⟩

theorem inEdgeChart_act_inv {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {S : Type} [CommRing S] [Algebra 𝒪 S] (h : Matrix.GeneralLinearGroup (Fin 2) K)
    (d : OmegaObj (K := K) π S) (M' M : FullLattice 𝒪 K)
    (hd : DeligneDatum.InEdgeChart π d (FullLattice.act h M') (FullLattice.act h M)) :
    DeligneDatum.InEdgeChart π ((Omega.action K π).act S h⁻¹ d) M' M := by
  have hact : (Omega.action K π).act S h ((Omega.action K π).act S h⁻¹ d) = d := by
    rw [← (Omega.action K π).act_mul S h h⁻¹ d, mul_inv_cancel, (Omega.action K π).act_one S d]
  have hpb : DeligneDatum.IsPullback (K := K) (π := π) S h⁻¹ ((Omega.action K π).act S h⁻¹ d) d := by
    have := DeligneDatum.isPullback_pullback π S h⁻¹ ((Omega.action K π).act S h⁻¹ d)
    have e : DeligneDatum.pullback π S h⁻¹ ((Omega.action K π).act S h⁻¹ d) = d := hact
    rwa [e] at this
  have key := DeligneDatum.inEdgeChart_act_of_isPullback (π := π) h⁻¹ hpb hd
  have e₁ : FullLattice.act h⁻¹ (FullLattice.act h M') = M' :=
    Subtype.ext (by simpa only [inv_inv] using act_act_inv (𝒪 := 𝒪) h⁻¹ M')
  have e₂ : FullLattice.act h⁻¹ (FullLattice.act h M) = M :=
    Subtype.ext (by simpa only [inv_inv] using act_act_inv (𝒪 := 𝒪) h⁻¹ M)
  rwa [e₁, e₂] at key

theorem inEdgeChart_map {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : OmegaObj (K := K) π B) (M' M : FullLattice 𝒪 K) (hd : DeligneDatum.InEdgeChart π d M' M) :
    DeligneDatum.InEdgeChart π ((Omega K π).map f d) M' M := by
  intro 𝔮 h𝔮
  haveI := h𝔮
  exact (CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_map_iff_edgeNondegAt_comap π f d 𝔮 M' M).mpr
    (hd _ (Ideal.comap_isPrime f 𝔮))

theorem exists_strict_of_inEdgeChart {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (π : 𝒪) (hπ : Irreducible π)
    (M' M : FullLattice 𝒪 K) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    ∃ M₁ : FullLattice 𝒪 K,
      latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M₁.1 ∧ M₁.1 < M.1 ∧
      ∀ (S : Type) [CommRing S] [Algebra 𝒪 S] (d : OmegaObj (K := K) π S),
        DeligneDatum.InEdgeChart π d M' M → DeligneDatum.InEdgeChart π d M₁ M := by
  by_cases hs : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 ∧ M'.1 < M.1
  · exact ⟨M', hs.1, hs.2, fun _ _ _ _ h => h⟩
  · obtain ⟨M₁, h₁, h₂, h⟩ := ChartN.Degenerate.exists_strict_forall_inEdgeChart_of_not_strict π hπ M' M hle hπM hs
    exact ⟨M₁, h₁, h₂, fun S _ _ d hd => h S d hd⟩

private theorem _root_.COREP.corep {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (M' M : FullLattice 𝒪 K₀) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra 𝒪 A) (_ : IsNoetherianRing A)
      (Ψ : Onr →ₐ[𝒪] A) (D : OmegaObj (K := K₀) π A),
      algebraMap 𝒪 A π = 0 ∧
      ∀ (S : Type) [CommRing S] [Algebra 𝒪 S], algebraMap 𝒪 S π = 0 →
        ∀ (ψ : Onr →ₐ[𝒪] S) (d : OmegaObj (K := K₀) π S), DeligneDatum.InEdgeChart π d M' M →
          ∃ φ : A →ₐ[𝒪] S, φ.comp Ψ = ψ ∧ (Omega K₀ π).map φ D = d := by
  classical
  haveI := hdvr
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) :=
    Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)

  obtain ⟨M₁, h₁, h₂, hmono⟩ := exists_strict_of_inEdgeChart π hπ M' M hle hπM

  obtain ⟨g, hg⟩ := exists_gl_diag (K := K₀) π hπ.ne_zero
  obtain ⟨h, hM, hM₁⟩ :=
    CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt π hπ g hg M₁ M h₁ h₂

  set 𝔨 : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π} with h𝔨
  haveI : 𝔨.IsMaximal := hOnr_max
  letI : Field (Onr ⧸ 𝔨) := Ideal.Quotient.field 𝔨
  haveI : IsNoetherianRing ((Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r) :=
    isNoetherianRing_tensor_chartERing 𝒪 π r (Onr ⧸ 𝔨)
  have hCπ : algebraMap 𝒪 (Onr ⧸ 𝔨) π = 0 := by
    rw [← Ideal.Quotient.mk_comp_algebraMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hAπ : algebraMap 𝒪 ((Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r) π = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply, hCπ, TensorProduct.zero_tmul]
  have hAnil : IsNilpotent (algebraMap 𝒪 ((Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r) π) := by rw [hAπ]; exact IsNilpotent.zero

  set xA : chartERing 𝒪 π r →ₐ[𝒪] (Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r := Algebra.TensorProduct.includeRight with hxA
  obtain ⟨-, hA2, hA3⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
      π hπ r hres g hg ((Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r) hAnil
  obtain ⟨D₀, ⟨hD₀l, hD₀c⟩, -⟩ := hA2 xA
  set iL : (Onr ⧸ 𝔨) →ₐ[𝒪] (Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r := Algebra.TensorProduct.includeLeft with hiL
  refine ⟨(Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r, inferInstance, inferInstance, inferInstance,
    iL.comp (Ideal.Quotient.mkₐ 𝒪 𝔨), (Omega.action K₀ π).act _ h D₀, hAπ, ?_⟩
  intro S _ _ hS ψ d hd
  have hSnil : IsNilpotent (algebraMap 𝒪 S π) := by rw [hS]; exact IsNilpotent.zero

  have hd₁ : DeligneDatum.InEdgeChart π d M₁ M := hmono S d hd
  set d'' : OmegaObj (K := K₀) π S := (Omega.action K₀ π).act S h⁻¹ d with hd''
  have hd''c : DeligneDatum.InEdgeChart π d'' (FullLattice.act g (stdFullLattice K₀)) (stdFullLattice K₀) := by
    apply inEdgeChart_act_inv π h d
    rw [hM, hM₁]; exact hd₁
  obtain ⟨hS1, hS2, -⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
      π hπ r hres g hg S hSnil
  obtain ⟨x, hxl, -⟩ := hS1 d'' hd''c

  have hψ𝔨 : ∀ a ∈ 𝔨, ψ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, AlgHom.commutes, hS, mul_zero]
  let ψb : Onr ⧸ 𝔨 →ₐ[𝒪] S := Ideal.Quotient.liftₐ 𝔨 ψ hψ𝔨
  let φ : (Onr ⧸ 𝔨) ⊗[𝒪] chartERing 𝒪 π r →ₐ[𝒪] S :=
    Algebra.TensorProduct.lift ψb x (fun _ _ => Commute.all _ _)
  have hφx : φ.comp xA = x := Algebra.TensorProduct.lift_comp_includeRight ψb x (fun _ _ => Commute.all _ _)
  refine ⟨φ, ?_, ?_⟩
  ·
    ext a
    show φ (iL (Ideal.Quotient.mkₐ 𝒪 𝔨 a)) = ψ a
    rw [hiL, ← AlgHom.comp_apply, Algebra.TensorProduct.lift_comp_includeLeft]
    rfl
  ·
    rw [(Omega.action K₀ π).act_map φ h D₀]
    have hφD₀ : (Omega K₀ π).map φ D₀ = d'' := by
      obtain ⟨d₁, -, huniq⟩ := hS2 x
      have e1 := huniq ((Omega K₀ π).map φ D₀) ⟨by
        have := hA3 S φ D₀ xA hD₀l
        rw [hφx] at this
        exact this, inEdgeChart_map π φ D₀ _ _ hD₀c⟩
      have e2 := huniq d'' ⟨hxl, hd''c⟩
      exact e1.trans e2.symm
    rw [hφD₀, hd'', ← (Omega.action K₀ π).act_mul, mul_inv_cancel, (Omega.action K₀ π).act_one]

p2m_export "COREP" "corep"
end COREP

namespace EDBDD

open MvPowerSeries in

theorem mem_span_range_X_of_constantCoeff_eq_zero {B : Type} [CommRing B]
    (f : MvPowerSeries (Fin 2) B) (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (Series.id B)) := by
  classical

  let h : MvPowerSeries (Fin 2) B := fun m => if m 0 = 0 then f m else 0
  have hcoeff : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m h = if m 0 = 0 then MvPowerSeries.coeff m f else 0 :=
    fun m => rfl
  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) B) ∣ (f - h) := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [map_sub, hcoeff, if_pos hm, sub_self]
  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) B) ∣ h := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hcoeff]
    split_ifs with hm0
    · have : m = 0 := by
        ext i; fin_cases i
        · exact hm0
        · exact hm
      subst this
      exact hf
    · rfl
  have hX : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ∈ Ideal.span (Set.range (Series.id B)) :=
    fun i => Ideal.subset_span ⟨i, rfl⟩
  have : f = (f - h) + h := by ring
  rw [this]
  refine Ideal.add_mem _ ?_ ?_
  · obtain ⟨q, hq⟩ := h0; rw [hq]; exact Ideal.mul_mem_right _ _ (hX 0)
  · obtain ⟨q, hq⟩ := h1; rw [hq]; exact Ideal.mul_mem_right _ _ (hX 1)

open MvPowerSeries in

theorem span_range_eq_of_comp_eq_id {B : Type} [CommRing B] {u v : Series B}
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (huv : u.comp v = Series.id B) :
    Ideal.span (Set.range v) = Ideal.span (Set.range (Series.id B)) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_span_range_X_of_constantCoeff_eq_zero _ (hv0 i)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩

    have hXi : (Series.id B) i = MvPowerSeries.subst v (u i) := by
      rw [← huv]; rfl
    rw [SetLike.mem_coe, hXi]
    have hv : MvPowerSeries.HasSubst v := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
    have hmem := mem_span_range_X_of_constantCoeff_eq_zero _ (hu0 i)

    have key : (Ideal.span (Set.range (Series.id B))).map (MvPowerSeries.substAlgHom hv).toRingHom ≤
        Ideal.span (Set.range v) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      refine Ideal.subset_span ⟨j, ?_⟩
      show v j = MvPowerSeries.substAlgHom hv (MvPowerSeries.X j)
      rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hv]
    have := key (Ideal.mem_map_of_mem _ hmem)
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.coe_substAlgHom] at this

theorem hasKernelOfDegree_one_of_inverse {B : Type} [CommRing B] {u v : Series B}
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (huv : u.comp v = Series.id B) :
    FormalODModule.HasKernelOfDegree v 1 := by
  have hid := CerednikDrinfeld.FormalODModule.hasKernelOfDegree_id B
  have hsp := span_range_eq_of_comp_eq_id hu0 hv0 huv
  have hspf : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Ideal.span (Set.range (v.map f)) = Ideal.span (Set.range ((Series.id B).map f)) := by
    intro κ _ f
    have hu0' : ∀ i, MvPowerSeries.constantCoeff ((u.map f) i) = 0 := fun i => by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map f (u i)) = 0
      rw [MvPowerSeries.constantCoeff_map, hu0, map_zero]
    have hv0' : ∀ i, MvPowerSeries.constantCoeff ((v.map f) i) = 0 := fun i => by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map f (v i)) = 0
      rw [MvPowerSeries.constantCoeff_map, hv0, map_zero]
    have huv' : (u.map f).comp (v.map f) = Series.id κ := by
      rw [← Series.map_comp f u v hv0, huv, Series.map_id]
    rw [span_range_eq_of_comp_eq_id hu0' hv0' huv', Series.map_id]
  unfold FormalODModule.HasKernelOfDegree FormalODModule.KerAlgebra at hid ⊢
  obtain ⟨h1, h2, h3⟩ := hid
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · rw [hsp]; exact h1
  · rw [hsp]; exact h2
  · rw [hspf κ f]; exact h3 κ f

theorem step10_represent {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (ι : Zp2 p →+* O) {B B' : Type} [CommRing B] [CommRing B'] [IsNoetherianRing B'] (g : B →+* B')
    (hg : Function.Bijective (reduceMap (p := p) g))
    (ψ : O →+* B) (t₀ : Rigidified p Φ B) (h₀ : t₀.IsAdmissible ι ψ)
    (s : Rigidified p Φ B') (hs : s.IsAdmissible ι (g.comp ψ)) (hiso : (t₀.map g).IsIsomorphic s) :
    ∃ t' : Rigidified p Φ B, t'.IsAdmissible ι ψ ∧ t₀.IsIsomorphic t' ∧ t'.n = s.n := by
  obtain ⟨u, v, m, hu, hv, hvu, huv, hid⟩ := hiso

  set mk : B →+* B ⧸ pIdeal p B := Ideal.Quotient.mk (pIdeal p B) with hmkdef
  set mk' : B' →+* B' ⧸ pIdeal p B' := Ideal.Quotient.mk (pIdeal p B') with hmk'def
  set θ : B ⧸ pIdeal p B →+* B' ⧸ pIdeal p B' := reduceMap (p := p) g with hθdef
  let θe : B ⧸ pIdeal p B ≃+* B' ⧸ pIdeal p B' := RingEquiv.ofBijective θ hg
  set θi : B' ⧸ pIdeal p B' →+* B ⧸ pIdeal p B := θe.symm.toRingHom with hθidef
  have hθiθ : θi.comp θ = RingHom.id _ := RingHom.ext fun x => θe.symm_apply_apply x
  have hθθi : θ.comp θi = RingHom.id _ := RingHom.ext fun x => θe.apply_symm_apply x
  have hθi_bij : Function.Bijective θi := θe.symm.bijective
  have hmk : mk'.comp g = θ.comp mk := RingHom.ext fun b => rfl
  haveI : IsNoetherianRing (B' ⧸ pIdeal p B') := inferInstance

  have hub : FormalODModule.IsODHom (t₀.map g).Xbar s.Xbar (u.map mk') := hu.map mk'
  have hvb : FormalODModule.IsODHom s.Xbar (t₀.map g).Xbar (v.map mk') := hv.map mk'
  have hvu' : (v.map mk').comp (u.map mk') = Series.id _ := by
    rw [← Series.map_comp mk' _ _ hu.constantCoeff, hvu, Series.map_id]
  have huv' : (u.map mk').comp (v.map mk') = Series.id _ := by
    rw [← Series.map_comp mk' _ _ hv.constantCoeff, huv, Series.map_id]
  have hXg : (t₀.map g).Xbar = t₀.Xbar.map θ := by
    show (t₀.X.map g).map mk' = (t₀.X.map mk).map θ
    rw [FormalODModule.map_map, FormalODModule.map_map, hmk]

  have hsρ0 : ∀ i, MvPowerSeries.constantCoeff (s.ρ i) = 0 := hs.constantCoeff_ρ
  have hρ0 : ∀ i, MvPowerSeries.constantCoeff (t₀.ρ i) = 0 := h₀.constantCoeff_ρ
  have hρg0 : ∀ i, MvPowerSeries.constantCoeff ((t₀.map g).ρ i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map θ (t₀.ρ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hρ0, map_zero]
  have hA : ∀ k i, MvPowerSeries.constantCoeff (s.Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => (s.Xbar.isLawHom_act _).1
  have hA' : ∀ k i, MvPowerSeries.constantCoeff ((t₀.map g).Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => ((t₀.map g).Xbar.isLawHom_act _).1

  set ρ₁ : Series (B' ⧸ pIdeal p B') := (v.map mk').comp s.ρ with hρ₁def
  have hρ₁0 : ∀ i, MvPowerSeries.constantCoeff (ρ₁ i) = 0 :=
    Series.constantCoeff_comp hvb.constantCoeff hsρ0
  set ρ' : Series (B ⧸ pIdeal p B) := ρ₁.map θi with hρ'def
  refine ⟨⟨t₀.X, s.n, ρ'⟩, ⟨h₀.1, h₀.2.1, ?_⟩, ?_, rfl⟩
  ·
    have hsρ := hs.2.2
    have h1 : FormalODModule.IsIsogenyOfHeight ((t₀.map g).Φbar (g.comp ψ)) (t₀.map g).Xbar ρ₁ (4 * s.n) := by
      refine ⟨hvb.comp hsρ.1, ?_⟩
      have hdeg := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp
        hsρ0 hvb.constantCoeff hsρ.2 (hasKernelOfDegree_one_of_inverse hub.constantCoeff hvb.constantCoeff huv')
      rwa [mul_one] at hdeg
    have h2 : FormalODModule.IsIsogenyOfHeight (((t₀.map g).Φbar (g.comp ψ)).map θi) ((t₀.map g).Xbar.map θi) ρ'
        (4 * s.n) :=
      ⟨h1.1.map θi, CerednikDrinfeld.FormalODModule.HasKernelOfDegree.map_of_bijective θi hθi_bij h1.2⟩
    have e1 : ((t₀.map g).Φbar (g.comp ψ)).map θi = Φ.map (residueMap ψ) := by
      rw [Rigidified.Φbar_map, Rigidified.Φbar, FormalODModule.map_map, FormalODModule.map_map,
        ← hθdef, hθiθ, RingHom.id_comp]
    have e2 : (t₀.map g).Xbar.map θi = t₀.Xbar := by
      rw [hXg, FormalODModule.map_map, hθiθ, FormalODModule.map_id]
    rw [e1, e2] at h2
    exact h2
  ·
    refine ⟨Series.id B, Series.id B, m, FormalODModule.IsODHom.id _, FormalODModule.IsODHom.id _,
      Series.comp_id _, Series.comp_id _, ?_⟩
    show (t₀.Xbar.act ((p : Zp2 p) ^ (m + s.n))).comp (((Series.id B).map mk).comp t₀.ρ) =
      (t₀.Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp ρ'
    rw [Series.map_id, Series.id_comp _ hρ0]

    have key : ((t₀.map g).Xbar.act ((p : Zp2 p) ^ (m + s.n))).comp (t₀.map g).ρ =
        ((t₀.map g).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp ρ₁ := by
      have huρ : ∀ i, MvPowerSeries.constantCoeff ((((u.map mk').comp (t₀.map g).ρ)) i) = 0 :=
        Series.constantCoeff_comp hub.constantCoeff hρg0
      have := congrArg (fun φ => (v.map mk').comp φ) hid
      rw [← Series.comp_assoc _ _ _ (hA _) huρ, hvb.2.1, Series.comp_assoc _ _ _ hvb.constantCoeff huρ,
        ← Series.comp_assoc _ _ _ hub.constantCoeff hρg0, hvu', Series.id_comp _ hρg0,
        ← Series.comp_assoc _ _ _ (hA _) hsρ0, hvb.2.1, Series.comp_assoc _ _ _ hvb.constantCoeff hsρ0] at this
      exact this

    have key2 := congrArg (Series.map θi) key
    rw [Series.map_comp θi _ _ hρg0, Series.map_comp θi _ _ hρ₁0] at key2
    have eρ : ((t₀.map g).ρ).map θi = t₀.ρ := by
      show (t₀.ρ.map θ).map θi = t₀.ρ
      rw [Series.map_map, hθiθ, Series.map_ringHom_id]
    have eA : ∀ k, ((t₀.map g).Xbar.act ((p : Zp2 p) ^ k)).map θi = t₀.Xbar.act ((p : Zp2 p) ^ k) := by
      intro k
      rw [← FormalODModule.map_act, hXg, FormalODModule.map_map, hθiθ, FormalODModule.map_id]
    rw [eρ, eA, eA] at key2
    exact key2

theorem step2_corep {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (M' M : FullLattice 𝒪 K₀) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra 𝒪 A) (_ : IsNoetherianRing A)
      (Ψ : Onr →ₐ[𝒪] A) (D : OmegaObj (K := K₀) π A),
      algebraMap 𝒪 A π = 0 ∧
      ∀ (S : Type) [CommRing S] [Algebra 𝒪 S], algebraMap 𝒪 S π = 0 →
        ∀ (ψ : Onr →ₐ[𝒪] S) (d : OmegaObj (K := K₀) π S), DeligneDatum.InEdgeChart π d M' M →
          ∃ φ : A →ₐ[𝒪] S, φ.comp Ψ = ψ ∧ (Omega K₀ π).map φ D = d :=
  COREP.corep 𝒪 hdvr π hπ hres K₀ Onr hOnr_max M' M hle hπM

end EDBDD

open EDBDD in
theorem solution
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (MD : ModuliPackage.{0, 0} r Onr) (hMD : MD.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → MD.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = MD.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : MD.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  MD.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))

      (eD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 MD).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)

      (hnatD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 MD).obj B), eD B' hB' ((ModuliPackage.G 𝒪 MD).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (eD B hB x))

      (hbijD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (eD B hB))

      (hfstD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 MD).obj B), (eD B hB x).1 = x.ψ)
    :
    ∀ (M' M : FullLattice 𝒪 K₀), M'.1 ≤ M.1 → (∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) →
      ∃ Nγ : ℕ, ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Algebra 𝒪 B]
        (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (ModuliPackage.G 𝒪 MD).obj B),
        DeligneDatum.InEdgeChart π (eD B hB y).2 M' M →
          ∃ t : Rigidified r Φ B, t.IsAdmissible ι (y.ψ : Onr →+* B) ∧ η B (y.ψ : Onr →+* B) y.nilp t = y.pt ∧ t.n ≤ Nγ := by
  intro M' M hle hπM

  obtain ⟨A, _instA, _algA, _noethA, Ψ, D, hAπ, hcorep⟩ :=
    step2_corep 𝒪 hdvr π hπ hres K₀ Onr hOnr_max M' M hle hπM
  have hAnil : IsNilpotent (algebraMap 𝒪 A π) := by rw [hAπ]; exact IsNilpotent.zero

  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : (ModuliPackage.G 𝒪 MD).obj A,
      eD A hAnil x₁ = (⟨Ψ, D⟩ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj A) :=
    (hbijD A hAnil).2 _
  have hx₁ψ : x₁.ψ = Ψ := by have := hfstD A hAnil x₁; rw [hx₁] at this; exact this.symm

  obtain ⟨m, f, hf, hcov⟩ := hη.2.2 A (x₁.ψ : Onr →+* A) x₁.nilp x₁.pt
  have hLnil : ∀ i : Fin m, IsNilpotent ((r : ℕ) : Localization.Away (f i)) := fun i => by
    simpa only [map_natCast] using x₁.nilp.map (algebraMap A (Localization.Away (f i)))
  have hLnoeth : ∀ i : Fin m, IsNoetherianRing (Localization.Away (f i)) := fun i =>
    IsLocalization.isNoetherianRing (Submonoid.powers (f i)) (Localization.Away (f i)) inferInstance
  have hrep : ∀ i : Fin m, ∃ t : Rigidified r Φ (Localization.Away (f i)),
      t.IsAdmissible ι ((algebraMap A (Localization.Away (f i))).comp (x₁.ψ : Onr →+* A)) ∧
      η (Localization.Away (f i)) ((algebraMap A (Localization.Away (f i))).comp (x₁.ψ : Onr →+* A)) (hLnil i) t =
        MD.map (ψ' := (algebraMap A (Localization.Away (f i))).comp (x₁.ψ : Onr →+* A)) x₁.nilp (hLnil i)
          (algebraMap A (Localization.Away (f i))) rfl x₁.pt := by
    intro i
    haveI := hLnoeth i
    exact hcov i (Localization.Away (f i)) (hLnil i)
  choose t ht using hrep
  refine ⟨Finset.univ.sup (fun i => (t i).n), ?_⟩
  intro B _ _ _ _ hB y hy

  have hπr : ∃ c : 𝒪, c * (r : 𝒪) = π := by
    rw [← Ideal.mem_span_singleton']
    rw [hunr]; exact Ideal.mem_span_singleton_self π
  obtain ⟨c, hc⟩ := hπr
  let I : Ideal B := pIdeal r B
  have hBr : IsNilpotent ((r : ℕ) : B) := y.nilp
  have hI : I ≠ ⊤ := by
    intro htop
    have hu : IsUnit ((r : ℕ) : B) := Ideal.span_singleton_eq_top.mp htop
    have hmem : ((r : ℕ) : B) ∈ IsLocalRing.maximalIdeal B :=
      nilpotent_iff_mem_prime.mp hBr _ (IsLocalRing.maximalIdeal.isMaximal B).isPrime
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu
  haveI : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (B ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let red : B →ₐ[𝒪] B ⧸ I := Ideal.Quotient.mkₐ 𝒪 I
  have hBπ : algebraMap 𝒪 (B ⧸ I) π = 0 := by
    rw [← Ideal.Quotient.mk_comp_algebraMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← hc, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hBnil : IsNilpotent (algebraMap 𝒪 (B ⧸ I) π) := by rw [hBπ]; exact IsNilpotent.zero
  haveI hredloc : IsLocalHom (red : B →ₐ[𝒪] B ⧸ I) :=
    ⟨(IsLocalHom.of_surjective (red : B →+* B ⧸ I) (Ideal.Quotient.mkₐ_surjective 𝒪 I)).map_nonunit⟩
  let ybar : (ModuliPackage.G 𝒪 MD).obj (B ⧸ I) := (ModuliPackage.G 𝒪 MD).map red y
  have hybar_e : eD (B ⧸ I) hBnil ybar =
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map red (eD B hB y) :=
    hnatD B (B ⧸ I) hB hBnil red y
  have hybar_chart : DeligneDatum.InEdgeChart π (eD (B ⧸ I) hBnil ybar).2 M' M := by
    rw [hybar_e]
    show DeligneDatum.InEdgeChart π (DeligneDatum.map π red (eD B hB y).2) M' M
    exact (CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_iff_of_isBaseChange_of_isLocalHom π red
      (eD B hB y).2 _ (DeligneDatum.isBaseChange_map π red (eD B hB y).2) M' M).mpr hy
  have hybar_ψ : ybar.ψ = red.comp y.ψ := rfl

  obtain ⟨φ, hφΨ, hφD⟩ := hcorep (B ⧸ I) hBπ (red.comp y.ψ) (eD (B ⧸ I) hBnil ybar).2 hybar_chart
  have hclass : (ModuliPackage.G 𝒪 MD).map φ x₁ = ybar := by
    apply (hbijD (B ⧸ I) hBnil).1
    rw [hnatD A (B ⧸ I) hAnil hBnil φ x₁, hx₁]
    refine Prod.ext ?_ ?_
    · show φ.comp Ψ = (eD (B ⧸ I) hBnil ybar).1
      rw [hfstD, hybar_ψ, hφΨ]
    · exact hφD

  obtain ⟨i, hi⟩ : ∃ i : Fin m, IsUnit (φ (f i)) := by
    by_contra hno
    push_neg at hno
    have hle' : Ideal.span (Set.range ((φ : A →+* B ⧸ I) ∘ f)) ≤ IsLocalRing.maximalIdeal (B ⧸ I) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (hno j)
    have htop : Ideal.span (Set.range ((φ : A →+* B ⧸ I) ∘ f)) = ⊤ := by
      rw [Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    exact (IsLocalRing.maximalIdeal.isMaximal (B ⧸ I)).ne_top (top_le_iff.mp (htop ▸ hle'))
  let L := Localization.Away (f i)
  haveI : IsNoetherianRing L := hLnoeth i
  obtain ⟨lam, hlam⟩ : ∃ lam : L →+* B ⧸ I, lam.comp (algebraMap A L) = (φ : A →+* B ⧸ I) :=
    ⟨IsLocalization.Away.lift (f i) hi, IsLocalization.Away.lift_comp (f i) hi⟩

  have hcore : ∀ (χ : A →+* B ⧸ I) (hχ : lam.comp (algebraMap A L) = χ) (hT : IsNilpotent ((r : ℕ) : B ⧸ I)),
      ((t i).map lam).IsAdmissible ι (χ.comp (x₁.ψ : Onr →+* A)) ∧
      η (B ⧸ I) (χ.comp (x₁.ψ : Onr →+* A)) hT ((t i).map lam) =
        MD.map (ψ' := χ.comp (x₁.ψ : Onr →+* A)) x₁.nilp hT χ rfl x₁.pt := by
    intro χ hχ hT
    subst hχ
    refine ⟨?_, ?_⟩
    · rw [RingHom.comp_assoc]
      exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ lam (t i) (ht i).1
    · have hnat := hη.2.1 L (B ⧸ I) ((algebraMap A L).comp (x₁.ψ : Onr →+* A))
        ((lam.comp (algebraMap A L)).comp (x₁.ψ : Onr →+* A)) (hLnil i) hT lam
        (RingHom.comp_assoc _ _ _).symm (t i) (ht i).1
      rw [hnat, (ht i).2, ← MD.map_comp]
  have hmember : ((t i).map lam).IsAdmissible ι (ybar.ψ : Onr →+* B ⧸ I) ∧
      η (B ⧸ I) (ybar.ψ : Onr →+* B ⧸ I) ybar.nilp ((t i).map lam) = ybar.pt := by
    rw [← hclass]
    exact hcore (φ : A →+* B ⧸ I) hlam _

  obtain ⟨t₀, ht₀adm, ht₀⟩ : ∃ t₀ : Rigidified r Φ B,
      t₀.IsAdmissible ι (y.ψ : Onr →+* B) ∧ η B (y.ψ : Onr →+* B) y.nilp t₀ = y.pt :=
    CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isAdmissible_eta_eq_of_isLocalRing ι Φ MD η hη.2.2
      B (y.ψ : Onr →+* B) y.nilp y.pt

  have ht₀red : (t₀.map (red : B →+* B ⧸ I)).IsAdmissible ι (ybar.ψ : Onr →+* B ⧸ I) :=
    CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ (red : B →+* B ⧸ I) t₀ ht₀adm
  have ht₀red_eq : η (B ⧸ I) (ybar.ψ : Onr →+* B ⧸ I) ybar.nilp (t₀.map (red : B →+* B ⧸ I)) = ybar.pt := by
    have hnat := hη.2.1 B (B ⧸ I) (y.ψ : Onr →+* B) (ybar.ψ : Onr →+* B ⧸ I) y.nilp ybar.nilp
      (red : B →+* B ⧸ I) rfl t₀ ht₀adm
    rw [hnat, ht₀]
    rfl
  have hiso : (t₀.map (red : B →+* B ⧸ I)).IsIsomorphic ((t i).map lam) :=
    (hη.1 (B ⧸ I) (ybar.ψ : Onr →+* B ⧸ I) ybar.nilp _ _ ht₀red hmember.1).1
      (ht₀red_eq.trans hmember.2.symm)

  have hIbot : pIdeal r (B ⧸ I) = ⊥ := by
    have h0 : ((r : ℕ) : B ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    rw [pIdeal, h0, Ideal.span_singleton_eq_bot]
  have hred_bij : Function.Bijective (reduceMap (p := r) (red : B →+* B ⧸ I)) := by
    constructor
    · intro a b hab
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hab' : Ideal.Quotient.mk (pIdeal r (B ⧸ I)) ((red : B →+* B ⧸ I) a) =
          Ideal.Quotient.mk (pIdeal r (B ⧸ I)) ((red : B →+* B ⧸ I) b) := by
        simpa only [reduceMap, residueMap, Ideal.quotientMap_mk] using hab
      rw [Ideal.Quotient.eq, hIbot, Ideal.mem_bot, ← map_sub] at hab'
      rw [Ideal.Quotient.eq]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hab'
    · intro z
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝒪 I w
      exact ⟨Ideal.Quotient.mk _ b, by simp only [reduceMap, residueMap, Ideal.quotientMap_mk]; rfl⟩
  obtain ⟨t', ht'adm, ht'iso, ht'n⟩ :=
    step10_represent ι (red : B →+* B ⧸ I) hred_bij (y.ψ : Onr →+* B) t₀ ht₀adm ((t i).map lam)
      (by have h__af := hmember.1; simp only [hybar_ψ, AlgHom.coe_comp] at h__af; exact h__af) hiso

  refine ⟨t', ht'adm, ?_, ?_⟩
  · rw [← ht₀]
    exact ((hη.1 B (y.ψ : Onr →+* B) y.nilp t₀ t' ht₀adm ht'adm).2 ht'iso).symm
  · rw [ht'n, Rigidified.map_n]
    exact Finset.le_sup (f := fun j => (t j).n) (Finset.mem_univ i)

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_exists_forall_isAdmissible_eta_eq_n_le_of_inEdgeChart_of_bijective
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_exists_forall_isAdmissible_eta_eq_n_le_of_inEdgeChart_of_bijective (solution)
