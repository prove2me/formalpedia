-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/eaa07772-2bf5-53d8-8af7-9b6a97102672

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace EOAux

open TensorProduct

section Coord

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

def coordFun (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) : 𝒪 := Classical.choose (w.2 i)

theorem algebraMap_coordFun (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) :
    algebraMap 𝒪 K (coordFun w i) = (w : Fin 2 → K) i := Classical.choose_spec (w.2 i)

def coordEquiv : ↥(stdLattice 𝒪 K) ≃ₗ[𝒪] (Fin 2 → 𝒪) where
  toFun := coordFun
  map_add' v w := by
    funext i
    apply IsFractionRing.injective 𝒪 K
    rw [algebraMap_coordFun, Pi.add_apply, map_add, algebraMap_coordFun, algebraMap_coordFun]
    rfl
  map_smul' r w := by
    funext i
    apply IsFractionRing.injective 𝒪 K
    rw [algebraMap_coordFun, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, algebraMap_coordFun,
      Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
  invFun a := ⟨fun i => algebraMap 𝒪 K (a i), fun i => ⟨a i, rfl⟩⟩
  left_inv w := Subtype.ext (funext fun i => algebraMap_coordFun w i)
  right_inv a := funext fun i => IsFractionRing.injective 𝒪 K (by rw [algebraMap_coordFun])

theorem algebraMap_coordEquiv (w : ↥(stdLattice 𝒪 K)) (i : Fin 2) :
    algebraMap 𝒪 K (coordEquiv w i) = (w : Fin 2 → K) i := algebraMap_coordFun w i

theorem coordEquiv_stdBasisVec (j i : Fin 2) :
    coordEquiv (stdBasisVec (𝒪 := 𝒪) K j) i = (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply IsFractionRing.injective 𝒪 K
  rw [algebraMap_coordEquiv]
  show (Pi.single j (1 : K) : Fin 2 → K) i = algebraMap 𝒪 K ((Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

def stdBasis : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 := Module.Basis.ofEquivFun coordEquiv

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def tensorBasis : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Algebra.TensorProduct.basis B stdBasis

private def _root_.EOAux.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "EOAux" "coord"
theorem coord_tmul (i : Fin 2) (b : B) (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    coord B i (b ⊗ₜ[𝒪] w) = b * algebraMap 𝒪 B (coordEquiv w i) := by
  show (Algebra.TensorProduct.basis B stdBasis).repr (b ⊗ₜ[𝒪] w) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [stdBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem coord_tmul_stdBasisVec (i j : Fin 2) (b : B) :
    coord B i (b ⊗ₜ[𝒪] stdBasisVec K j) = if i = j then b else 0 := by
  rw [coord_tmul, coordEquiv_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

theorem eq_of_span_xi_eq (b b' : B)
    (h : Submodule.span B {b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} =
      Submodule.span B {b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}) : b = b' := by
  have hmem : b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 ∈
      Submodule.span B {b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrArg (coord (K := K) B 1) hc
  have h0 := congrArg (coord (K := K) B 0) hc
  simp only [map_smul, map_add, coord_tmul_stdBasisVec, smul_eq_mul] at h1 h0
  simp at h1 h0
  rw [← h0, h1, one_mul]

theorem eq_of_span_eta_eq (b b' : B)
    (h : Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}) : b = b' := by
  have hmem : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 ∈
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 := congrArg (coord (K := K) B 0) hc
  have h1 := congrArg (coord (K := K) B 1) hc
  simp only [map_smul, map_add, coord_tmul_stdBasisVec, smul_eq_mul] at h1 h0
  simp at h1 h0
  rw [← h1, h0, one_mul]

theorem lineBaseChange_span_singleton {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K)
    (v : latticeBaseChange 𝒪 K B M) :
    lineBaseChange f M (Submodule.span B {v}) = Submodule.span B' {LinearMap.rTensor (↥M.1) f.toLinearMap v} := by
  apply le_antisymm
  · rw [lineBaseChange]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [rTensor_smul_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [lineBaseChange]
    apply Submodule.span_mono
    exact Set.singleton_subset_iff.mpr ⟨v, Submodule.mem_span_singleton_self _, rfl⟩

end Coord

end EOAux

end

open EOAux in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :

    (∀ d : DeligneDatum (K := K) π B, d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) →
        ∃! x : chartERing 𝒪 π q →ₐ[𝒪] B,
          d.line (stdFullLattice K) =
            Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          d.line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B g (stdFullLattice K)).toLinearMap) ∧

    (∀ x : chartERing 𝒪 π q →ₐ[𝒪] B,
        ∃! d : DeligneDatum (K := K) π B,
          (d.line (stdFullLattice K) =
            Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          d.line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B g (stdFullLattice K)).toLinearMap) ∧
          d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K)) ∧

    (∀ (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B) (x : chartERing 𝒪 π q →ₐ[𝒪] B),
        (d.line (stdFullLattice K) =
            Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          d.line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B g (stdFullLattice K)).toLinearMap) →
          ((Omega K π).map φ d).line (stdFullLattice K) =
            Submodule.span B' {((φ.comp x) (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          ((Omega K π).map φ d).line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B' {(1 : B') ⊗ₜ[𝒪] stdBasisVec K 0 + ((φ.comp x) (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B' g (stdFullLattice K)).toLinearMap) := by
  classical
  refine ⟨fun d hd => ?_, fun x => ?_, ?_⟩
  ·
    obtain ⟨x, hx⟩ :=
      CerednikDrinfeld.FormalOmega.DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite π hπ q hq g hg B hB d hd
    refine ⟨x, hx, fun x' hx' => ?_⟩
    apply (chartERing.corepEquiv 𝒪 π q B).injective
    apply Subtype.ext
    rw [chartERing.corepEquiv_apply_val, chartERing.corepEquiv_apply_val]
    apply Prod.ext
    · exact eq_of_span_xi_eq B _ _ (hx'.1.symm.trans hx.1)
    · have hinj := Submodule.map_injective_of_injective (f := (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap)
        (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).injective
      exact eq_of_span_eta_eq B _ _ (hinj (hx'.2.symm.trans hx.2))
  ·
    obtain ⟨d, hd1, hd2, hd3⟩ :=
      CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (K := K) π hπ q hq g hg B hB x
    refine ⟨d, ⟨⟨hd1, hd2⟩, hd3⟩, fun d' hd' => ?_⟩
    exact CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d d' (FullLattice.act g (stdFullLattice K))
      (stdFullLattice K) hd3 (hd'.1.1.trans hd1.symm) (hd'.1.2.trans hd2.symm)
  ·
    intro B' _ _ φ d x hx
    obtain ⟨h1, h2⟩ := hx
    have hu : LinearMap.rTensor (↥(stdFullLattice (𝒪 := 𝒪) K).1) φ.toLinearMap
        ((x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) =
        ((φ.comp x) (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec K 1 := by
      simp only [map_add, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, AlgHom.comp_apply]
    have hv : LinearMap.rTensor (↥(stdFullLattice (𝒪 := 𝒪) K).1) φ.toLinearMap
        ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1) =
        (1 : B') ⊗ₜ[𝒪] stdBasisVec K 0 + ((φ.comp x) (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1 := by
      simp only [map_add, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, AlgHom.comp_apply]
    constructor
    · show lineBaseChange φ (stdFullLattice K) (d.line (stdFullLattice K)) = _
      rw [h1, lineBaseChange_span_singleton, hu]
    · show lineBaseChange φ (FullLattice.act g (stdFullLattice K)) (d.line (FullLattice.act g (stdFullLattice K))) = _
      rw [h2, Submodule.map_span, Set.image_singleton, lineBaseChange_span_singleton, Submodule.map_span, Set.image_singleton,
        LinearEquiv.coe_coe, LinearEquiv.coe_coe, rTensor_actBaseChange, hv]

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart (solution)
