-- Prove2me | solution 1 for CerednikDrinfeld.exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ba1fb321-50ac-519b-9143-9c8c8176c9c0

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_basicOpen_le_preimage_chartMorphism_of_level_zero_of_cerednikDrinfeld_quotient
import Theorems.Thm_IsDiscreteValuationRing_of_isAdicComplete_span_singleton_of_isMaximal
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_injective
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

noncomputable section

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
section Translate
variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev tr (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) : DeligneDatum (K := K₀) π B :=
  (Omega.action K₀ π).act B g d

theorem tr_one (d : DeligneDatum (K := K₀) π B) : tr π 1 d = d := (Omega.action K₀ π).act_one B d

theorem tr_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) :
    tr π (g * h) d = tr π g (tr π h d) := (Omega.action K₀ π).act_mul B g h d

theorem isPullback_inv_iff (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d d' : DeligneDatum (K := K₀) π B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d' ↔ d' = tr π g d := by
  constructor
  · intro h
    apply DeligneDatum.ext'
    funext M
    exact h M
  · rintro rfl
    exact DeligneDatum.isPullback_pullback π B g⁻¹ d

theorem isPullback_inv_tr (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d (tr π g d) :=
  (isPullback_inv_iff π g d _).2 rfl

end Translate

end EDB

namespace EDB
namespace Coord

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

theorem coordEquiv_eq_of {w : ↥(stdLattice 𝒪 K)} {i : Fin 2} {r : 𝒪} (h : (w : Fin 2 → K) i = algebraMap 𝒪 K r) :
    coordEquiv w i = r :=
  IsFractionRing.injective 𝒪 K (by rw [algebraMap_coordEquiv, h])

theorem coordEquiv_stdBasisVec (j i : Fin 2) :
    coordEquiv (stdBasisVec (𝒪 := 𝒪) K j) i = (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply coordEquiv_eq_of
  show (Pi.single j (1 : K) : Fin 2 → K) i = algebraMap 𝒪 K ((Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

def stdBasis : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 := Module.Basis.ofEquivFun coordEquiv

theorem stdBasis_repr (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) (i : Fin 2) : stdBasis.repr w i = coordEquiv w i := by
  show (Module.Basis.ofEquivFun coordEquiv).repr w i = _
  rw [Module.Basis.ofEquivFun_repr_apply]

theorem stdBasis_apply (i : Fin 2) : stdBasis i = stdBasisVec (𝒪 := 𝒪) K i := by
  apply stdBasis.repr.injective
  ext j
  rw [Module.Basis.repr_self, stdBasis_repr, coordEquiv_stdBasisVec, Finsupp.single_apply, Pi.single_apply]
  simp only [eq_comm]

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def tensorBasis : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Algebra.TensorProduct.basis B stdBasis

theorem tensorBasis_apply (i : Fin 2) : tensorBasis B i = (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K i := by
  rw [tensorBasis, Algebra.TensorProduct.basis_apply, stdBasis_apply]

private def _root_.EDB.Coord.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "EDB.Coord" "coord"
theorem coord_tmul (i : Fin 2) (b : B) (w : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    coord B i (b ⊗ₜ[𝒪] w) = b * algebraMap 𝒪 B (coordEquiv w i) := by
  show (Algebra.TensorProduct.basis B stdBasis).repr (b ⊗ₜ[𝒪] w) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [stdBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem coord_tmul_stdBasisVec (i j : Fin 2) (b : B) :
    coord B i (b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K j) = if i = j then b else 0 := by
  rw [coord_tmul, coordEquiv_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

omit B in
theorem coordEquiv_smul_stdBasisVec (r : 𝒪) (j i : Fin 2) :
    coordEquiv (r • stdBasisVec (𝒪 := 𝒪) K j) i = r * (Pi.single j 1 : Fin 2 → 𝒪) i := by
  apply coordEquiv_eq_of
  show r • ((Pi.single j (1 : K) : Fin 2 → K) i) = algebraMap 𝒪 K (r * (Pi.single j (1 : 𝒪) : Fin 2 → 𝒪) i)
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same, mul_one, Algebra.smul_def, mul_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero, mul_zero, map_zero]

theorem coord_tmul_smul_stdBasisVec (i j : Fin 2) (b : B) (r : 𝒪) :
    coord B i (b ⊗ₜ[𝒪] (r • stdBasisVec (𝒪 := 𝒪) K j)) = if i = j then b * algebraMap 𝒪 B r else 0 := by
  rw [coord_tmul, coordEquiv_smul_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

theorem eq_sum_coord (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    x = coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) + coord B 1 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
  have h := (tensorBasis B).sum_repr x
  rw [Fin.sum_univ_two, tensorBasis_apply, tensorBasis_apply] at h
  exact h.symm

variable {B}

def D0 (ξ : B) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := coord B 0 - ξ • coord B 1

def D1 (η : B) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := coord B 1 - η • coord B 0

theorem D0_apply (ξ : B) (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    D0 ξ x = coord B 0 x - ξ * coord B 1 x := rfl

theorem D1_apply (η : B) (x : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :
    D1 η x = coord B 1 x - η * coord B 0 x := rfl

abbrev N0 (ξ : B) : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Submodule.span B {ξ ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}

abbrev N1' (η : B) : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + η ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}

theorem N0_eq_ker (ξ : B) : N0 (𝒪 := 𝒪) (K := K) ξ = LinearMap.ker (D0 (𝒪 := 𝒪) (K := K) ξ) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, D0_apply]
    simp [map_add, coord_tmul_stdBasisVec]
  · intro x hx
    rw [LinearMap.mem_ker, D0_apply, sub_eq_zero] at hx
    rw [eq_sum_coord B x, hx]
    have : (ξ * coord B 1 x) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) + coord B 1 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1)
        = coord B 1 x • (ξ ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
      simp only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm ξ]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem N1'_eq_ker (η : B) : N1' (𝒪 := 𝒪) (K := K) η = LinearMap.ker (D1 (𝒪 := 𝒪) (K := K) η) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, D1_apply]
    simp [map_add, coord_tmul_stdBasisVec]
  · intro x hx
    rw [LinearMap.mem_ker, D1_apply, sub_eq_zero] at hx
    rw [eq_sum_coord B x, hx]
    have : coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) + (η * coord B 0 x) • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1)
        = coord B 0 x • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + η ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
      simp only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm η]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Coord
end EDB

namespace EDB
section Lines
variable (𝒪 : Type) [CommRing 𝒪]
variable (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

theorem fst_eq_of_span_eq {B : Type} [CommRing B] [Algebra 𝒪 B] {a a' : B}
    (h : Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} =
      Submodule.span B {a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}) : a = a' := by
  have hm : a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 ∈ Coord.N0 (𝒪 := 𝒪) (K := K₀) a := by
    show _ ∈ Submodule.span B _
    rw [h]; exact Submodule.mem_span_singleton_self _
  rw [Coord.N0_eq_ker, LinearMap.mem_ker, Coord.D0_apply] at hm
  simp only [map_add, Coord.coord_tmul_stdBasisVec] at hm
  simpa [sub_eq_zero, eq_comm] using hm

theorem snd_eq_of_span_map_eq {B : Type} [CommRing B] [Algebra 𝒪 B] {b b' : B}
    (h : (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}).map
        (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}).map
        (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap) : b = b' := by
  have h' := Submodule.map_injective_of_injective (actBaseChange B g₁ (stdFullLattice K₀)).injective h
  have hm : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 ∈ Coord.N1' (𝒪 := 𝒪) (K := K₀) b := by
    show _ ∈ Submodule.span B _
    rw [h']; exact Submodule.mem_span_singleton_self _
  rw [Coord.N1'_eq_ker, LinearMap.mem_ker, Coord.D1_apply] at hm
  simp only [map_add, Coord.coord_tmul_stdBasisVec] at hm
  simpa [sub_eq_zero, eq_comm] using hm

end Lines

section AdicAct
variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
variable {R : Type} [CommRing R] [Algebra 𝒪 R]

theorem eq_act_inv_pt (x : AdicPoint K₀ π R) (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
    (d : DeligneDatum (K := K₀) π (modPow π R n))
    (hP : DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ d (x.pt n)) :
    d = (x.act h⁻¹).pt n := by
  have e := (isPullback_inv_iff π h d (x.pt n)).1 hP
  show d = tr π h⁻¹ (x.pt n)
  rw [e, ← tr_mul, inv_mul_cancel, tr_one]

end AdicAct
end EDB

namespace EDB
section PointExt
variable {Onr : Type} [CommRing Onr] (π' : Onr) (q n : ℕ) {B : Type} [CommRing B]

theorem ringHom_An_ext {f g : ((chartERing Onr π' q) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr π' q) π') ^ (n + 1)}) →+* B}
    (hc : f.comp (algebraMap Onr _) = g.comp (algebraMap Onr _))
    (hξ : f (Ideal.Quotient.mk _ (chartERing.ξ Onr π' q)) = g (Ideal.Quotient.mk _ (chartERing.ξ Onr π' q)))
    (hη : f (Ideal.Quotient.mk _ (chartERing.η Onr π' q)) = g (Ideal.Quotient.mk _ (chartERing.η Onr π' q))) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (edgeQuot.discr Onr π' q))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    have := congrArg (fun φ => φ c) hc
    simp only [RingHom.comp_apply] at this
    exact this
  · intro i
    fin_cases i
    · exact hξ
    · exact hη

end PointExt
end EDB

namespace EDB
section Compat
variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] (π : 𝒪)
variable {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem rTensor_smul_base (M : FullLattice 𝒪 K₀) (b : B) (v : latticeBaseChange 𝒪 K₀ B M) :
    LinearMap.rTensor (↥M.1) f.toLinearMap (b • v) = f b • LinearMap.rTensor (↥M.1) f.toLinearMap v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => simp [TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem lineBaseChange_span_singleton (M : FullLattice 𝒪 K₀) (v : latticeBaseChange 𝒪 K₀ B M) :
    lineBaseChange (K := K₀) f M (Submodule.span B {v}) = Submodule.span B' {LinearMap.rTensor (↥M.1) f.toLinearMap v} := by
  apply le_antisymm
  · rw [lineBaseChange]
    apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [SetLike.mem_coe, rTensor_smul_base]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [lineBaseChange]
    apply Submodule.span_mono
    exact Set.singleton_subset_iff.2 ⟨v, Submodule.mem_span_singleton_self v, rfl⟩

theorem rTensor_edgeVec0 (a : B) :
    LinearMap.rTensor (↥(stdFullLattice (𝒪 := 𝒪) K₀).1) f.toLinearMap (a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1) =
      f a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 := by
  simp [LinearMap.rTensor_tmul]

theorem rTensor_edgeVec1 (b : B) :
    LinearMap.rTensor (↥(stdFullLattice (𝒪 := 𝒪) K₀).1) f.toLinearMap ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1) =
      (1 : B') ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + f b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1 := by
  simp [LinearMap.rTensor_tmul]

theorem fst_coord_map (d : DeligneDatum (K := K₀) π B) (a : B) (a' : B')
    (h : d.line (stdFullLattice K₀) = Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1})
    (h' : (d.map π f).line (stdFullLattice K₀) = Submodule.span B' {a' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}) :
    f a = a' := by
  have e : (d.map π f).line (stdFullLattice K₀) = Submodule.span B' {f a ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1} := by
    show lineBaseChange (K := K₀) f _ (d.line _) = _
    rw [h, lineBaseChange_span_singleton, rTensor_edgeVec0]
  rw [e] at h'
  exact fst_eq_of_span_eq 𝒪 K₀ h'

end Compat
end EDB

namespace EDB
section Compat2
variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] (π : 𝒪)
variable {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem lineBaseChange_map_actBaseChange (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (M : FullLattice 𝒪 K₀)
    (N : Submodule B (latticeBaseChange 𝒪 K₀ B M)) :
    lineBaseChange (K := K₀) f (FullLattice.act g M) (N.map (actBaseChange B g M).toLinearMap) =
      (lineBaseChange (K := K₀) f M N).map (actBaseChange B' g M).toLinearMap := by
  rw [lineBaseChange, lineBaseChange, Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro x _
  exact rTensor_actBaseChange f g M x

theorem snd_coord_map (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) (b : B) (b' : B')
    (h : d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}).map
        (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap)
    (h' : (d.map π f).line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span B' {(1 : B') ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + b' ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}).map
        (actBaseChange B' g₁ (stdFullLattice K₀)).toLinearMap) :
    f b = b' := by
  have e : (d.map π f).line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span B' {(1 : B') ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 0 + f b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K₀ 1}).map
        (actBaseChange B' g₁ (stdFullLattice K₀)).toLinearMap := by
    show lineBaseChange (K := K₀) f _ (d.line _) = _
    rw [h, lineBaseChange_map_actBaseChange, lineBaseChange_span_singleton, rTensor_edgeVec1]
  rw [e] at h'
  exact snd_eq_of_span_map_eq 𝒪 K₀ g₁ h'

end Compat2
end EDB

namespace EDB
section AdicLift
variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {R : Type} [CommRing R] [Algebra 𝒪 R]

theorem exists_lift_of_compat (hc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (a : ∀ n : ℕ, modPow π R n) (hcompat : ∀ n : ℕ, modPowTransition π R n (a (n + 1)) = a n) :
    ∃ L : R, ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) L = a n := by
  classical
  set I : Ideal R := Ideal.span {algebraMap 𝒪 R π} with hI

  choose b hb using fun n => Ideal.Quotient.mk_surjective (a n)

  have hstep : ∀ n, b (n + 1) - b n ∈ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} := by
    intro n
    rw [← Ideal.Quotient.eq, hb n, ← hcompat n, ← hb (n + 1)]
    rfl
  have hpow : ∀ n, I ^ n = Ideal.span {algebraMap 𝒪 R π ^ n} := fun n => by rw [hI, Ideal.span_singleton_pow]

  have hmn : ∀ m n, m ≤ n → b n - b m ∈ Ideal.span {algebraMap 𝒪 R π ^ (m + 1)} := by
    intro m n hle
    induction hle with
    | refl => simp
    | step hk ih =>
      rename_i k
      have h1 := hstep k
      have h2 : Ideal.span {algebraMap 𝒪 R π ^ (k + 1)} ≤ Ideal.span {algebraMap 𝒪 R π ^ (m + 1)} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.succ_le_succ hk))
      have : b (k + 1) - b m = (b (k + 1) - b k) + (b k - b m) := by ring
      rw [this]
      exact Ideal.add_mem _ (h2 h1) ih

  have hprec : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n hle
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, hpow]
    have := hmn m n hle
    have h2 : Ideal.span {algebraMap 𝒪 R π ^ (m + 1)} ≤ Ideal.span {algebraMap 𝒪 R π ^ m} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ m))
    rw [← neg_sub]
    exact (Ideal.neg_mem_iff _).2 (h2 this)
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' b hprec
  refine ⟨L, fun n => ?_⟩
  rw [← hb n, Ideal.Quotient.eq]
  have h1 := hL (n + 1)
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, hpow] at h1
  have : L - b n = -(b (n + 1) - L) + (b (n + 1) - b n) := by ring
  rw [this]
  exact Ideal.add_mem _ ((Ideal.neg_mem_iff _).2 h1) (hstep n)

end AdicLift
end EDB

namespace EDB
section ChartFamily
variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] (π : 𝒪)
variable {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (r : ℕ)
variable {R : Type} [CommRing R] [Algebra 𝒪 R] (ψ₀ : Onr →ₐ[𝒪] R) (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

def IsChartPt (y : AdicPoint K₀ π R) (n : ℕ)
    (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* modPow π R n) : Prop :=
  xbar.comp (algebraMap Onr _) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom ∧
  (y.pt n).line (stdFullLattice K₀) =
      Submodule.span (modPow π R n) {(xbar (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
  (y.pt n).line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span (modPow π R n) {(1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
        (actBaseChange (modPow π R n) g₁ (stdFullLattice K₀)).toLinearMap

variable {π r ψ₀ g₁}

theorem IsChartPt.fst_compat {y : AdicPoint K₀ π R} {n : ℕ} {xbar₁ xbar₀}
    (h₁ : IsChartPt π r ψ₀ g₁ y (n + 1) xbar₁) (h₀ : IsChartPt π r ψ₀ g₁ y n xbar₀) :
    modPowTransition π R n (xbar₁ (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) =
      xbar₀ (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) := by
  apply fst_coord_map π (modPowTransition π R n) (y.pt (n + 1)) _ _ h₁.2.1
  rw [y.compat n]; exact h₀.2.1

theorem IsChartPt.snd_compat {y : AdicPoint K₀ π R} {n : ℕ} {xbar₁ xbar₀}
    (h₁ : IsChartPt π r ψ₀ g₁ y (n + 1) xbar₁) (h₀ : IsChartPt π r ψ₀ g₁ y n xbar₀) :
    modPowTransition π R n (xbar₁ (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) =
      xbar₀ (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) := by
  apply snd_coord_map π (modPowTransition π R n) g₁ (y.pt (n + 1)) _ _ h₁.2.2
  rw [y.compat n]; exact h₀.2.2

theorem IsChartPt.fst_eq {y : AdicPoint K₀ π R} {n : ℕ} {xbar xbar'}
    (h : IsChartPt π r ψ₀ g₁ y n xbar) (h' : IsChartPt π r ψ₀ g₁ y n xbar') :
    xbar (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) = xbar' (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) :=
  fst_eq_of_span_eq 𝒪 K₀ (h.2.1.symm.trans h'.2.1)

theorem IsChartPt.snd_eq {y : AdicPoint K₀ π R} {n : ℕ} {xbar xbar'}
    (h : IsChartPt π r ψ₀ g₁ y n xbar) (h' : IsChartPt π r ψ₀ g₁ y n xbar') :
    xbar (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) = xbar' (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) :=
  snd_eq_of_span_map_eq 𝒪 K₀ g₁ (h.2.2.symm.trans h'.2.2)

theorem IsChartPt.ext {y : AdicPoint K₀ π R} {n : ℕ} {xbar xbar'}
    (h : IsChartPt π r ψ₀ g₁ y n xbar) (h' : IsChartPt π r ψ₀ g₁ y n xbar') : xbar = xbar' :=
  ringHom_An_ext (algebraMap 𝒪 Onr π) r n (h.1.trans h'.1.symm) (h.fst_eq h') (h.snd_eq h')

theorem exists_coords (hc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R) (y : AdicPoint K₀ π R)
    (hy : ∀ n : ℕ, ∃ xbar, IsChartPt π r ψ₀ g₁ y n xbar) :
    ∃ u w : R, ∀ (n : ℕ) (xbar), IsChartPt π r ψ₀ g₁ y n xbar →
      xbar (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) = Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) u ∧
      xbar (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) = Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) w := by
  choose xb hxb using hy
  obtain ⟨u, hu⟩ := exists_lift_of_compat π hc (fun n => xb n (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)))
    (fun n => (hxb (n + 1)).fst_compat (hxb n))
  obtain ⟨w, hw⟩ := exists_lift_of_compat π hc (fun n => xb n (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r)))
    (fun n => (hxb (n + 1)).snd_compat (hxb n))
  refine ⟨u, w, fun n xbar hx => ⟨?_, ?_⟩⟩
  · rw [hx.fst_eq (hxb n), hu n]
  · rw [hx.snd_eq (hxb n), hw n]

end ChartFamily
end EDB

namespace EDB
section OnrPoint
variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
  {C : Type} [Field C] [Algebra K₀ C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {π : 𝒪} {ϖ : PseudoUniformizer K₀ C} {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C]
  [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
variable {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] {r : ℕ} {ψ₀ : Onr →ₐ[𝒪] R} {g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀}

theorem ringHom_chartERing_ext {Onr : Type} [CommRing Onr] (π' : Onr) (q : ℕ) {B : Type} [CommRing B]
    {f g : chartERing Onr π' q →+* B}
    (hc : f.comp (algebraMap Onr _) = g.comp (algebraMap Onr _))
    (hξ : f (chartERing.ξ Onr π' q) = g (chartERing.ξ Onr π' q))
    (hη : f (chartERing.η Onr π' q) = g (chartERing.η Onr π' q)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (edgeQuot.discr Onr π' q))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    have := congrArg (fun φ => φ c) hc
    simp only [RingHom.comp_apply] at this
    exact this
  · intro i
    fin_cases i
    · exact hξ
    · exact hη

theorem eq_of_forall_mk_eq (hF : IsAdicFrame π ϖ R) {a b : R}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) a = Ideal.Quotient.mk _ b) : a = b := by
  rw [← sub_eq_zero]
  apply hF.complete.toIsHausdorff.haus
  intro n
  rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have : a - b ∈ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} := by rw [← Ideal.Quotient.eq]; exact h n
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n)) this

theorem isUnit_of_isUnit_mk (hF : IsAdicFrame π ϖ R) {a : R} (n : ℕ)
    (h : IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) a)) : IsUnit a := by
  haveI := isLocalRing hF
  obtain ⟨bq, hbq⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
  rw [← map_mul, ← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq] at hbq
  have hmem : a * b - 1 ∈ IsLocalRing.maximalIdeal R := by
    have hle : Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (not_isUnit_algebraMap_pi hF)) _ (Nat.succ_pos n)
    exact hle hbq
  have hu : IsUnit (a * b) := by
    by_contra hnu
    have := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ this hmem; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  exact isUnit_of_mul_isUnit_left hu

theorem exists_chartPoint (hF : IsAdicFrame π ϖ R) (y : AdicPoint K₀ π R)
    (hy : ∀ n : ℕ, ∃ xbar, IsChartPt π r ψ₀ g₁ y n xbar) :
    ∃ xt : chartERing Onr (algebraMap 𝒪 Onr π) r →+* R,
      xt.comp (algebraMap Onr _) = ψ₀.toRingHom ∧
      (∀ (n : ℕ) (xbar), IsChartPt π r ψ₀ g₁ y n xbar →
        xbar.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp xt) ∧
      (∀ n : ℕ, (y.pt n).line (stdFullLattice K₀) =
        Submodule.span (modPow π R n) {(Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (xt (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 1}) := by
  obtain ⟨u, w, huw⟩ := exists_coords hF.complete y hy
  have key : ∀ n, ∃ xbar, IsChartPt π r ψ₀ g₁ y n xbar := hy

  have h1 : u * w = algebraMap 𝒪 R π := by
    apply eq_of_forall_mk_eq hF
    intro n
    obtain ⟨xb, hxb⟩ := key n
    obtain ⟨hu, hw⟩ := huw n xb hxb
    have hc := congrArg (fun φ => φ (algebraMap 𝒪 Onr π)) hxb.1
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] at hc
    rw [map_mul, ← hu, ← hw, ← map_mul, ← map_mul, chartERing.ξ_mul_η, ← hc, ← Ideal.Quotient.mk_comp_algebraMap,
      RingHom.comp_apply]

  obtain ⟨xb0, hxb0⟩ := key 0
  obtain ⟨hu0, hw0⟩ := huw 0 xb0 hxb0
  have hdisc : IsUnit ((u ^ (r - 1) - 1) * (w ^ (r - 1) - 1)) := by
    apply isUnit_of_isUnit_mk hF 0
    have := (chartERing.isUnit_discr Onr (algebraMap 𝒪 Onr π) r).map (xb0.comp (Ideal.Quotient.mk _))
    simp only [RingHom.comp_apply, map_mul, map_sub, map_pow, map_one] at this
    rw [hu0, hw0] at this
    simpa only [map_mul, map_sub, map_pow, map_one] using this
  letI : Algebra Onr R := ψ₀.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap Onr R c = ψ₀ c := fun c => rfl
  have hπR : algebraMap Onr R (algebraMap 𝒪 Onr π) = algebraMap 𝒪 R π := by rw [halg, AlgHom.commutes]
  let pt : (chartE Onr (algebraMap 𝒪 Onr π) r).obj R :=
    ⟨(u, w), by rw [hπR]; exact h1, isUnit_of_mul_isUnit_left hdisc, isUnit_of_mul_isUnit_right hdisc⟩
  have hξ : chartERing.lift pt (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r) = u := chartERing.lift_ξ pt
  have hη : chartERing.lift pt (chartERing.η Onr (algebraMap 𝒪 Onr π) r) = w := chartERing.lift_η pt
  refine ⟨(chartERing.lift pt).toRingHom, ?_, ?_, ?_⟩
  · ext c
    show chartERing.lift pt (algebraMap Onr _ c) = ψ₀ c
    rw [AlgHom.commutes, halg]
  · intro n xbar hx
    obtain ⟨hu', hw'⟩ := huw n xbar hx
    apply ringHom_chartERing_ext (algebraMap 𝒪 Onr π) r
    · rw [RingHom.comp_assoc, Ideal.Quotient.mk_comp_algebraMap, hx.1, RingHom.comp_assoc]
      congr 1
      ext c
      show ψ₀ c = chartERing.lift pt (algebraMap Onr _ c)
      rw [AlgHom.commutes, halg]
    · show xbar (Ideal.Quotient.mk _ _) = Ideal.Quotient.mk _ (chartERing.lift pt _)
      rw [hu', hξ]
    · show xbar (Ideal.Quotient.mk _ _) = Ideal.Quotient.mk _ (chartERing.lift pt _)
      rw [hw', hη]
  · intro n
    obtain ⟨xb, hxb⟩ := key n
    rw [hxb.2.1, (huw n xb hxb).1]
    show _ = Submodule.span _ {(Ideal.Quotient.mk _ (chartERing.lift pt _)) ⊗ₜ[𝒪] _ + _}
    rw [hξ]

end OnrPoint
end EDB

namespace EDB
section Factor
variable {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
  (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
  (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
  {R : Type} [CommRing R] [Algebra 𝒪 R] (ψ₀ : Onr →ₐ[𝒪] R)
  (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)
  (sn : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
  (κ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Limits.pullback f (sn n))
  (hκ : (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          (Θ B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)).1 =
            Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ h n ≫ Limits.pullback.fst f (sn n)))

include hκ in

theorem spec_comp_eq_spec_xbar_comp_chart (x : AdicPoint K₀ π R) (n : ℕ) (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (Px : Spec (CommRingCat.of R) ⟶ 𝒳)
    (hΦ1 : Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ Px =
          (Θ (modPow π R n) (isNilpotent_algebraMap_modPow π R n)
            (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)).1)
    (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* modPow π R n)
    (hc : xbar.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom)
    (d : DeligneDatum (K := K₀) π (modPow π R n))
    (hd : d.line (stdFullLattice K₀) =
            Submodule.span (modPow π R n) {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span (modPow π R n) {(1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange (modPow π R n) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))
    (hP : DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ d (x.pt n)) :
    Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ Px =
      Spec.map (CommRingCat.ofHom xbar) ≫ κ h n ≫ Limits.pullback.fst f (sn n) := by
  rw [hΦ1]
  letI alg : Algebra Onr (modPow π R n) := ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom).toAlgebra
  have halg : ∀ c, algebraMap Onr (modPow π R n) c = Ideal.Quotient.mk _ (ψ₀ c) := fun c => rfl
  haveI : IsScalarTower 𝒪 Onr (modPow π R n) := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [halg, AlgHom.commutes]; rfl)
  let xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] modPow π R n :=
    { toRingHom := xbar
      commutes' := fun c => by
        have := congrArg (fun φ => φ c) hc
        simp only [RingHom.comp_apply] at this
        exact this }
  have key := hκ h n (modPow π R n) (isNilpotent_algebraMap_modPow π R n) xbar' d (x.pt n) hd hP
  have e : (IsScalarTower.toAlgHom 𝒪 Onr (modPow π R n)) = (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀ := by
    apply AlgHom.ext; intro c; rfl
  rw [e] at key
  exact key

end Factor
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

namespace PieceCover

theorem algebraMap_pi_ne_zero {r : ℕ} [Fact r.Prime] {𝒪 Onr : Type} [CommRing 𝒪] [CommRing Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) : algebraMap 𝒪 Onr π ≠ 0 := by
  intro h
  have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
  have : ((r : ℕ) : Onr) = 0 := by
    rw [← map_natCast (algebraMap 𝒪 Onr), ← hc, map_mul, h, mul_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : r.Prime).ne_zero) this

theorem exists_finset_basicOpen_cover {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (U : Set (PrimeSpectrum (A ⧸ I))) (hU : IsOpen U) :
    ∃ T : Finset A, (∀ t ∈ T, (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I t) : Set (PrimeSpectrum (A ⧸ I))) ⊆ U) ∧
      ∀ P ∈ U, ∃ t ∈ T, P ∈ PrimeSpectrum.basicOpen (Ideal.Quotient.mk I t) := by
  classical
  have hc : IsCompact U := TopologicalSpace.NoetherianSpace.isCompact U
  obtain ⟨s, hs⟩ := PrimeSpectrum.isCompact_isOpen_iff.1 ⟨hc, hU⟩
  refine ⟨s.image (fun a => (Ideal.Quotient.mk_surjective a).choose), ?_, ?_⟩
  · intro t ht P hP
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
    have e : Ideal.Quotient.mk I (Ideal.Quotient.mk_surjective a).choose = a := (Ideal.Quotient.mk_surjective a).choose_spec
    rw [e] at hP
    rw [← hs]
    intro hzero
    exact hP (hzero ha)
  · intro P hP
    rw [← hs] at hP
    obtain ⟨a, ha, haP⟩ := Set.not_subset.1 hP
    refine ⟨_, Finset.mem_image_of_mem _ ha, ?_⟩
    show Ideal.Quotient.mk I _ ∉ P.asIdeal
    rw [(Ideal.Quotient.mk_surjective a).choose_spec]
    exact haP

section Chart
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] {π : 𝒪}
  {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]

theorem inEdgeChart_act_inv_pt (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R) (hunifK : ϖ.ϖ = algebraMap 𝒪 K₀ π)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (x : AdicPoint K₀ π R)
    (hz : x.toOmega C ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ))) (n : ℕ) :
    ((x.act h⁻¹).pt n).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) := by
  have hg : g₁ = edgeFlip K₀ ϖ := Units.ext (by rw [hg₁, edgeFlip, diagFst_coe, Units.val_mk0, hunifK])
  rw [AdicPoint.inEdgeChart_pt_iff_inEdgeChart_pt_zero, hg]
  have h0 := (AdicPoint.inEdgeChart_iff_toOmega_mem ϖ hF h x).2 hz
  have e1 : FullLattice.act h⁻¹ (FullLattice.act (h * edgeFlip K₀ ϖ) (stdFullLattice K₀)) =
      FullLattice.act (edgeFlip K₀ ϖ) (stdFullLattice (𝒪 := 𝒪) K₀) :=
    Subtype.ext (by
      show latticeMap h⁻¹ (latticeMap (h * edgeFlip K₀ ϖ) (stdFullLattice (𝒪 := 𝒪) K₀).1) = latticeMap (edgeFlip K₀ ϖ) _
      rw [← latticeMap_mul, ← mul_assoc, inv_mul_cancel, one_mul])
  have e2 : FullLattice.act h⁻¹ (FullLattice.act h (stdFullLattice (𝒪 := 𝒪) K₀)) = stdFullLattice K₀ :=
    Subtype.ext (latticeMap_inv_latticeMap h _)
  have e3 : (x.act h⁻¹).pt 0 = DeligneDatum.pullback π (modPow π R 0) h (x.pt 0) := by
    rw [AdicPoint.act_pt]
    show DeligneDatum.pullback π (modPow π R 0) (h⁻¹)⁻¹ (x.pt 0) = _
    rw [inv_inv]
  intro 𝔭 h𝔭
  have key := DeligneDatum.edgeNondegAt_pullback_act_inv π (x.pt 0) h 𝔭 _ _ (h0 𝔭 h𝔭)
  rw [e1, e2] at key
  rw [e3]
  exact key

end Chart

section OnrLift
variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] {R : Type} [CommRing R] [Algebra 𝒪 R]

theorem exists_ringHom_level_of_algHom (π : 𝒪) (r : ℕ) (ψ₀ : Onr →ₐ[𝒪] R) (n : ℕ)
    (x₀ : chartERing 𝒪 π r →ₐ[𝒪] modPow π R n) :
    ∃ xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* modPow π R n,
      xbar.comp (algebraMap Onr _) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom ∧
      xbar (Ideal.Quotient.mk _ (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) = x₀ (chartERing.ξ 𝒪 π r) ∧
      xbar (Ideal.Quotient.mk _ (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) = x₀ (chartERing.η 𝒪 π r) := by
  letI alg : Algebra Onr (modPow π R n) := ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom).toAlgebra
  have halg : ∀ c, algebraMap Onr (modPow π R n) c = Ideal.Quotient.mk _ (ψ₀ c) := fun c => rfl
  have hπ' : algebraMap Onr (modPow π R n) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 (modPow π R n) π := by
    rw [halg, AlgHom.commutes]; rfl
  have h1 : x₀ (chartERing.ξ 𝒪 π r) * x₀ (chartERing.η 𝒪 π r) = algebraMap Onr (modPow π R n) (algebraMap 𝒪 Onr π) := by
    rw [hπ', ← map_mul, chartERing.ξ_mul_η, AlgHom.commutes]
  have hdisc : IsUnit ((x₀ (chartERing.ξ 𝒪 π r) ^ (r - 1) - 1) * (x₀ (chartERing.η 𝒪 π r) ^ (r - 1) - 1)) := by
    have := (chartERing.isUnit_discr 𝒪 π r).map x₀
    simpa only [map_mul, map_sub, map_pow, map_one] using this
  let pt : (chartE Onr (algebraMap 𝒪 Onr π) r).obj (modPow π R n) :=
    ⟨(x₀ (chartERing.ξ 𝒪 π r), x₀ (chartERing.η 𝒪 π r)), h1, isUnit_of_mul_isUnit_left hdisc, isUnit_of_mul_isUnit_right hdisc⟩
  have hLπ : (chartERing.lift pt).toRingHom
      ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)) = 0 := by
    rw [map_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, hπ', ← map_pow,
      IsScalarTower.algebraMap_apply 𝒪 R (modPow π R n), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact Ideal.mem_span_singleton_self _
  refine ⟨Ideal.Quotient.lift _ (chartERing.lift pt).toRingHom (fun a ha => ?_), ?_, ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hLπ, mul_zero]
  · ext c
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) _ c,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, halg]
    rfl
  · rw [Ideal.Quotient.lift_mk, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, chartERing.lift_ξ]
  · rw [Ideal.Quotient.lift_mk, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, chartERing.lift_η]

end OnrLift

end PieceCover

open EDB PieceCover in
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

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
        (sn : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
        (hsn : ∀ n : ℕ, sn n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))
    (κ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Limits.pullback f (sn n))
    (hκ : (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          (Θ B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)).1 =
            Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ h n ≫ Limits.pullback.fst f (sn n)))
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (V : 𝒳.Opens) :
    ∃ T : Finset (chartERing Onr (algebraMap 𝒪 Onr π) r),
      (∀ t ∈ T, ∀ n : ℕ, PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) t) ≤
          (κ h n) ⁻¹ᵁ ((Limits.pullback.fst f (sn n)) ⁻¹ᵁ V)) ∧
      ∀ (x : AdicPoint K₀ π R) (z : C), z = x.toOmega C →
        z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ))) →
        (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((Φ x).1) ⁻¹ᵁ V →
        ∃ t ∈ T, (z ∈ Omega.upperHalfPlane K₀ C ∧ ∀ x : AdicPoint K₀ π R, x.toOmega C = z → ∀ n : ℕ,
      ∃ (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* (modPow π R n)) (d : DeligneDatum (K := K₀) π (modPow π R n)),
        xbar.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom ∧
        (d.line (stdFullLattice K₀) =
            Submodule.span (modPow π R n) {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : (modPow π R n)) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span (modPow π R n) {(1 : (modPow π R n)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange (modPow π R n) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) ∧
        DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ d (x.pt n) ∧
        IsUnit (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) t))) := by

  classical
  haveI hdvrI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  have hunifK : ϖ.ϖ = algebraMap 𝒪 K₀ π := by
    apply (algebraMap K₀ C).injective
    rw [← hF.unif, IsScalarTower.algebraMap_apply 𝒪 K₀ C]

  have hπ'0 : algebraMap 𝒪 Onr π ≠ 0 := algebraMap_pi_ne_zero π hunr
  haveI : IsDiscreteValuationRing Onr :=
    IsDiscreteValuationRing.of_isAdicComplete_span_singleton_of_isMaximal Onr (algebraMap 𝒪 Onr π) hπ'0 hOnr_complete hOnr_max
  haveI : IsNoetherianRing (edgeQuot Onr (algebraMap 𝒪 Onr π)) := by unfold edgeQuot; infer_instance
  haveI hNA : IsNoetherianRing (chartERing Onr (algebraMap 𝒪 Onr π) r) := by unfold chartERing; infer_instance

  obtain ⟨T, hT₀, hTcov⟩ := exists_finset_basicOpen_cover
    (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (0 + 1)})
    (SetLike.coe ((κ h 0) ⁻¹ᵁ ((Limits.pullback.fst f (sn 0)) ⁻¹ᵁ V))) ((κ h 0) ⁻¹ᵁ ((Limits.pullback.fst f (sn 0)) ⁻¹ᵁ V)).isOpen
  refine ⟨T, fun t ht n => ?_, ?_⟩
  ·
    apply CerednikDrinfeld.basicOpen_le_preimage_chartMorphism_of_level_zero_of_cerednikDrinfeld_quotient
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ'
      ρ hρ hdisc hcocpt 𝒳 f Θ hΘnat hΘinv hΘfib hΘuniv g₁ hg₁ sn hsn κ hκ V h t ?_ n
    intro P hP
    exact hT₀ t ht hP

  intro x z hz hzE hxV
  have hzE' : x.toOmega C ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
      Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ)) := by rw [← hz]; exact hzE

  have hIEC : ∀ n : ℕ, ((x.act h⁻¹).pt n).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) :=
    fun n => inEdgeChart_act_inv_pt ϖ hF hunifK g₁ hg₁ h x hzE' n
  have hy : ∀ n : ℕ, ∃ xbar, EDB.IsChartPt π r ψ₀ g₁ (x.act h⁻¹) n xbar := by
    intro n
    obtain ⟨x₀, hx₀⟩ := DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite π hπ r hres g₁ hg₁
      (modPow π R n) (isNilpotent_algebraMap_modPow π R n) ((x.act h⁻¹).pt n) (hIEC n)
    obtain ⟨xbar, hc, hξ, hη⟩ := exists_ringHom_level_of_algHom π r ψ₀ n x₀
    exact ⟨xbar, hc, by rw [hξ]; exact hx₀.1, by rw [hη]; exact hx₀.2⟩
  choose xb hxb using hy
  obtain ⟨xt, -, hxt₂, -⟩ := EDB.exists_chartPoint hF (x.act h⁻¹) (fun n => ⟨xb n, hxb n⟩)

  have hPull : ∀ n : ℕ, DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ ((x.act h⁻¹).pt n) (x.pt n) := by
    intro n
    rw [EDB.isPullback_inv_iff]
    show x.pt n = ((x.act h⁻¹).act h).pt n
    rw [← AdicPoint.act_mul, mul_inv_cancel, AdicPoint.act_one]

  have hfac := EDB.spec_comp_eq_spec_xbar_comp_chart 𝒪 π K₀ Onr 𝒳 f Θ ψ₀ g₁ sn κ hκ x 0 h (Φ x).1 (hΦ.1 x 0)
    (xb 0) (hxb 0).1 ((x.act h⁻¹).pt 0) ⟨(hxb 0).2.1, (hxb 0).2.2, hIEC 0⟩ (hPull 0)
  haveI := EDB.isLocalRing hF
  have hI0m : Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)} ≤ IsLocalRing.maximalIdeal R := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    apply EDB.not_isUnit_algebraMap_pi hF
    rw [Ideal.span_singleton_eq_top, zero_add, pow_one] at htop
    exact htop
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})) ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.mk_ker]; exact hI0m
  haveI hp : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)}))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  let q₀ : PrimeSpectrum (modPow π R 0) :=
    ⟨(IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})), hp⟩
  have h1 : (⊤ : (Spec (CommRingCat.of (modPow π R 0))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R 0))) ≫ (Φ x).1) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage]
    intro p _
    exact hxV trivial
  rw [hfac] at h1
  simp only [Scheme.Hom.comp_preimage] at h1
  have hP₀ := h1 (show q₀ ∈ (⊤ : (Spec (CommRingCat.of (modPow π R 0))).Opens) from trivial)
  obtain ⟨t, htT, htP⟩ := hTcov _ hP₀

  have hu0 : IsUnit ((xb 0) (Ideal.Quotient.mk _ t)) := by
    have hnot : (xb 0) (Ideal.Quotient.mk _ t) ∉
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})) := by
      have e := htP
      rw [Spec.map_base] at e
      exact e
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((xb 0) (Ideal.Quotient.mk _ t))
    rw [← hb] at hnot ⊢
    have hbu : IsUnit b := by
      by_contra hb'
      exact hnot (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hb'))
    exact hbu.map _

  have hut : IsUnit (xt t) := by
    apply EDB.isUnit_of_isUnit_mk hF 0
    have e := congrArg (fun φ => φ t) (hxt₂ 0 (xb 0) (hxb 0))
    simp only [RingHom.comp_apply] at e
    rw [← e]
    exact hu0
  refine ⟨t, htT, ⟨by rw [hz]; exact AdicPoint.toOmega_mem_upperHalfPlane ϖ hF x, fun x' hx' n => ?_⟩⟩
  have ex : x' = x := AdicPoint.toOmega_injective ϖ hF (hx'.trans hz)
  rw [ex]
  refine ⟨xb n, (x.act h⁻¹).pt n, (hxb n).1, ⟨(hxb n).2.1, (hxb n).2.2, hIEC n⟩, hPull n, ?_⟩
  have e := congrArg (fun φ => φ t) (hxt₂ n (xb n) (hxb n))
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact hut.map _

end

end S_CerednikDrinfeld_exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient (solution)
