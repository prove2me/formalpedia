-- Prove2me | solution 1 for CerednikDrinfeld.exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d9fe41bd-3aa3-552d-ad93-5423986a4405

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_injective
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_Omega_exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient

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

section L5

variable {Onr R C : Type} [CommRing Onr] [CommRing R] [Field C] [Algebra Onr R] [Algebra R C]
  (π' : Onr) (q : ℕ)

def L5RatRep (a : chartERing Onr π' q) : Prop :=
  ∃ ρ : Omega.RatPair C, ∀ x : chartERing Onr π' q →ₐ[Onr] R,
    ρ.den.eval (algebraMap R C (x (chartERing.ξ Onr π' q))) ≠ 0 ∧
    ρ.evalAt (algebraMap R C (x (chartERing.ξ Onr π' q))) = algebraMap R C (x a)

variable {π' q}

theorem L5RatRep.of_const (a : chartERing Onr π' q) (c : C)
    (h : ∀ x : chartERing Onr π' q →ₐ[Onr] R, algebraMap R C (x a) = c) : L5RatRep (R := R) (C := C) π' q a := by
  refine ⟨Omega.RatPair.const c, fun x => ⟨?_, ?_⟩⟩
  · show (1 : Polynomial C).eval _ ≠ 0
    rw [Polynomial.eval_one]; exact one_ne_zero
  · rw [Omega.RatPair.evalAt_const, h x]

theorem L5RatRep.of_algebraMap (r : Onr) :
    L5RatRep (R := R) (C := C) π' q (algebraMap Onr (chartERing Onr π' q) r) :=
  L5RatRep.of_const _ (algebraMap R C (algebraMap Onr R r)) fun x => by rw [AlgHom.commutes]

theorem L5RatRep.add {a b : chartERing Onr π' q} (ha : L5RatRep (R := R) (C := C) π' q a)
    (hb : L5RatRep (R := R) (C := C) π' q b) : L5RatRep (R := R) (C := C) π' q (a + b) := by
  obtain ⟨ρ, hρ⟩ := ha
  obtain ⟨σ, hσ⟩ := hb
  refine ⟨ρ.add σ, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hρ x
  obtain ⟨h3, h4⟩ := hσ x
  refine ⟨?_, ?_⟩
  · show (ρ.den * σ.den).eval _ ≠ 0
    rw [Polynomial.eval_mul]; exact mul_ne_zero h1 h3
  · rw [Omega.RatPair.evalAt_add h1 h3, h2, h4, map_add, map_add]

theorem L5RatRep.mul {a b : chartERing Onr π' q} (ha : L5RatRep (R := R) (C := C) π' q a)
    (hb : L5RatRep (R := R) (C := C) π' q b) : L5RatRep (R := R) (C := C) π' q (a * b) := by
  obtain ⟨ρ, hρ⟩ := ha
  obtain ⟨σ, hσ⟩ := hb
  refine ⟨ρ.mul σ, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hρ x
  obtain ⟨h3, h4⟩ := hσ x
  refine ⟨?_, ?_⟩
  · show (ρ.den * σ.den).eval _ ≠ 0
    rw [Polynomial.eval_mul]; exact mul_ne_zero h1 h3
  · rw [Omega.RatPair.evalAt_mul, h2, h4, map_mul, map_mul]

theorem L5RatRep.of_mul_eq_one {a b : chartERing Onr π' q} (hab : a * b = 1)
    (ha : L5RatRep (R := R) (C := C) π' q a) : L5RatRep (R := R) (C := C) π' q b := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨⟨ρ.den, ρ.num⟩, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hρ x
  set u : C := algebraMap R C (x (chartERing.ξ Onr π' q)) with hu
  have habC : algebraMap R C (x a) * algebraMap R C (x b) = 1 := by
    rw [← map_mul, ← map_mul, hab, map_one, map_one]
  have hne : algebraMap R C (x a) ≠ 0 := left_ne_zero_of_mul_eq_one habC
  have h2' : ρ.num.eval u / ρ.den.eval u = algebraMap R C (x a) := h2
  have hnum : ρ.num.eval u ≠ 0 := by
    intro h0
    rw [h0, zero_div] at h2'
    exact hne h2'.symm
  refine ⟨hnum, ?_⟩
  show ρ.den.eval u / ρ.num.eval u = _
  rw [← inv_div, h2', (mul_eq_one_iff_inv_eq₀ hne).mp habC]

theorem L5RatRep.ξ : L5RatRep (R := R) (C := C) π' q (chartERing.ξ Onr π' q) := by
  refine ⟨⟨Polynomial.X, 1⟩, fun x => ⟨?_, ?_⟩⟩
  · show (1 : Polynomial C).eval _ ≠ 0
    rw [Polynomial.eval_one]; exact one_ne_zero
  · show (Polynomial.X : Polynomial C).eval _ / (1 : Polynomial C).eval _ = _
    rw [Polynomial.eval_X, Polynomial.eval_one, div_one]

theorem L5RatRep.η (hπ : algebraMap R C (algebraMap Onr R π') ≠ 0) :
    L5RatRep (R := R) (C := C) π' q (chartERing.η Onr π' q) := by
  refine ⟨⟨Polynomial.C (algebraMap R C (algebraMap Onr R π')), Polynomial.X⟩, fun x => ?_⟩
  set u : C := algebraMap R C (x (chartERing.ξ Onr π' q)) with hu
  set v : C := algebraMap R C (x (chartERing.η Onr π' q)) with hv
  have key : u * v = algebraMap R C (algebraMap Onr R π') := by
    rw [hu, hv, ← map_mul, ← map_mul, chartERing.ξ_mul_η, AlgHom.commutes]
  have hu0 : u ≠ 0 := by
    intro h0
    apply hπ
    rw [← key, h0, zero_mul]
  refine ⟨?_, ?_⟩
  · show (Polynomial.X : Polynomial C).eval u ≠ 0
    rwa [Polynomial.eval_X]
  · show (Polynomial.C _ : Polynomial C).eval u / (Polynomial.X : Polynomial C).eval u = v
    rw [Polynomial.eval_C, Polynomial.eval_X, eq_comm, eq_div_iff hu0, mul_comm, key]

theorem L5RatRep.ofPoly (hπ : algebraMap R C (algebraMap Onr R π') ≠ 0)
    (p : MvPolynomial (Fin 2) Onr) : L5RatRep (R := R) (C := C) π' q (chartERing.ofPoly Onr π' q p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.algHom_C]
    exact L5RatRep.of_algebraMap r
  | add p p' hp hp' =>
    rw [map_add]
    exact hp.add hp'
  | mul_X p i hp =>
    rw [map_mul]
    refine hp.mul ?_
    fin_cases i
    · exact L5RatRep.ξ
    · exact L5RatRep.η hπ

end L5

theorem exists_ratPair_evalAt_eq_chartERing
    {Onr R C : Type} [CommRing Onr] [CommRing R] [Field C] [Algebra Onr R] [Algebra R C]
    (π' : Onr) (q : ℕ) (hπ : algebraMap R C (algebraMap Onr R π') ≠ 0)
    (a : chartERing Onr π' q) :
    ∃ ρ : Omega.RatPair C, ∀ x : chartERing Onr π' q →ₐ[Onr] R,
      ρ.den.eval (algebraMap R C (x (chartERing.ξ Onr π' q))) ≠ 0 ∧
      ρ.evalAt (algebraMap R C (x (chartERing.ξ Onr π' q))) = algebraMap R C (x a) := by

  obtain ⟨⟨z, s⟩, hzs⟩ := IsLocalization.surj (Submonoid.powers (edgeQuot.discr Onr π' q)) a
  obtain ⟨n, hn⟩ := s.2
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {edgeRel Onr π'}) z
  have hof : ∀ p' : MvPolynomial (Fin 2) Onr, chartERing.ofPoly Onr π' q p' =
      algebraMap (edgeQuot Onr π') (chartERing Onr π' q) (Ideal.Quotient.mk (Ideal.span {edgeRel Onr π'}) p') :=
    fun _ => rfl
  have hZ : algebraMap (edgeQuot Onr π') (chartERing Onr π' q) z = chartERing.ofPoly Onr π' q p := by
    rw [hof, hp]
  have hD : algebraMap (edgeQuot Onr π') (chartERing Onr π' q) (s : edgeQuot Onr π') =
      chartERing.ofPoly Onr π' q (edgeDiscr Onr q ^ n) := by
    rw [map_pow, hof, ← hn, map_pow]; rfl
  simp only at hzs
  rw [hZ, hD] at hzs

  have hunit : IsUnit (chartERing.ofPoly Onr π' q (edgeDiscr Onr q ^ n)) := by
    rw [map_pow, chartERing.ofPoly_edgeDiscr]
    exact (chartERing.isUnit_discr Onr π' q).pow n
  obtain ⟨dinv, hdinv⟩ := hunit.exists_right_inv
  have ha : a = chartERing.ofPoly Onr π' q p * dinv := by
    rw [← hzs, mul_assoc, hdinv, mul_one]
  rw [ha]
  exact (L5RatRep.ofPoly hπ p).mul (L5RatRep.of_mul_eq_one hdinv (L5RatRep.ofPoly hπ _))

end EDB

namespace EDB
section L2c

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
  {C : Type} [Field C] [Algebra K₀ C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {π : 𝒪} {ϖ : PseudoUniformizer K₀ C} {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C]
  [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]

omit C Γ₀ ϖ in

theorem coord_coordToTensor (n : ℕ) (w : Fin 2 → R) (i : Fin 2) :
    Coord.coord (modPow π R n) i (coordToTensor K₀ π R n w) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (w i) := by
  rw [coordToTensor, Fin.sum_univ_two, map_add, Coord.coord_tmul_stdBasisVec, Coord.coord_tmul_stdBasisVec]
  fin_cases i <;> simp

theorem mem_stdLine_iff_of_forall_line_eq (hF : IsAdicFrame π ϖ R) (y : AdicPoint K₀ π R) (u : R)
    (h : ∀ n : ℕ, (y.pt n).line (stdFullLattice K₀) = Submodule.span (modPow π R n)
      {(Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) u) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
        (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 1})
    (w : Fin 2 → R) : w ∈ y.stdLine ↔ w 0 = u * w 1 := by
  rw [AdicPoint.mem_stdLine_iff]
  constructor
  · intro hw
    have hmod : ∀ n : ℕ, w 0 - u * w 1 ∈ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} := by
      intro n
      have hn := hw n
      rw [h n] at hn
      have hn' := (Coord.N0_eq_ker (𝒪 := 𝒪) (K := K₀)
        (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) u)).le hn
      rw [LinearMap.mem_ker, Coord.D0_apply, coord_coordToTensor, coord_coordToTensor,
        ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hn'
      exact hn'
    have h0 : w 0 - u * w 1 = 0 := by
      refine IsHausdorff.haus hF.complete.toIsHausdorff (w 0 - u * w 1) fun n => ?_
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      cases n with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      | succ n => rw [Ideal.span_singleton_pow]; exact hmod n
    exact sub_eq_zero.mp h0
  · intro hw n
    rw [h n]
    have : coordToTensor K₀ π R n w = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (w 1)) •
        ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) u) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
          (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 1) := by
      rw [coordToTensor, Fin.sum_univ_two, hw, map_mul, smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem apply_zero_eq_of_mem_lineC (hF : IsAdicFrame π ϖ R) (y : AdicPoint K₀ π R) (u : R)
    (h : ∀ n : ℕ, (y.pt n).line (stdFullLattice K₀) = Submodule.span (modPow π R n)
      {(Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) u) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
        (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 1})
    {v : Fin 2 → C} (hv : v ∈ y.lineC C) : v 0 = algebraMap R C u * v 1 := by
  suffices hker : y.lineC C ≤
      LinearMap.ker (LinearMap.proj 0 - algebraMap R C u • LinearMap.proj 1 : (Fin 2 → C) →ₗ[C] C) by
    have := hker hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply, LinearMap.proj_apply,
      sub_eq_zero, smul_eq_mul] at this
    exact this
  rw [AdicPoint.lineC, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.proj_apply, sub_eq_zero, smul_eq_mul]
  show algebraMap R C (w 0) = algebraMap R C u * algebraMap R C (w 1)
  rw [(mem_stdLine_iff_of_forall_line_eq hF y u h w).mp hw, map_mul]

theorem toOmega_eq_of_forall_line_eq (hF : IsAdicFrame π ϖ R) (y : AdicPoint K₀ π R) (u : R)
    (h : ∀ n : ℕ, (y.pt n).line (stdFullLattice K₀) = Submodule.span (modPow π R n)
      {(Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) u) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
        (1 : modPow π R n) ⊗ₜ[𝒪] stdBasisVec K₀ 1}) :
    y.toOmega C = algebraMap R C u := by
  have hmem : (![algebraMap R C u, 1] : Fin 2 → C) ∈ y.lineC C := by
    refine Submodule.subset_span ⟨![u, 1], ?_, ?_⟩
    · exact (mem_stdLine_iff_of_forall_line_eq hF y u h _).mpr (by simp)
    · funext i
      fin_cases i <;> simp
  have huniq : ∀ z : C, (![z, 1] : Fin 2 → C) ∈ y.lineC C → z = algebraMap R C u := by
    intro z hz
    have := apply_zero_eq_of_mem_lineC hF y u h hz
    simpa using this
  have hex : ∃! z : C, (![z, 1] : Fin 2 → C) ∈ y.lineC C := ⟨_, hmem, huniq⟩
  exact huniq _ (y.vecCons_toOmega_mem C hex)

end L2c
end EDB

namespace PieceShape

section Chart
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] {π : 𝒪}
  {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]

theorem act_inv_act_mul_std (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) :
    FullLattice.act h⁻¹ (FullLattice.act (h * g) (stdFullLattice (𝒪 := 𝒪) K₀)) = FullLattice.act g (stdFullLattice K₀) :=
  Subtype.ext (by
    show latticeMap h⁻¹ (latticeMap (h * g) (stdFullLattice (𝒪 := 𝒪) K₀).1) = latticeMap g _
    rw [← latticeMap_mul, ← mul_assoc, inv_mul_cancel, one_mul])

theorem act_inv_act_std (h : Matrix.GeneralLinearGroup (Fin 2) K₀) :
    FullLattice.act h⁻¹ (FullLattice.act h (stdFullLattice (𝒪 := 𝒪) K₀)) = stdFullLattice K₀ :=
  Subtype.ext (latticeMap_inv_latticeMap h _)

theorem act_inv_pt_zero_eq (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (x : AdicPoint K₀ π R) :
    (x.act h⁻¹).pt 0 = DeligneDatum.pullback π (modPow π R 0) h (x.pt 0) := by
  rw [AdicPoint.act_pt]
  show DeligneDatum.pullback π (modPow π R 0) (h⁻¹)⁻¹ (x.pt 0) = _
  rw [inv_inv]

theorem inEdgeChart_act_inv_pt_zero_iff (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R) (hunifK : ϖ.ϖ = algebraMap 𝒪 K₀ π)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (x : AdicPoint K₀ π R) :
    ((x.act h⁻¹).pt 0).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) ↔
    x.toOmega C ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ)) := by
  have hg : g₁ = edgeFlip K₀ ϖ := Units.ext (by rw [hg₁, edgeFlip, diagFst_coe, Units.val_mk0, hunifK])
  rw [← AdicPoint.inEdgeChart_iff_toOmega_mem ϖ hF h x, hg, act_inv_pt_zero_eq]
  constructor
  · intro hin 𝔭 h𝔭
    have key := DeligneDatum.edgeNondegAt_pullback_act_inv π (DeligneDatum.pullback π (modPow π R 0) h (x.pt 0)) h⁻¹ 𝔭 _ _ (hin 𝔭 h𝔭)
    rw [inv_inv] at key
    have e : DeligneDatum.pullback π (modPow π R 0) h⁻¹ (DeligneDatum.pullback π (modPow π R 0) h (x.pt 0)) = x.pt 0 := by
      show EDB.tr π h (EDB.tr π (h⁻¹) (x.pt 0)) = x.pt 0
      rw [← EDB.tr_mul, mul_inv_cancel, EDB.tr_one]
    have e1 : FullLattice.act h (FullLattice.act (edgeFlip K₀ ϖ) (stdFullLattice (𝒪 := 𝒪) K₀)) =
        FullLattice.act (h * edgeFlip K₀ ϖ) (stdFullLattice K₀) :=
      Subtype.ext (by
        show latticeMap h (latticeMap (edgeFlip K₀ ϖ) (stdFullLattice (𝒪 := 𝒪) K₀).1) = latticeMap (h * edgeFlip K₀ ϖ) _
        rw [latticeMap_mul])
    rw [e, e1] at key
    exact key
  · intro hin 𝔭 h𝔭
    have key := DeligneDatum.edgeNondegAt_pullback_act_inv π (x.pt 0) h 𝔭 _ _ (hin 𝔭 h𝔭)
    rw [act_inv_act_mul_std, act_inv_act_std] at key
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

end PieceShape

open EDB PieceShape in
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
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (t : chartERing Onr (algebraMap 𝒪 Onr π) r)
    (S : Set C)
    (hS : ∀ z : C, z ∈ S ↔ z ∈ Omega.upperHalfPlane K₀ C ∧ ∀ x : AdicPoint K₀ π R, x.toOmega C = z → ∀ n : ℕ,
      ∃ (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* (modPow π R n)) (d : DeligneDatum (K := K₀) π (modPow π R n)),
        xbar.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom ∧
        (d.line (stdFullLattice K₀) =
            Submodule.span (modPow π R n) {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : (modPow π R n)) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span (modPow π R n) {(1 : (modPow π R n)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange (modPow π R n) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) ∧
        DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ d (x.pt n) ∧
        IsUnit (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) t))) :
    ∃ (m : ℕ) (L M : Fin m → Finset (C × C)),
      (∀ k, ∀ er ∈ L k, er.2 ≠ 0) ∧ (∀ k, ∀ er ∈ M k, er.2 ≠ 0) ∧
      (∀ k, {z : C | z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ))) ∧
              (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ z - er.1)) ∧
              (∀ er ∈ M k, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ z - er.1) ≤ Valued.v er.2)} ⊆ S) ∧
      (∀ z ∈ S, ∃ k, z ∈ {z : C | z ∈ (Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
            Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ))) ∧
              (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ z - er.1)) ∧
              (∀ er ∈ M k, Valued.v (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ z - er.1) ≤ Valued.v er.2)}) := by

  classical
  haveI hdvrI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
  have hunifK : ϖ.ϖ = algebraMap 𝒪 K₀ π := by
    apply (algebraMap K₀ C).injective
    rw [← hF.unif, IsScalarTower.algebraMap_apply 𝒪 K₀ C]
  have hπpos := hF.v_algebraMap_pos
  have hπC0 : algebraMap 𝒪 C π ≠ 0 := fun h0 => by rw [h0, map_zero] at hπpos; exact lt_irrefl _ hπpos

  letI algOnrR : Algebra Onr R := ψ₀.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap Onr R c = ψ₀ c := fun c => rfl
  have hπ' : algebraMap R C (algebraMap Onr R (algebraMap 𝒪 Onr π)) ≠ 0 := by
    rw [halg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]; exact hπC0
  have hmk : (Matrix.ProjGenLinGroup.mk h)⁻¹ = Matrix.ProjGenLinGroup.mk h⁻¹ := (map_inv _ h).symm
  have hEΩ : ∀ z : C, z ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ)) → z ∈ Omega.upperHalfPlane K₀ C := fun z hz =>
    hz.elim (fun h' => h'.elim (fun h'' => Omega.vertexTube_subset_upperHalfPlane ϖ _ h'')
      (fun h'' => Omega.edgeTube_subset_upperHalfPlane ϖ _ h'')) (fun h' => Omega.vertexTube_subset_upperHalfPlane ϖ _ h')

  obtain ⟨ρt, hρt⟩ := exists_ratPair_evalAt_eq_chartERing (R := R) (C := C) (algebraMap 𝒪 Onr π) r hπ' t
  obtain ⟨m, L, M, hL, hM, hLM⟩ :=
    CerednikDrinfeld.Omega.exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed C ρt.num ρt.den

  have hPull : ∀ (x : AdicPoint K₀ π R) (n : ℕ),
      DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ ((x.act h⁻¹).pt n) (x.pt n) := fun x n =>
    (isPullback_inv_iff π h _ _).2 (by
      show x.pt n = tr π h (tr π h⁻¹ (x.pt n))
      rw [← tr_mul, mul_inv_cancel, tr_one])

  have key : ∀ z : C, z ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ)) →
      ∃ (x : AdicPoint K₀ π R) (xt : chartERing Onr (algebraMap 𝒪 Onr π) r →+* R)
        (xb : ∀ n : ℕ, ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* modPow π R n),
        x.toOmega C = z ∧
        (∀ n, IsChartPt π r ψ₀ g₁ (x.act h⁻¹) n (xb n)) ∧
        (∀ n, ((x.act h⁻¹).pt n).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) ∧
        (∀ n, (xb n).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp xt) ∧
        ρt.den.eval (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ z) ≠ 0 ∧
        ρt.evalAt (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ z) = algebraMap R C (xt t) := by
    intro z hzE
    obtain ⟨x, -, hx0⟩ := AdicPoint.toOmega_surjOn (C := C) ϖ hF (hEΩ z hzE)
    have hx : x.toOmega C = z := hx0
    have hzE' : x.toOmega C ∈ _ := hx.symm ▸ hzE
    have hIEC : ∀ n : ℕ, ((x.act h⁻¹).pt n).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) := by
      intro n
      rw [AdicPoint.inEdgeChart_pt_iff_inEdgeChart_pt_zero]
      exact (inEdgeChart_act_inv_pt_zero_iff ϖ hF hunifK g₁ hg₁ h x).2 hzE'
    have hy : ∀ n : ℕ, ∃ xbar, IsChartPt π r ψ₀ g₁ (x.act h⁻¹) n xbar := by
      intro n
      obtain ⟨x₀, hx₀⟩ := DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite π hπ r hres g₁ hg₁
        (modPow π R n) (isNilpotent_algebraMap_modPow π R n) ((x.act h⁻¹).pt n) (hIEC n)
      obtain ⟨xbar, hc, hξ, hη⟩ := exists_ringHom_level_of_algHom π r ψ₀ n x₀
      exact ⟨xbar, hc, by rw [hξ]; exact hx₀.1, by rw [hη]; exact hx₀.2⟩
    choose xb hxb using hy
    obtain ⟨xt, hxtψ, hxt₂, hline⟩ := exists_chartPoint (r := r) (ψ₀ := ψ₀) (g₁ := g₁) hF (x.act h⁻¹) (fun n => ⟨xb n, hxb n⟩)
    let xt' : (chartERing Onr (algebraMap 𝒪 Onr π) r) →ₐ[Onr] R :=
      { toRingHom := xt
        commutes' := fun c => by
          have := congrArg (fun φ => φ c) hxtψ
          simp only [RingHom.comp_apply] at this
          exact this }

    have hu : algebraMap R C (xt' (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) =
        Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ z := by
      show algebraMap R C (xt (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) = _
      rw [← toOmega_eq_of_forall_line_eq hF (x.act h⁻¹) _ hline, AdicPoint.toOmega_act ϖ hF, hx, hmk]
    obtain ⟨hden, heval⟩ := hρt xt'
    rw [hu] at hden heval
    exact ⟨x, xt, xb, hx, hxb, hIEC, fun n => hxt₂ n (xb n) (hxb n), hden, heval⟩

  have uniq : ∀ (x : AdicPoint K₀ π R) (n : ℕ)
      (xb : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* modPow π R n),
      IsChartPt π r ψ₀ g₁ (x.act h⁻¹) n xb →
      ∀ (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →+* (modPow π R n)) (d : DeligneDatum (K := K₀) π (modPow π R n)),
        xbar.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀.toRingHom →
        (d.line (stdFullLattice K₀) =
            Submodule.span (modPow π R n) {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : (modPow π R n)) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span (modPow π R n) {(1 : (modPow π R n)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange (modPow π R n) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ d (x.pt n) → xbar = xb := by
    intro x n xb hxb xbar d hc hd hP
    have e : d = (x.act h⁻¹).pt n := eq_act_inv_pt π x h n d hP
    subst e
    exact IsChartPt.ext ⟨hc, hd.1, hd.2.1⟩ hxb

  have hunit_iff : ∀ (xt : chartERing Onr (algebraMap 𝒪 Onr π) r →+* R) (u : C),
      ρt.den.eval u ≠ 0 → ρt.evalAt u = algebraMap R C (xt t) →
      (IsUnit (xt t) ↔ Valued.v (ρt.num.eval u) = Valued.v (ρt.den.eval u)) := by
    intro xt u hden heval
    rw [isUnit_iff_v_eq_one hF, ← heval]
    show Valued.v (ρt.num.eval u / ρt.den.eval u) = 1 ↔ _
    rw [map_div₀, div_eq_one_iff_eq ((Valuation.ne_zero_iff _).2 hden)]
  refine ⟨m, L, M, hL, hM, ?_, ?_⟩
  ·
    intro k z hz
    obtain ⟨hzE, hzL, hzM⟩ := hz
    obtain ⟨x, xt, xb, hx, hxb, hIEC, hxt₂, hden, heval⟩ := key z hzE
    have hut : IsUnit (xt t) := (hunit_iff xt _ hden heval).2 ((hLM _ hden).2 ⟨k, hzL, hzM⟩)
    rw [hS]
    refine ⟨hEΩ z hzE, fun x' hx' n => ?_⟩
    have ex : x' = x := AdicPoint.toOmega_injective ϖ hF (hx'.trans hx.symm)
    rw [ex]
    refine ⟨xb n, (x.act h⁻¹).pt n, (hxb n).1, ⟨(hxb n).2.1, (hxb n).2.2, hIEC n⟩, hPull x n, ?_⟩
    have e := congrArg (fun φ => φ t) (hxt₂ n)
    simp only [RingHom.comp_apply] at e
    rw [e]
    exact hut.map _
  ·
    intro z hzS
    obtain ⟨hzΩ, hzall⟩ := (hS z).1 hzS

    obtain ⟨x₁, -, hx₁0⟩ := AdicPoint.toOmega_surjOn (C := C) ϖ hF hzΩ
    have hx₁ : x₁.toOmega C = z := hx₁0
    have hzE : z ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk h) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (h * edgeFlip K₀ ϖ)) := by
      obtain ⟨xbar, d, -, hd, hP, -⟩ := hzall x₁ hx₁ 0
      have e : d = (x₁.act h⁻¹).pt 0 := eq_act_inv_pt π x₁ h 0 d hP
      subst e
      rw [← hx₁]
      exact (inEdgeChart_act_inv_pt_zero_iff ϖ hF hunifK g₁ hg₁ h x₁).1 hd.2.2
    obtain ⟨x, xt, xb, hx, hxb, hIEC, hxt₂, hden, heval⟩ := key z hzE

    obtain ⟨xbar, d, hc, hd, hP, hu⟩ := hzall x hx 0
    have exb : xbar = xb 0 := uniq x 0 (xb 0) (hxb 0) xbar d hc hd hP
    have hut : IsUnit (xt t) := by
      apply isUnit_of_isUnit_mk hF 0
      have e := congrArg (fun φ => φ t) (hxt₂ 0)
      simp only [RingHom.comp_apply] at e
      rw [← e, ← exb]
      exact hu
    obtain ⟨k, hk⟩ := (hLM _ hden).1 ((hunit_iff xt _ hden heval).1 hut)
    exact ⟨k, hzE, hk.1, hk.2⟩

end

end S_CerednikDrinfeld_exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient (solution)
