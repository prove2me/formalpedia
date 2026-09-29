-- Prove2me | solution 1 for CerednikDrinfeld.exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1046bb0d-ebe8-5dfe-964c-2b11abc6e62f

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_surjOn
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_injective
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_act
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient

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

namespace EDB

noncomputable def specValue {R : Type} [CommRing R] {X : Scheme.{0}} (P : Spec (CommRingCat.of R) ⟶ X) (V : X.Opens)
    (p : X.presheaf.obj (Opposite.op V)) (hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ V) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hV).op).hom ((P.app V).hom p))

theorem specValue_eq_appLE {R : Type} [CommRing R] {X : Scheme.{0}} (P : Spec (CommRingCat.of R) ⟶ X) (V : X.Opens)
    (p : X.presheaf.obj (Opposite.op V)) (hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ V) :
    specValue P V p hV = ((P.appLE V ⊤ hV ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom p) := rfl

theorem map_specValue_eq {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}}
    (P : Spec (CommRingCat.of R) ⟶ X) (Q : Spec (CommRingCat.of R') ⟶ X)
    (hfac : Spec.map (CommRingCat.ofHom φ) ≫ P = Q)
    (V : X.Opens) (p : X.presheaf.obj (Opposite.op V)) (hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ P ⁻¹ᵁ V) :
    ∃ hV' : (⊤ : (Spec (CommRingCat.of R')).Opens) ≤ Q ⁻¹ᵁ V, φ (specValue P V p hV) = specValue Q V p hV' := by
  subst hfac
  have hV' : (⊤ : (Spec (CommRingCat.of R')).Opens) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ P) ⁻¹ᵁ V :=
    fun x _ => hV (Set.mem_univ _)
  refine ⟨hV', ?_⟩
  have e₂ : (⊤ : (Spec (CommRingCat.of R')).Opens) ≤
      Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) :=
    fun _ _ => Set.mem_univ _
  have htop : (Spec.map (CommRingCat.ofHom φ)).appTop = (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e₂ :=
    Scheme.Hom.app_eq_appLE _
  have key : P.appLE V ⊤ hV ≫ (Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom =
      (Spec.map (CommRingCat.ofHom φ) ≫ P).appLE V ⊤ hV' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom := by
    rw [htop, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
  rw [specValue_eq_appLE, specValue_eq_appLE, ← key, Scheme.ΓSpecIso_naturality]
  rfl

theorem exists_mul_pow_eq_of_basicOpen_le_preimage
    {A : Type} [CommRing A] {X : Scheme.{0}} (κ : Spec (CommRingCat.of A) ⟶ X) (V : X.Opens) (t : A)
    (ht : PrimeSpectrum.basicOpen t ≤ κ ⁻¹ᵁ V) (p : X.presheaf.obj (Opposite.op V)) :
    ∃ (a : A) (k : ℕ), ∀ (B : Type) [CommRing B] (φ : A →+* B), IsUnit (φ t) →
      ∀ (hφ : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ κ) ⁻¹ᵁ V),
        specValue (Spec.map (CommRingCat.ofHom φ) ≫ κ) V p hφ * φ t ^ k = φ a := by

  let s : ((Spec.structureSheaf A).obj.obj (Opposite.op (PrimeSpectrum.basicOpen t))) :=
    (κ.appLE V (PrimeSpectrum.basicOpen t) ht).hom p
  obtain ⟨k, a, hk⟩ := IsLocalization.Away.surj t s
  refine ⟨a, k, fun B _ φ hunit hφ => ?_⟩

  have e₂ : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen t := by
    intro x _
    change φ t ∉ x.asIdeal
    exact fun h => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hunit)

  let ψ : ((Spec.structureSheaf A).obj.obj (Opposite.op (PrimeSpectrum.basicOpen t))) →+* B :=
    ((Spec.map (CommRingCat.ofHom φ)).appLE (PrimeSpectrum.basicOpen t) ⊤ e₂ ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom
  have hval : specValue (Spec.map (CommRingCat.ofHom φ) ≫ κ) V p hφ = ψ s := by
    rw [specValue_eq_appLE,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) κ V (PrimeSpectrum.basicOpen t) ⊤ ht e₂]
    rfl

  have htop : (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (fun _ _ => Set.mem_univ _) :=
    Scheme.Hom.app_eq_appLE _
  have hmor : CommRingCat.ofHom (algebraMap A ((structureSheafInType A A).obj.obj (Opposite.op (PrimeSpectrum.basicOpen t)))) ≫
      (Spec.map (CommRingCat.ofHom φ)).appLE (PrimeSpectrum.basicOpen t) ⊤ e₂ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      CommRingCat.ofHom φ := by
    rw [← StructureSheaf.algebraMap_self_map A (Opposite.op (PrimeSpectrum.basicOpen t)) (Opposite.op ⊤) (homOfLE le_top).op]
    erw [Category.assoc, Scheme.Hom.map_appLE_assoc]
    erw [← Scheme.ΓSpecIso_inv (CommRingCat.of A), ← htop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hψ : ∀ x : A, ψ (algebraMap A _ x) = φ x := fun x =>
    congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom x) hmor
  rw [hval, ← hψ t, ← hψ a, ← map_pow, ← map_mul, hk]

end EDB

namespace EDB
section Hol
variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {π : 𝒪} {ϖ : PseudoUniformizer K C} {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C]
  [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]

theorem exists_vRestrict_eq (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := C)) : C →*₀ Γ₀))ˣ) :
    ∃ y : C, y ≠ 0 ∧ vRestrict C y = (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := C)) : C →*₀ Γ₀)) := by
  obtain ⟨y, hy⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v (R := C)) : C →*₀ Γ₀) (γ : MonoidWithZeroHom.ValueGroup₀ _)
  refine ⟨y, fun h0 => ?_, hy⟩
  rw [h0, map_zero] at hy
  exact γ.ne_zero hy.symm

theorem mem_holOn_of_approx (hF : IsAdicFrame π ϖ R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set C) (F : ↥S → C) (ρ : ℕ → RatPair C)
    (hpf : ∀ k, (ρ k).IsPoleFreeOn S) (hb : ∀ k (z : ↥S), Valued.v ((ρ k).evalAt z) ≤ 1)
    (happ : ∀ k (z : ↥S), Valued.v ((ρ k).evalAt z - F z) ≤ Valued.v (algebraMap 𝒪 C π) ^ (k + 1)) :
    F ∈ holOn C S := by
  rw [mem_holOn_iff]
  refine ⟨ρ, hpf, ⟨1, fun k z => by rw [map_one]; exact hb k z⟩, ?_⟩
  rw [tendstoUniformly_iff_vRestrict]
  intro γ
  obtain ⟨y, hy0, hy⟩ := exists_vRestrict_eq γ

  have hπ0 : algebraMap 𝒪 C π ≠ 0 := fun h => by
    have := hF.v_algebraMap_pos; rw [h, map_zero] at this; exact lt_irrefl _ this
  obtain ⟨N, hN⟩ := hrk (algebraMap 𝒪 C π) (y * algebraMap 𝒪 C π) hF.v_algebraMap_lt_one (mul_ne_zero hy0 hπ0)
  have hlt : Valued.v (algebraMap 𝒪 C π) ^ (N + 1) < Valued.v y := by
    have hy' : 0 < Valued.v y := (Valuation.pos_iff _).2 hy0
    calc Valued.v (algebraMap 𝒪 C π) ^ (N + 1) ≤ Valued.v (algebraMap 𝒪 C π) ^ N :=
          pow_le_pow_right_of_le_one' (le_of_lt hF.v_algebraMap_lt_one) (Nat.le_succ N)
      _ ≤ Valued.v (y * algebraMap 𝒪 C π) := hN
      _ = Valued.v y * Valued.v (algebraMap 𝒪 C π) := map_mul _ _ _
      _ < Valued.v y * 1 := mul_lt_mul_of_pos_left hF.v_algebraMap_lt_one hy'
      _ = Valued.v y := mul_one _
  refine Filter.eventually_atTop.2 ⟨N, fun k hk z => ?_⟩
  rw [← hy, ← v_lt_iff_vRestrict_lt]
  calc Valued.v ((ρ k).evalAt z - F z) ≤ Valued.v (algebraMap 𝒪 C π) ^ (k + 1) := happ k z
    _ ≤ Valued.v (algebraMap 𝒪 C π) ^ (N + 1) :=
        pow_le_pow_right_of_le_one' (le_of_lt hF.v_algebraMap_lt_one) (Nat.succ_le_succ hk)
    _ < Valued.v y := hlt

end Hol
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

namespace EDB

theorem exists_ratPair_pullback_quot (K₀ : Type) [Field K₀] (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C]
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (p q : Omega.RatPair C) (k : ℕ) :
    ∃ ρ : Omega.RatPair C, ∀ z : C, z ∈ Omega.upperHalfPlane K₀ C →
      p.den.eval (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z) ≠ 0 →
      q.den.eval (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z) ≠ 0 →
      q.evalAt (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z) ≠ 0 →
      ρ.den.eval z ≠ 0 ∧
      ρ.evalAt z = p.evalAt (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z) /
        q.evalAt (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z) ^ k := by
  refine ⟨RatPair.pullback g ⟨p.num * q.den ^ k, p.den * q.num ^ k⟩, fun z hz hp hq hq0 => ?_⟩
  have hden := moebius_denom_ne_zero_of_mem K₀ hz g
  rw [pmoebius_mk K₀ g z hden] at hp hq hq0 ⊢
  have hqn : q.num.eval (moebius K₀ C g z) ≠ 0 := by
    intro h0; apply hq0; rw [RatPair.evalAt, h0, zero_div]
  refine ⟨?_, ?_⟩
  · rw [RatPair.pullback_den_eval hz]
    refine mul_ne_zero (pow_ne_zero _ hden) ?_
    show (p.den * q.num ^ k).eval (moebius K₀ C g z) ≠ 0
    rw [Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero hp (pow_ne_zero _ hqn)
  · rw [RatPair.evalAt_pullback hz]
    show (p.num * q.den ^ k).eval (moebius K₀ C g z) / (p.den * q.num ^ k).eval (moebius K₀ C g z) =
      p.num.eval (moebius K₀ C g z) / p.den.eval (moebius K₀ C g z) /
        (q.num.eval (moebius K₀ C g z) / q.den.eval (moebius K₀ C g z)) ^ k
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_pow, div_pow, div_div_div_eq]

end EDB

open EDB in
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

    (V : 𝒳.Opens) (p : 𝒳.presheaf.obj (Opposite.op V)) (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (t : chartERing Onr (algebraMap 𝒪 Onr π) r)
    (ht : ∀ n : ℕ, PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) t) ≤ (κ h n) ⁻¹ᵁ ((Limits.pullback.fst f (sn n)) ⁻¹ᵁ V))
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
    ∃ F : ↥S → C, F ∈ Omega.holOn C S ∧ (∀ z : ↥S, Valued.v (F z) ≤ 1) ∧
      ∀ (x : AdicPoint K₀ π R) (z : C) (hz : z = x.toOmega C) (hzS : z ∈ S)
        (hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (Φ x).1 ⁻¹ᵁ V),
        F ⟨z, hzS⟩ = algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
          (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hV).op).hom (((Φ x).1.app V).hom p))) := by
  classical
  haveI := hdvr
  have hπpos := hF.v_algebraMap_pos
  have hπC0 : algebraMap 𝒪 C π ≠ 0 := fun h0 => by rw [h0, map_zero] at hπpos; exact lt_irrefl _ hπpos

  letI algOnrR : Algebra Onr R := ψ₀.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap Onr R c = ψ₀ c := fun c => rfl
  have hπ' : algebraMap R C (algebraMap Onr R (algebraMap 𝒪 Onr π)) ≠ 0 := by
    rw [halg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]; exact hπC0

  have hxz : ∀ z : ↥S, ∃ x : AdicPoint K₀ π R, x.toOmega C = (z : C) := fun z => by
    obtain ⟨x, -, hx⟩ := AdicPoint.toOmega_surjOn (C := C) ϖ hF ((hS z).1 z.2).1
    exact ⟨x, hx⟩
  choose xz hxz using hxz

  have chart : ∀ (x : AdicPoint K₀ π R), x.toOmega C ∈ S → ∀ n : ℕ,
      ∃ xbar : (chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)} →+* modPow π R n,
        IsChartPt π r ψ₀ g₁ (x.act h⁻¹) n xbar ∧
        ((x.act h⁻¹).pt n).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) ∧
        IsUnit (xbar (Ideal.Quotient.mk _ t)) := by
    intro x hx n
    obtain ⟨xbar, d, hc, hd, hP, hu⟩ := ((hS _).1 hx).2 x rfl n
    have e : d = (x.act h⁻¹).pt n := eq_act_inv_pt π x h n d hP
    subst e
    exact ⟨xbar, ⟨hc, hd.1, hd.2.1⟩, hd.2.2, hu⟩
  have hPB : ∀ (x : AdicPoint K₀ π R) (n : ℕ),
      DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) h⁻¹ ((x.act h⁻¹).pt n) (x.pt n) := fun x n =>
    (isPullback_inv_iff π h _ _).2 (by
      show x.pt n = tr π h (tr π h⁻¹ (x.pt n))
      rw [← tr_mul, mul_inv_cancel, tr_one])

  have hfac : ∀ (x : AdicPoint K₀ π R) (n : ℕ) (xbar : (chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)} →+* modPow π R n),
      IsChartPt π r ψ₀ g₁ (x.act h⁻¹) n xbar →
      ((x.act h⁻¹).pt n).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) →
      Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ (Φ x).1 =
        Spec.map (CommRingCat.ofHom xbar) ≫ κ h n ≫ Limits.pullback.fst f (sn n) := fun x n xbar hcp hin =>
    spec_comp_eq_spec_xbar_comp_chart 𝒪 π K₀ Onr 𝒳 f Θ ψ₀ g₁ sn κ hκ x n h (Φ x).1 (hΦ.1 x n)
      xbar hcp.1 ((x.act h⁻¹).pt n) ⟨hcp.2.1, hcp.2.2, hin⟩ (hPB x n)

  have hVx : ∀ (x : AdicPoint K₀ π R), x.toOmega C ∈ S → (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (Φ x).1 ⁻¹ᵁ V := by
    intro x hx
    haveI := isLocalRing hF
    obtain ⟨xbar, hcp, hin, hu⟩ := chart x hx 0
    apply top_le_preimage_of_isLocalRing (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})
    · intro htop
      apply not_isUnit_algebraMap_pi hF
      rw [Ideal.span_singleton_eq_top, zero_add, pow_one] at htop
      exact htop
    · rw [hfac x 0 xbar hcp hin, Scheme.Hom.comp_preimage]
      intro q _
      apply ht 0

      show (Spec.map (CommRingCat.ofHom xbar)).base q ∈ PrimeSpectrum.basicOpen _
      rw [Spec.map_base]
      show xbar (Ideal.Quotient.mk _ t) ∉ q.asIdeal
      exact fun hm => q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)

  let F : ↥S → C := fun z => algebraMap R C (specValue (Φ (xz z)).1 V p (hVx (xz z) ((hxz z).symm ▸ z.2)))

  have ht' : ∀ n : ℕ, PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) t) ≤
      (κ h n ≫ Limits.pullback.fst f (sn n)) ⁻¹ᵁ V := fun n => by rw [Scheme.Hom.comp_preimage]; exact ht n
  choose a k hak using fun n => exists_mul_pow_eq_of_basicOpen_le_preimage (κ h n ≫ Limits.pullback.fst f (sn n)) V _ (ht' n) p
  choose atl hat using fun n => Ideal.Quotient.mk_surjective (a n)
  choose ρa hρa using fun n => exists_ratPair_evalAt_eq_chartERing (R := R) (C := C) (algebraMap 𝒪 Onr π) r hπ' (atl n)
  obtain ⟨ρt, hρt⟩ := exists_ratPair_evalAt_eq_chartERing (R := R) (C := C) (algebraMap 𝒪 Onr π) r hπ' t
  choose ρ hρ using fun n => exists_ratPair_pullback_quot K₀ C h⁻¹ (ρa n) ρt (k n)

  have est : ∀ (z : ↥S) (n : ℕ), (ρ n).den.eval (z : C) ≠ 0 ∧ Valued.v ((ρ n).evalAt z) ≤ 1 ∧
      Valued.v ((ρ n).evalAt z - F z) ≤ Valued.v (algebraMap 𝒪 C π) ^ (n + 1) := by
    intro z n
    set x := xz z with hxdef
    have hxS : x.toOmega C ∈ S := (hxz z).symm ▸ z.2

    have hy : ∀ m : ℕ, ∃ xbar, IsChartPt π r ψ₀ g₁ (x.act h⁻¹) m xbar := fun m => by
      obtain ⟨xbar, hcp, -, -⟩ := chart x hxS m; exact ⟨xbar, hcp⟩
    obtain ⟨xt, hxtψ, hxt, hline⟩ := exists_chartPoint (r := r) (ψ₀ := ψ₀) (g₁ := g₁) hF (x.act h⁻¹) hy
    let xt' : (chartERing Onr (algebraMap 𝒪 Onr π) r) →ₐ[Onr] R :=
      { toRingHom := xt
        commutes' := fun c => by
          have := congrArg (fun φ => φ c) hxtψ
          simp only [RingHom.comp_apply] at this
          exact this }

    have hu : algebraMap R C (xt (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) =
        Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h⁻¹) (z : C) := by
      rw [← toOmega_eq_of_forall_line_eq hF (x.act h⁻¹) _ hline, AdicPoint.toOmega_act ϖ hF, hxz]
    have hzΩ : (z : C) ∈ Omega.upperHalfPlane K₀ C := ((hS z).1 z.2).1

    obtain ⟨xbar, hcp, hin, hunit⟩ := chart x hxS n
    have hxbar : ∀ y, xbar (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (xt y) := fun y => by
      have := congrArg (fun φ => φ y) (hxt n xbar hcp); simpa only [RingHom.comp_apply] using this

    have htu : IsUnit (xt t) := isUnit_of_isUnit_mk hF n (by rw [← hxbar]; exact hunit)
    have htC : Valued.v (algebraMap R C (xt t)) = 1 := (isUnit_iff_v_eq_one hF _).1 htu
    have htC0 : algebraMap R C (xt t) ≠ 0 := fun h0 => by rw [h0, map_zero] at htC; exact zero_ne_one htC

    obtain ⟨hρa1, hρa2⟩ := hρa n xt'
    obtain ⟨hρt1, hρt2⟩ := hρt xt'
    have eξ : algebraMap R C (xt' (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) =
        Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h⁻¹) (z : C) := hu
    rw [eξ] at hρa1 hρa2 hρt1 hρt2
    have hρt0 : ρt.evalAt (Omega.pmoebius K₀ (Matrix.ProjGenLinGroup.mk h⁻¹) (z : C)) ≠ 0 := by
      rw [hρt2]; exact htC0
    obtain ⟨hρ1, hρ2⟩ := hρ n z hzΩ hρa1 hρt1 hρt0
    rw [hρa2, hρt2] at hρ2

    obtain ⟨hV', hval⟩ := map_specValue_eq (algebraMap R (modPow π R n)) (Φ x).1 _ (hfac x n xbar hcp hin) V p (hVx x hxS)
    have hfrac := hak n (modPow π R n) xbar hunit hV'
    rw [← hval, hxbar, ← hat n, hxbar] at hfrac
    change Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (specValue (Φ x).1 V p (hVx x hxS)) *
        Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (xt t) ^ (k n) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (xt (atl n)) at hfrac
    have hfrac' : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (specValue (Φ x).1 V p (hVx x hxS) * xt t ^ (k n)) =
        Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (xt (atl n)) := by
      simpa only [map_mul, map_pow] using hfrac
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hfrac'
    obtain ⟨c, hc⟩ := hfrac'
    have hFz : F z = algebraMap R C (specValue (Φ x).1 V p (hVx x hxS)) := rfl
    refine ⟨hρ1, ?_, ?_⟩
    · rw [hρ2]
      show Valued.v (algebraMap R C (xt (atl n)) / algebraMap R C (xt t) ^ k n) ≤ 1
      rw [map_div₀, map_pow, htC, one_pow, div_one]; exact hF.v_algebraMap_le_one _
    · rw [hρ2, hFz]
      show Valued.v (algebraMap R C (xt (atl n)) / algebraMap R C (xt t) ^ k n -
        algebraMap R C (specValue (Φ x).1 V p (hVx x hxS))) ≤ _
      have e1 : algebraMap R C (xt (atl n)) / algebraMap R C (xt t) ^ (k n) - algebraMap R C (specValue (Φ x).1 V p (hVx x hxS)) =
          -(algebraMap R C (algebraMap 𝒪 R π ^ (n + 1) * c)) / algebraMap R C (xt t) ^ (k n) := by
        rw [← hc, map_sub, map_mul, map_pow]
        field_simp
        ring
      rw [e1, map_div₀, Valuation.map_neg]
      simp only [map_mul, map_pow, htC, one_pow, div_one]
      rw [← IsScalarTower.algebraMap_apply 𝒪 R C π]
      calc Valued.v (algebraMap 𝒪 C π) ^ (n + 1) * Valued.v (algebraMap R C c)
          ≤ Valued.v (algebraMap 𝒪 C π) ^ (n + 1) * 1 := mul_le_mul_right (hF.v_algebraMap_le_one c) _
        _ = _ := mul_one _
  refine ⟨F, ?_, ?_, ?_⟩
  · exact mem_holOn_of_approx hF hrk S F ρ (fun n z hz => (est ⟨z, hz⟩ n).1) (fun n z => (est z n).2.1)
      (fun n z => (est z n).2.2)
  · intro z; exact hF.v_algebraMap_le_one _
  · intro x z hz hzS hV
    have hx : x = xz ⟨z, hzS⟩ := AdicPoint.toOmega_injective (C := C) ϖ hF (by
      show x.toOmega C = (xz ⟨z, hzS⟩).toOmega C
      rw [hxz]; exact hz.symm)
    subst hx
    rfl

end

end S_CerednikDrinfeld_exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient (solution)
