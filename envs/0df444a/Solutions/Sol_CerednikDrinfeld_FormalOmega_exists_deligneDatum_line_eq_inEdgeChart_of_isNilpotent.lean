-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/88e90966-7ec2-53b3-be93-0ce756d5a5d4

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_edgeNondegAt_stdEdge_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace P2mWs2ChartDatum

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

private def _root_.P2mWs2ChartDatum.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "P2mWs2ChartDatum" "coord"
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

theorem D0_surjective (ξ : B) : Function.Surjective (D0 (𝒪 := 𝒪) (K := K) ξ) := by
  intro b
  refine ⟨b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0, ?_⟩
  rw [D0_apply, coord_tmul_stdBasisVec, coord_tmul_stdBasisVec]
  simp

theorem D1_surjective (η : B) : Function.Surjective (D1 (𝒪 := 𝒪) (K := K) η) := by
  intro b
  refine ⟨b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1, ?_⟩
  rw [D1_apply, coord_tmul_stdBasisVec, coord_tmul_stdBasisVec]
  simp

theorem invertible_N0 (ξ : B) :
    Module.Invertible B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) ⧸ N0 (𝒪 := 𝒪) (K := K) ξ) :=
  Module.Invertible.congr
    ((Submodule.quotEquivOfEq _ _ (N0_eq_ker (𝒪 := 𝒪) (K := K) ξ)).trans
      (LinearMap.quotKerEquivOfSurjective _ (D0_surjective (𝒪 := 𝒪) (K := K) ξ))).symm

theorem invertible_N1' (η : B) :
    Module.Invertible B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) ⧸ N1' (𝒪 := 𝒪) (K := K) η) :=
  Module.Invertible.congr
    ((Submodule.quotEquivOfEq _ _ (N1'_eq_ker (𝒪 := 𝒪) (K := K) η)).trans
      (LinearMap.quotKerEquivOfSurjective _ (D1_surjective (𝒪 := 𝒪) (K := K) η))).symm

theorem invertible_quot_map {V W : Type} [AddCommGroup V] [Module B V] [AddCommGroup W] [Module B W]
    (e : V ≃ₗ[B] W) (P : Submodule B V) [Module.Invertible B (V ⧸ P)] :
    Module.Invertible B (W ⧸ P.map e.toLinearMap) :=
  Module.Invertible.congr (Submodule.Quotient.equiv P (P.map e.toLinearMap) e rfl)

end P2mWs2ChartDatum

end

namespace P2mWs2ChartDatum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem inclBaseChange_tmul {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) (b : B) (v : ↥M₁.1) :
    inclBaseChange B h (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) :=
  rfl

theorem baseChange_tmul' {M₁ M₂ : FullLattice 𝒪 K} (f : ↥M₁.1 →ₗ[𝒪] ↥M₂.1) (b : B) (v : ↥M₁.1) :
    f.baseChange B (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪] f v :=
  rfl

end P2mWs2ChartDatum

open P2mWs2ChartDatum in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : chartERing 𝒪 π q →ₐ[𝒪] B) :
    ∃ d : DeligneDatum (K := K) π B,
      d.line (stdFullLattice K) =
        Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
      d.line (FullLattice.act g (stdFullLattice K)) =
        (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
          (actBaseChange B g (stdFullLattice K)).toLinearMap ∧
      d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
  classical
  have hgv : ∀ w : Fin 2 → K, (g : Matrix (Fin 2) (Fin 2) K).mulVec w = ![algebraMap 𝒪 K π * w 0, w 1] := by
    intro w; rw [hg]; ext i; fin_cases i <;> simp [Matrix.mulVec_diagonal]
  have hξη : x (chartERing.ξ 𝒪 π q) * x (chartERing.η 𝒪 π q) = algebraMap 𝒪 B π := by
    rw [← map_mul, chartERing.ξ_mul_η, AlgHom.commutes]
  have hdisc : IsUnit ((x (chartERing.ξ 𝒪 π q) ^ (q - 1) - 1) * (x (chartERing.η 𝒪 π q) ^ (q - 1) - 1)) := by
    have h := (chartERing.isUnit_discr 𝒪 π q).map x
    simpa only [map_mul, map_sub, map_pow, map_one] using h
  have hξu : IsUnit (x (chartERing.ξ 𝒪 π q) ^ (q - 1) - 1) := isUnit_of_mul_isUnit_left hdisc
  have hηu : IsUnit (x (chartERing.η 𝒪 π q) ^ (q - 1) - 1) := isUnit_of_mul_isUnit_right hdisc
  have hπ𝔭 : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → algebraMap 𝒪 B π ∈ 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨n, hn⟩ := hB
    exact h𝔭.mem_of_pow_mem n (by rw [hn]; exact 𝔭.zero_mem)

  have memM₁ : ∀ v : Fin 2 → K, v ∈ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 ↔
      (∃ a : 𝒪, v 0 = algebraMap 𝒪 K (π * a)) ∧ IsLocalization.IsInteger 𝒪 (v 1) := by
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
      obtain ⟨a, ha⟩ := hw 0
      refine ⟨⟨a, ?_⟩, ?_⟩
      · rw [hgv]; simp [← ha, map_mul]
      · rw [hgv]; simpa using hw 1
    · rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
      refine mem_latticeMap.mpr ⟨![algebraMap 𝒪 K a, algebraMap 𝒪 K c], ?_, ?_⟩
      · intro i; fin_cases i; exacts [⟨a, rfl⟩, ⟨c, rfl⟩]
      · rw [hgv]; ext i; fin_cases i
        · simp [ha, map_mul]
        · simp [hc]
  have hle : (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 ≤ (stdFullLattice (𝒪 := 𝒪) K).1 := by
    intro v hv
    obtain ⟨⟨a, ha⟩, h1⟩ := (memM₁ v).mp hv
    intro i; fin_cases i
    · exact ⟨π * a, ha.symm⟩
    · exact h1
  have hπM : ∀ v ∈ (stdFullLattice (𝒪 := 𝒪) K).1,
      algebraMap 𝒪 K π • v ∈ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 := by
    intro v hv
    refine (memM₁ _).mpr ⟨?_, ?_⟩
    · obtain ⟨a, ha⟩ := hv 0
      exact ⟨a, by rw [Pi.smul_apply, smul_eq_mul, ← ha, map_mul]⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact IsLocalization.isInteger_mul ⟨π, rfl⟩ (hv 1)

  have hge0 : ((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 0) :
      ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) = ![algebraMap 𝒪 K π, 0] := by
    rw [coe_latticeMapEquiv_apply, hgv]
    ext i; fin_cases i <;> simp [stdBasisVec]
  have hge1 : ((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 1) :
      ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) = ![0, 1] := by
    rw [coe_latticeMapEquiv_apply, hgv]
    ext i; fin_cases i <;> simp [stdBasisVec]

  haveI i0 := invertible_N0 (𝒪 := 𝒪) (K := K) (x (chartERing.ξ 𝒪 π q))
  haveI i1' := invertible_N1' (𝒪 := 𝒪) (K := K) (x (chartERing.η 𝒪 π q))
  haveI i1 := invertible_quot_map (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K))
    (N1' (𝒪 := 𝒪) (K := K) (x (chartERing.η 𝒪 π q)))

  have hincl0 : ∀ b : B, inclBaseChange B hle (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)
      (b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0)) = b ⊗ₜ[𝒪] (π • stdBasisVec (𝒪 := 𝒪) K 0) := by
    intro b
    rw [actBaseChange_tmul]
    erw [inclBaseChange_tmul]
    congr 1
    apply Subtype.ext
    show ((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 0) :
      ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
      ((π • stdBasisVec (𝒪 := 𝒪) K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
    rw [hge0, Submodule.coe_smul]
    ext i; fin_cases i <;> simp [stdBasisVec, Algebra.smul_def]
  have hincl1 : ∀ b : B, inclBaseChange B hle (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)
      (b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1)) = b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 := by
    intro b
    rw [actBaseChange_tmul]
    erw [inclBaseChange_tmul]
    congr 1
    apply Subtype.ext
    show ((latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec (𝒪 := 𝒪) K 1) :
      ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) : Fin 2 → K) =
      ((stdBasisVec (𝒪 := 𝒪) K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K)
    rw [hge1]
    ext i; fin_cases i <;> simp [stdBasisVec]

  have hmono : ((N1' (𝒪 := 𝒪) (K := K) (x (chartERing.η 𝒪 π q))).map
      (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap).map (inclBaseChange B hle) ≤
      N0 (𝒪 := 𝒪) (K := K) (x (chartERing.ξ 𝒪 π q)) := by
    rw [Submodule.map_le_iff_le_comap, Submodule.map_le_iff_le_comap, Submodule.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_comap, N0_eq_ker, LinearMap.mem_ker]
    rw [map_add, map_add, LinearEquiv.coe_coe, hincl0, hincl1, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
      D0_apply, map_add, map_add, coord_tmul_stdBasisVec, coord_tmul_stdBasisVec, coord_tmul_stdBasisVec,
      coord_tmul_stdBasisVec, if_pos rfl, if_neg (show (0 : Fin 2) ≠ 1 by decide), if_neg (show (1 : Fin 2) ≠ 0 by decide),
      if_pos rfl, ← hξη]
    ring

  have hsmul : (N0 (𝒪 := 𝒪) (K := K) (x (chartERing.ξ 𝒪 π q))).map
      ((smulInto π hπM).baseChange B :
        latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B]
          latticeBaseChange 𝒪 K B (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))) ≤
      (N1' (𝒪 := 𝒪) (K := K) (x (chartERing.η 𝒪 π q))).map (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Submodule.mem_comap, Submodule.mem_map]
    refine ⟨x (chartERing.ξ 𝒪 π q) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + (1 : B) ⊗ₜ[𝒪] (π • stdBasisVec (𝒪 := 𝒪) K 1), ?_, ?_⟩
    · rw [N1'_eq_ker, LinearMap.mem_ker, D1_apply, map_add, map_add, coord_tmul_stdBasisVec, coord_tmul_smul_stdBasisVec,
        coord_tmul_stdBasisVec, coord_tmul_smul_stdBasisVec, if_neg (show (1 : Fin 2) ≠ 0 by decide), if_pos rfl,
        if_pos rfl, if_neg (show (0 : Fin 2) ≠ 1 by decide), ← hξη]
      ring
    · rw [map_add, map_add, LinearEquiv.coe_coe, actBaseChange_tmul, actBaseChange_tmul, baseChange_tmul',
        baseChange_tmul']
      congr 1
      · congr 1
        apply Subtype.ext
        rw [hge0, coe_smulInto_apply]
        ext i; fin_cases i <;> simp [stdBasisVec, Algebra.smul_def]
      · congr 1
        apply Subtype.ext
        rw [coe_latticeMapEquiv_apply, Submodule.coe_smul, hgv, coe_smulInto_apply]
        ext i; fin_cases i <;> simp [stdBasisVec, Algebra.smul_def]

  have hND := fun (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) =>
    CerednikDrinfeld.FormalOmega.edgeNondegAt_stdEdge_of_isUnit π hπ q hq g hg B (x (chartERing.ξ 𝒪 π q))
      (x (chartERing.η 𝒪 π q)) hξη hξu hηu 𝔭 h𝔭 (hπ𝔭 𝔭 h𝔭)
  obtain ⟨d, hd0, hd1, hde⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_inEdgeChart_and_line_eq
    (K := K) hπ (B := B) hle hπM (N0 (𝒪 := 𝒪) (K := K) (x (chartERing.ξ 𝒪 π q)))
    ((N1' (𝒪 := 𝒪) (K := K) (x (chartERing.η 𝒪 π q))).map (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap)
    hmono hsmul (fun 𝔭 h𝔭 => (hND 𝔭 h𝔭).2.2.1) (fun 𝔭 h𝔭 => (hND 𝔭 h𝔭).2.2.2)
  exact ⟨d, hd0, hd1, hde⟩

end S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent (solution)
