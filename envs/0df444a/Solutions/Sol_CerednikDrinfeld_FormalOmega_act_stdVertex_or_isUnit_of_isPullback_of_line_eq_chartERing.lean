-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3f59f615-c073-5f24-bc4e-bc1f33a1f521

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_of_vertexNondegAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct Matrix
p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing.CerednikDrinfeld.FormalOmega"

noncomputable section

namespace CerednikDrinfeld
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "stdFullLattice stdBasisVec transportEquiv coe_ofEq_apply DeligneDatum.line_transport coe_latticeMapEquiv_apply DeligneDatum.pullback Omega Omega.action latticeBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback chartERing chartERing.ξ chartERing.η chartERing.ξ_mul_η chartERing.isUnit_discr DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt DeligneDatum.edgeNondegAt_pullback_act_inv DeligneDatum.edgeNondegAt_of_vertexNondegAt"
namespace ChartIncidence
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

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

private def _root_.CerednikDrinfeld.FormalOmega.ChartIncidence.coord (i : Fin 2) : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := (tensorBasis B).coord i

p2m_export "CerednikDrinfeld.FormalOmega.ChartIncidence" "coord"
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

theorem apply_mem_of_mem_sup_smul_top {X : Type} [AddCommGroup X] [Module B X] (D : X →ₗ[B] B)
    (P : Submodule B X) (hP : ∀ y ∈ P, D y = 0) (𝔭 : Ideal B) {x : X}
    (hx : x ∈ P ⊔ (𝔭 • ⊤ : Submodule B X)) : D x ∈ 𝔭 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, hP y hy, zero_add]
  refine Submodule.smul_induction_on (p := fun z => D z ∈ 𝔭) hz (fun r hr n _ => ?_) (fun a c ha hc => ?_)
  · show D (r • n) ∈ 𝔭
    rw [LinearMap.map_smul, smul_eq_mul]; exact Ideal.mul_mem_right (D n) 𝔭 hr
  · show D (a + c) ∈ 𝔭
    rw [map_add]; exact 𝔭.add_mem ha hc

theorem pow_sub_mem_span [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π) (q : ℕ)
    (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) (hq0 : 0 < q) (a : 𝒪) : a ^ q - a ∈ Ideal.span {π} := by
  haveI : (Ideal.span {π}).IsMaximal := by rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal 𝒪
  letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = q := by rw [← Nat.card_eq_fintype_card]; exact hq
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
  have := FiniteField.pow_card (Ideal.Quotient.mk (Ideal.span {π}) a)
  rwa [hcard] at this

theorem mk_algebraMap_pow [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π) (q : ℕ)
    (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) (hq0 : 0 < q) (𝔭 : Ideal B) (hπ𝔭 : algebraMap 𝒪 B π ∈ 𝔭) (a : 𝒪) :
    (Ideal.Quotient.mk 𝔭 (algebraMap 𝒪 B a)) ^ q = Ideal.Quotient.mk 𝔭 (algebraMap 𝒪 B a) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (pow_sub_mem_span π hπ q hq hq0 a)
  rw [← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hc, map_mul]
  exact 𝔭.mul_mem_right _ hπ𝔭

theorem isUnit_of_not_dvd [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π) {a : 𝒪}
    (ha : ¬ π ∣ a) : IsUnit a := by
  by_contra h
  apply ha
  have : a ∈ IsLocalRing.maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal a).mpr h
  rw [hπ.maximalIdeal_eq] at this
  exact Ideal.mem_span_singleton.mp this

theorem pow_pred_sub_one_mem [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (π : 𝒪) (hπ : Irreducible π) (q : ℕ)
    (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) (hq0 : 0 < q) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime)
    (hπ𝔭 : algebraMap 𝒪 B π ∈ 𝔭) (x : B) (a₀ a₁ : 𝒪) (ha₀ : ¬ π ∣ a₀)
    (h : algebraMap 𝒪 B a₀ - x * algebraMap 𝒪 B a₁ ∈ 𝔭) : x ^ (q - 1) - 1 ∈ 𝔭 := by
  haveI : Nontrivial (B ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr h𝔭.ne_top
  haveI : IsDomain (B ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  set mk := Ideal.Quotient.mk 𝔭 with hmk
  have hu : IsUnit (mk (algebraMap 𝒪 B a₀)) := ((isUnit_of_not_dvd π hπ ha₀).map (algebraMap 𝒪 B)).map mk
  have hne : mk (algebraMap 𝒪 B a₀) ≠ 0 := hu.ne_zero
  have heq : mk (algebraMap 𝒪 B a₀) = mk x * mk (algebraMap 𝒪 B a₁) := by
    rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact h
  have hne₁ : mk (algebraMap 𝒪 B a₁) ≠ 0 := by intro h0; rw [heq, h0, mul_zero] at hne; exact hne rfl
  have f₀ := mk_algebraMap_pow B π hπ q hq hq0 𝔭 hπ𝔭 a₀
  have f₁ := mk_algebraMap_pow B π hπ q hq hq0 𝔭 hπ𝔭 a₁

  have g₀ : mk (algebraMap 𝒪 B a₀) ^ (q - 1) = 1 := by
    have : mk (algebraMap 𝒪 B a₀) ^ (q - 1) * mk (algebraMap 𝒪 B a₀) = 1 * mk (algebraMap 𝒪 B a₀) := by
      rw [← pow_succ, Nat.sub_add_cancel hq0, f₀, one_mul]
    exact mul_right_cancel₀ hne this
  have g₁ : mk (algebraMap 𝒪 B a₁) ^ (q - 1) = 1 := by
    have : mk (algebraMap 𝒪 B a₁) ^ (q - 1) * mk (algebraMap 𝒪 B a₁) = 1 * mk (algebraMap 𝒪 B a₁) := by
      rw [← pow_succ, Nat.sub_add_cancel hq0, f₁, one_mul]
    exact mul_right_cancel₀ hne₁ this
  have : mk x ^ (q - 1) = 1 := by
    have := congrArg (fun y => y ^ (q - 1)) heq
    simp only [mul_pow, g₀, g₁, mul_one] at this
    exact this.symm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, this, sub_self]

section Pullback

variable (π : 𝒪)
variable {B}

theorem eq_pullback_of_isPullback {g : Matrix.GeneralLinearGroup (Fin 2) K} {d d' : DeligneDatum (K := K) π B}
    (h : DeligneDatum.IsPullback (K := K) (π := π) B g d d') : d' = DeligneDatum.pullback π B g d :=
  DeligneDatum.ext' (funext fun M => h M)

theorem pullback_inv_inv_pullback_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B g⁻¹⁻¹ (DeligneDatum.pullback π B g⁻¹ d) = d := by
  have h1 : DeligneDatum.pullback π B (g⁻¹ * g)⁻¹ d =
      DeligneDatum.pullback π B g⁻¹⁻¹ (DeligneDatum.pullback π B g⁻¹ d) :=
    (Omega.action K π).act_mul B g⁻¹ g d
  have h2 : DeligneDatum.pullback π B (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ d = d :=
    (Omega.action K π).act_one B d
  rw [← h1, inv_mul_cancel, h2]

theorem pullback_pullback (g h : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B g (DeligneDatum.pullback π B h d) = DeligneDatum.pullback π B (h * g) d := by
  have h1 := (Omega.action K π).act_mul B g⁻¹ h⁻¹ d
  change DeligneDatum.pullback π B (g⁻¹ * h⁻¹)⁻¹ d =
    DeligneDatum.pullback π B g⁻¹⁻¹ (DeligneDatum.pullback π B h⁻¹⁻¹ d) at h1
  rw [inv_inv, inv_inv, mul_inv_rev, inv_inv, inv_inv] at h1
  exact h1.symm

theorem pullback_one (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (1 : Matrix.GeneralLinearGroup (Fin 2) K) d = d := by
  have h1 := (Omega.action K π).act_one B d
  change DeligneDatum.pullback π B (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ d = d at h1
  rwa [inv_one] at h1

theorem pullback_inv_pullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B g⁻¹ (DeligneDatum.pullback π B g d) = d := by
  rw [pullback_pullback, mul_inv_cancel, pullback_one]

theorem pullback_pullback_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B g (DeligneDatum.pullback π B g⁻¹ d) = d := by
  rw [pullback_pullback, inv_mul_cancel, pullback_one]

theorem pullback_scalarGL (c : Kˣ) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (scalarGL c) d = d := by
  apply DeligneDatum.ext'
  funext M
  show (d.line (FullLattice.act (scalarGL c) M)).comap (actBaseChange B (scalarGL c) M).toLinearMap = d.line M
  rw [d.homothety c M]
  exact Submodule.comap_map_eq_of_injective (actBaseChange B (scalarGL c) M).injective _

theorem scalarGL_inv (c : Kˣ) : (scalarGL c⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) = (scalarGL c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← scalarGL_mul, inv_mul_cancel, scalarGL_one])

theorem vertexNondegAt_pullback (d : DeligneDatum (K := K) π B) (h : Matrix.GeneralLinearGroup (Fin 2) K) (𝔭 : Ideal B)
    (N : FullLattice 𝒪 K) (hV : d.VertexNondegAt π 𝔭 N) :
    (DeligneDatum.pullback π B h d).VertexNondegAt π 𝔭 (FullLattice.act h⁻¹ N) := by
  have hE : d.EdgeNondegAt π 𝔭 N N :=
    DeligneDatum.edgeNondegAt_of_vertexNondegAt π d 𝔭 N N le_rfl
      (fun v => by rw [algebraMap_smul]; exact N.1.smul_mem π v.2) hV
  exact (DeligneDatum.edgeNondegAt_pullback_act_inv π d h 𝔭 N N hE).2.2.2

theorem vertexNondegAt_act_scalarGL (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (N : FullLattice 𝒪 K) (c : Kˣ)
    (hV : d.VertexNondegAt π 𝔭 N) : d.VertexNondegAt π 𝔭 (FullLattice.act (scalarGL c) N) := by
  have h := vertexNondegAt_pullback π d (scalarGL c⁻¹) 𝔭 N hV
  rwa [pullback_scalarGL, scalarGL_inv, inv_inv] at h

theorem vertexNondegAt_congr (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) {N₁ N₂ : FullLattice 𝒪 K} (h : N₁.1 = N₂.1)
    (hV : d.VertexNondegAt π 𝔭 N₁) : d.VertexNondegAt π 𝔭 N₂ := by
  obtain rfl : N₁ = N₂ := Subtype.ext h
  exact hV

theorem edgeNondegAt_congr (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) {N₁' N₁ N₂' N₂ : FullLattice 𝒪 K}
    (h' : N₁'.1 = N₂'.1) (h : N₁.1 = N₂.1)
    (hE : d.EdgeNondegAt π 𝔭 N₁' N₁) : d.EdgeNondegAt π 𝔭 N₂' N₂ := by
  obtain rfl : N₁ = N₂ := Subtype.ext h
  obtain rfl : N₁' = N₂' := Subtype.ext h'
  exact hE

theorem line_pullback_std (d : DeligneDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (S : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)))
    (h : d.line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)) = S.map (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap) :
    (DeligneDatum.pullback π B g d).line (stdFullLattice (𝒪 := 𝒪) K) = S := by
  show (d.line (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))).comap (actBaseChange B g _).toLinearMap = S
  rw [h]
  exact Submodule.comap_map_eq_of_injective (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).injective _

theorem map_mem_sup_smul_top {X Y : Type} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y] (f : X →ₗ[B] Y)
    (S : Submodule B X) (𝔭 : Ideal B) {z : X} (hz : z ∈ S ⊔ (𝔭 • ⊤ : Submodule B X)) :
    f z ∈ S.map f ⊔ (𝔭 • ⊤ : Submodule B Y) := by
  have : (S ⊔ (𝔭 • ⊤ : Submodule B X)).map f ≤ S.map f ⊔ (𝔭 • ⊤ : Submodule B Y) := by
    rw [Submodule.map_sup, Submodule.map_smul'']
    exact sup_le_sup_left (Submodule.smul_mono le_rfl le_top) _
  exact this (Submodule.mem_map_of_mem hz)

end Pullback

section Dictionary

variable (π : 𝒪)
variable {B}

theorem vertexNondegAt_std_of_line_eq (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (a b : B)
    (hline : d.line (stdFullLattice (𝒪 := 𝒪) K) =
      Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1})
    (hab : ∀ μ ν : 𝒪, ¬ (π ∣ μ ∧ π ∣ ν) → algebraMap 𝒪 B ν * a - algebraMap 𝒪 B μ * b ∉ 𝔭) :
    d.VertexNondegAt π 𝔭 (stdFullLattice (𝒪 := 𝒪) K) := by
  intro v hv hmem
  have hcoord : ¬ (π ∣ coordEquiv v 0 ∧ π ∣ coordEquiv v 1) := by
    rintro ⟨⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩⟩
    apply hv
    refine ⟨⟨![algebraMap 𝒪 K c₀, algebraMap 𝒪 K c₁], ?_⟩, ?_⟩
    · intro i; fin_cases i; exacts [⟨c₀, rfl⟩, ⟨c₁, rfl⟩]
    · show (v : Fin 2 → K) = _
      ext i; fin_cases i
      · change (v : Fin 2 → K) 0 = algebraMap 𝒪 K π • algebraMap 𝒪 K c₀
        rw [smul_eq_mul, ← map_mul, ← hc₀, algebraMap_coordEquiv]
      · change (v : Fin 2 → K) 1 = algebraMap 𝒪 K π • algebraMap 𝒪 K c₁
        rw [smul_eq_mul, ← map_mul, ← hc₁, algebraMap_coordEquiv]
  let D : latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K) →ₗ[B] B := b • coord B 0 - a • coord B 1
  have hD : ∀ z ∈ Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1}, D z = 0 := by
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [LinearMap.map_smul]
    simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, map_add, coord_tmul_stdBasisVec]
    simp [mul_comm]
  rw [hline] at hmem
  have hDv := apply_mem_of_mem_sup_smul_top B D _ hD 𝔭 hmem
  simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, coord_tmul, one_mul, smul_eq_mul] at hDv
  apply hab (coordEquiv v 0) (coordEquiv v 1) hcoord
  have : algebraMap 𝒪 B (coordEquiv v 1) * a - algebraMap 𝒪 B (coordEquiv v 0) * b =
      -(b * algebraMap 𝒪 B (coordEquiv v 0) - a * algebraMap 𝒪 B (coordEquiv v 1)) := by ring
  rw [this]
  exact 𝔭.neg_mem hDv

theorem hab_fst [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (hπ : Irreducible π) (q : ℕ)
    (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) (hq0 : 0 < q) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime)
    (hπ𝔭 : algebraMap 𝒪 B π ∈ 𝔭) (x : B) (hx : x ∉ 𝔭) (hxq : x ^ (q - 1) - 1 ∉ 𝔭) :
    ∀ μ ν : 𝒪, ¬ (π ∣ μ ∧ π ∣ ν) → algebraMap 𝒪 B ν * x - algebraMap 𝒪 B μ * 1 ∉ 𝔭 := by
  intro μ ν hμν hmem
  by_cases hμ : π ∣ μ
  · have hν : ¬ π ∣ ν := fun hν => hμν ⟨hμ, hν⟩
    obtain ⟨c, rfl⟩ := hμ
    have h1 : algebraMap 𝒪 B ν * x ∈ 𝔭 := by
      have : algebraMap 𝒪 B ν * x = (algebraMap 𝒪 B ν * x - algebraMap 𝒪 B (π * c) * 1) +
          algebraMap 𝒪 B π * algebraMap 𝒪 B c := by rw [map_mul]; ring
      rw [this]
      exact 𝔭.add_mem hmem (𝔭.mul_mem_right _ hπ𝔭)
    rcases h𝔭.mem_or_mem h1 with h | h
    · exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h ((isUnit_of_not_dvd π hπ hν).map (algebraMap 𝒪 B)))
    · exact hx h
  · apply hxq
    refine pow_pred_sub_one_mem B π hπ q hq hq0 𝔭 h𝔭 hπ𝔭 x μ ν hμ ?_
    have : algebraMap 𝒪 B μ - x * algebraMap 𝒪 B ν = -(algebraMap 𝒪 B ν * x - algebraMap 𝒪 B μ * 1) := by ring
    rw [this]
    exact 𝔭.neg_mem hmem

theorem hab_snd [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (hπ : Irreducible π) (q : ℕ)
    (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) (hq0 : 0 < q) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime)
    (hπ𝔭 : algebraMap 𝒪 B π ∈ 𝔭) (y : B) (hy : y ∉ 𝔭) (hyq : y ^ (q - 1) - 1 ∉ 𝔭) :
    ∀ μ ν : 𝒪, ¬ (π ∣ μ ∧ π ∣ ν) → algebraMap 𝒪 B ν * 1 - algebraMap 𝒪 B μ * y ∉ 𝔭 := by
  intro μ ν hμν hmem
  by_cases hν : π ∣ ν
  · have hμ : ¬ π ∣ μ := fun hμ => hμν ⟨hμ, hν⟩
    obtain ⟨c, rfl⟩ := hν
    have h1 : algebraMap 𝒪 B μ * y ∈ 𝔭 := by
      have : algebraMap 𝒪 B μ * y = algebraMap 𝒪 B π * algebraMap 𝒪 B c -
          (algebraMap 𝒪 B (π * c) * 1 - algebraMap 𝒪 B μ * y) := by rw [map_mul]; ring
      rw [this]
      exact 𝔭.sub_mem (𝔭.mul_mem_right _ hπ𝔭) hmem
    rcases h𝔭.mem_or_mem h1 with h | h
    · exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h ((isUnit_of_not_dvd π hπ hμ).map (algebraMap 𝒪 B)))
    · exact hy h
  · apply hyq
    refine pow_pred_sub_one_mem B π hπ q hq hq0 𝔭 h𝔭 hπ𝔭 y ν μ hν ?_
    have : algebraMap 𝒪 B ν - y * algebraMap 𝒪 B μ = algebraMap 𝒪 B ν * 1 - algebraMap 𝒪 B μ * y := by ring
    rw [this]
    exact hmem

theorem stdBasisVec_not_mem_smul (hπu : ¬ IsUnit π) (i : Fin 2) :
    ¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
      ((stdBasisVec (𝒪 := 𝒪) K i : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) =
        (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
  rintro ⟨w, hw⟩
  obtain ⟨c, hc⟩ := w.2 i
  have h1 := congrFun hw i
  change (Pi.single i (1 : K) : Fin 2 → K) i = (algebraMap 𝒪 K π • (w : Fin 2 → K)) i at h1
  rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, ← hc, ← map_mul] at h1
  exact hπu (isUnit_iff_exists_inv.mpr ⟨c, IsFractionRing.injective 𝒪 K (by rw [map_one]; exact h1.symm)⟩)

theorem tmul_snd_mem_of_mem (𝔭 : Ideal B) (a : B) (ha : a ∈ 𝔭) :
    (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 ∈
      Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))) := by
  have : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1 =
      (a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) - a • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; abel
  have hmem : (a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1) - a • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0) ∈
      Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))) :=
    Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul ha Submodule.mem_top))
  rwa [← this] at hmem

theorem tmul_fst_mem_of_mem (𝔭 : Ideal B) (b : B) (hb : b ∈ 𝔭) :
    (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 ∈
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1} ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))) := by
  have : (1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 =
      ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1) - b • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; abel
  have hmem : ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1) - b • ((1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1) ∈
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1} ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K))) :=
    Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul hb Submodule.mem_top))
  rwa [← this] at hmem

theorem not_mem_of_vertexNondegAt_fst (hπu : ¬ IsUnit π) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (a : B)
    (hline : d.line (stdFullLattice (𝒪 := 𝒪) K) =
      Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (hV : d.VertexNondegAt π 𝔭 (stdFullLattice (𝒪 := 𝒪) K)) : a ∉ 𝔭 := by
  intro ha
  refine hV (stdBasisVec K 1) (stdBasisVec_not_mem_smul π hπu 1) ?_
  rw [hline]
  exact tmul_snd_mem_of_mem 𝔭 a ha

theorem not_mem_of_vertexNondegAt_snd (hπu : ¬ IsUnit π) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (b : B)
    (hline : d.line (stdFullLattice (𝒪 := 𝒪) K) =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1})
    (hV : d.VertexNondegAt π 𝔭 (stdFullLattice (𝒪 := 𝒪) K)) : b ∉ 𝔭 := by
  intro hb
  refine hV (stdBasisVec K 0) (stdBasisVec_not_mem_smul π hπu 0) ?_
  rw [hline]
  exact tmul_fst_mem_of_mem 𝔭 b hb

end Dictionary

section Vertices

theorem vertexMk_eq_of_latticeMap_scalarGL_eq {c : Kˣ} {X Y : FullLattice 𝒪 K} (h : latticeMap (scalarGL c) X.1 = Y.1) :
    Vertex.mk 𝒪 K X.1 X.2 = Vertex.mk 𝒪 K Y.1 Y.2 :=
  Vertex.mk_eq_mk_iff.mpr ⟨c, h⟩

theorem vertexMk_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) :
    Vertex.mk 𝒪 K (FullLattice.act g M).1 (FullLattice.act g M).2 = Vertex.act g (Vertex.mk 𝒪 K M.1 M.2) := rfl

theorem vertexMk_std : Vertex.mk 𝒪 K (stdFullLattice (𝒪 := 𝒪) K).1 (stdFullLattice (𝒪 := 𝒪) K).2 = stdVertex 𝒪 K := rfl

theorem act_eq_of_eq_act_inv {k : Matrix.GeneralLinearGroup (Fin 2) K} {s t : Vertex 𝒪 K} (h : Vertex.act k⁻¹ t = s) :
    Vertex.act k s = t := by
  rw [← h, ← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

theorem diag_mul_diagSnd [IsDomain 𝒪] {π : 𝒪} (hπ0 : π ≠ 0) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) :
    g * diagSnd (unitOfNeZero (K := K) hπ0) = scalarGL (unitOfNeZero (K := K) hπ0) := by
  apply Units.ext
  rw [Units.val_mul, hg, diagSnd_coe, scalarGL_coe, unitOfNeZero_coe, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diag_mul_scalarGL_inv_mul_diagSnd [IsDomain 𝒪] {π : 𝒪} (hπ0 : π ≠ 0) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) :
    g * scalarGL (unitOfNeZero (K := K) hπ0)⁻¹ * diagSnd (unitOfNeZero (K := K) hπ0) = 1 := by
  rw [mul_assoc, scalarGL_mul_comm, ← mul_assoc, diag_mul_diagSnd hπ0 g hg, ← scalarGL_mul, mul_inv_cancel,
    scalarGL_one]

end Vertices

section Crossing

variable (π : 𝒪)
variable {B}

theorem vec_eq_smul_add_smul (w : Fin 2 → K) :
    w = w 0 • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) + w 1 • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by
  ext i; fin_cases i <;> simp

theorem mem_of_coord {L : Submodule 𝒪 (Fin 2 → K)} {w f₀ f₁ : Fin 2 → K} (a₀ a₁ : 𝒪)
    (hw : w = algebraMap 𝒪 K a₀ • f₀ + algebraMap 𝒪 K a₁ • f₁) (hf₀ : f₀ ∈ L) (hf₁ : f₁ ∈ L) : w ∈ L := by
  rw [hw, algebraMap_smul, algebraMap_smul]
  exact L.add_mem (L.smul_mem a₀ hf₀) (L.smul_mem a₁ hf₁)

theorem diag_mulVec (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) (w : Fin 2 → K) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = ![algebraMap 𝒪 K π * w 0, w 1] := by
  rw [hg]; ext i; fin_cases i <;> simp [Matrix.mulVec_diagonal]

theorem mem_act_std_iff (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) (v : Fin 2 → K) :
    v ∈ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 ↔
      (∃ a : 𝒪, v 0 = algebraMap 𝒪 K (π * a)) ∧ IsLocalization.IsInteger 𝒪 (v 1) := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
    obtain ⟨a, ha⟩ := hw 0
    refine ⟨⟨a, ?_⟩, ?_⟩
    · rw [diag_mulVec π g hg]; simp [← ha, map_mul]
    · rw [diag_mulVec π g hg]; simpa using hw 1
  · rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    refine mem_latticeMap.mpr ⟨![algebraMap 𝒪 K a, algebraMap 𝒪 K c], ?_, ?_⟩
    · intro i; fin_cases i; exacts [⟨a, rfl⟩, ⟨c, rfl⟩]
    · rw [diag_mulVec π g hg]; ext i; fin_cases i
      · simp [ha, map_mul]
      · simp [hc]

theorem mem_inv_act_std_iff [IsDomain 𝒪] (hπ0 : π ≠ 0) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) (v : Fin 2 → K) :
    v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hπ0)⁻¹) (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 ↔
      IsLocalization.IsInteger 𝒪 (v 0) ∧ IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K π * v 1) := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h => hπ0 (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have hcoe : (((unitOfNeZero (K := K) hπ0)⁻¹ : Kˣ) : K) = (algebraMap 𝒪 K π)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, unitOfNeZero_coe]
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (mem_act_std_iff π g hg w).mp hw
    refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
    · rw [Pi.smul_apply, smul_eq_mul, hcoe, ha, map_mul, inv_mul_cancel_left₀ hπK]
    · rw [Pi.smul_apply, smul_eq_mul, hcoe, mul_inv_cancel_left₀ hπK]; exact hb
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨![algebraMap 𝒪 K (π * a), algebraMap 𝒪 K b], (mem_act_std_iff π g hg _).mpr ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩, ?_⟩
    ext i; fin_cases i
    · change (((unitOfNeZero (K := K) hπ0)⁻¹ : Kˣ) : K) • algebraMap 𝒪 K (π * a) = v 0
      rw [hcoe, smul_eq_mul, map_mul, inv_mul_cancel_left₀ hπK, ha]
    · change (((unitOfNeZero (K := K) hπ0)⁻¹ : Kˣ) : K) • algebraMap 𝒪 K b = v 1
      rw [hcoe, smul_eq_mul, hb, inv_mul_cancel_left₀ hπK]

theorem crossing_top [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (x : B) (hx : x ∈ 𝔭)
    (hline : d.line (stdFullLattice (𝒪 := 𝒪) K) =
      Submodule.span B {x ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (L' L : FullLattice 𝒪 K) (hL : L.1 = (stdFullLattice (𝒪 := 𝒪) K).1) (hE : d.EdgeNondegAt π 𝔭 L' L) :
    L'.1 = (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 := by
  obtain ⟨L₁, hL₁⟩ := L
  change L₁ = stdLattice 𝒪 K at hL
  subst hL
  change d.EdgeNondegAt π 𝔭 L' (stdFullLattice (𝒪 := 𝒪) K) at hE
  obtain ⟨hle, hπL, h1, h2⟩ := hE
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have he₁ := tmul_snd_mem_of_mem (𝒪 := 𝒪) (K := K) 𝔭 x hx
  rw [← hline] at he₁
  have he₁L' : ((stdBasisVec (𝒪 := 𝒪) K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) ∈ L'.1 := by
    by_contra h; exact h1 (stdBasisVec K 1) h he₁
  have he₁L'' : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ∈ L'.1 := he₁L'

  have hdiv : ∀ u : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (u : Fin 2 → K) ∈ L'.1 → π ∣ coordEquiv u 0 := by
    intro u hu
    by_contra hndvd
    obtain ⟨a, ha⟩ := isUnit_of_not_dvd π hπ hndvd
    have h0 := algebraMap_coordEquiv u 0
    have h1' := algebraMap_coordEquiv u 1
    have hinv : algebraMap 𝒪 K ↑a⁻¹ * algebraMap 𝒪 K (coordEquiv u 0) = 1 := by
      rw [← map_mul, ← ha, Units.inv_mul, map_one]
    have he₀L' : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ∈ L'.1 := by
      have : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
          algebraMap 𝒪 K ↑a⁻¹ • ((u : Fin 2 → K) -
            algebraMap 𝒪 K (coordEquiv u 1) • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)) := by
        ext i; fin_cases i
        · change (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0 = algebraMap 𝒪 K ↑a⁻¹ *
            ((u : Fin 2 → K) 0 - algebraMap 𝒪 K (coordEquiv u 1) * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0)
          rw [Pi.single_eq_same, Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), mul_zero, sub_zero, ← h0, hinv]
        · change (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1 = algebraMap 𝒪 K ↑a⁻¹ *
            ((u : Fin 2 → K) 1 - algebraMap 𝒪 K (coordEquiv u 1) * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1)
          rw [Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), Pi.single_eq_same, mul_one, ← h1', sub_self, mul_zero]
      rw [this, algebraMap_smul]
      exact L'.1.smul_mem _ (L'.1.sub_mem hu (by rw [algebraMap_smul]; exact L'.1.smul_mem _ he₁L''))
    have hge : (stdFullLattice (𝒪 := 𝒪) K).1 ≤ L'.1 := by
      intro w hw
      exact mem_of_coord (coordEquiv ⟨w, hw⟩ 0) (coordEquiv ⟨w, hw⟩ 1)
        (by rw [algebraMap_coordEquiv, algebraMap_coordEquiv]; exact vec_eq_smul_add_smul w) he₀L' he₁L''
    obtain ⟨L'₁, hL'₁⟩ := L'
    obtain rfl : L'₁ = stdLattice 𝒪 K := le_antisymm hle hge
    exact h2 (stdBasisVec K 1) (stdBasisVec_not_mem_smul π hπu 1) he₁
  apply le_antisymm
  · intro u hu
    obtain ⟨c, hc⟩ := hdiv ⟨u, hle hu⟩ hu
    refine (mem_act_std_iff π g hg u).mpr ⟨⟨c, ?_⟩, (hle hu) 1⟩
    rw [← hc, algebraMap_coordEquiv]
  · intro v hv
    obtain ⟨⟨c, hc⟩, ⟨b, hb⟩⟩ := (mem_act_std_iff π g hg v).mp hv
    have : v = algebraMap 𝒪 K b • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) +
        algebraMap 𝒪 K π • (algebraMap 𝒪 K c • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K)) := by
      ext i; fin_cases i
      · change v 0 = algebraMap 𝒪 K b * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0 +
          algebraMap 𝒪 K π * (algebraMap 𝒪 K c * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0)
        rw [Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), Pi.single_eq_same, mul_zero, zero_add, mul_one,
          ← map_mul, hc]
      · change v 1 = algebraMap 𝒪 K b * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1 +
          algebraMap 𝒪 K π * (algebraMap 𝒪 K c * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1)
        rw [Pi.single_eq_same, Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), mul_one, mul_zero, mul_zero,
          add_zero, hb]
    rw [this, algebraMap_smul]
    refine L'.1.add_mem (L'.1.smul_mem _ he₁L'') ?_
    have hmem : algebraMap 𝒪 K c • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ∈ (stdFullLattice (𝒪 := 𝒪) K).1 := by
      rw [algebraMap_smul]; exact (stdFullLattice (𝒪 := 𝒪) K).1.smul_mem c (single_one_mem_stdLattice 𝒪 K 0)
    exact hπL ⟨_, hmem⟩

theorem crossing_bot [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (x : B) (hx : x ∈ 𝔭)
    (hline : d.line (stdFullLattice (𝒪 := 𝒪) K) =
      Submodule.span B {x ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (L' L : FullLattice 𝒪 K) (hL' : L'.1 = (stdFullLattice (𝒪 := 𝒪) K).1) (hE : d.EdgeNondegAt π 𝔭 L' L) :
    L.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹) (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 := by
  obtain ⟨L'₁, hL'₁⟩ := L'
  change L'₁ = stdLattice 𝒪 K at hL'
  subst hL'
  change d.EdgeNondegAt π 𝔭 (stdFullLattice (𝒪 := 𝒪) K) L at hE
  obtain ⟨hle, hπL, h1, h2⟩ := hE
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have hcoe : (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) = (algebraMap 𝒪 K π)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, unitOfNeZero_coe]
  have he₁ := tmul_snd_mem_of_mem (𝒪 := 𝒪) (K := K) 𝔭 x hx
  rw [← hline] at he₁

  have hf : ∃ w : ↥L.1, ((stdBasisVec (𝒪 := 𝒪) K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) =
      algebraMap 𝒪 K π • (w : Fin 2 → K) := by
    by_contra h; exact h2 (stdBasisVec K 1) h he₁
  obtain ⟨f, hf⟩ := hf
  change (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) = algebraMap 𝒪 K π • (f : Fin 2 → K) at hf
  have hf0 : (f : Fin 2 → K) 0 = 0 := by
    have := congrFun hf 0
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1)] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hπK
    · exact h
  have hf1 : (f : Fin 2 → K) 1 = (algebraMap 𝒪 K π)⁻¹ := by
    have := congrFun hf 1
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have he₀L : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ∈ L.1 := hle (single_one_mem_stdLattice 𝒪 K 0)

  have hint : ∀ v : ↥L.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K π * (v : Fin 2 → K) i) := by
    intro v i
    have := hπL v i
    rwa [Pi.smul_apply, smul_eq_mul] at this

  have hint0 : ∀ v : ↥L.1, IsLocalization.IsInteger 𝒪 ((v : Fin 2 → K) 0) := by
    intro v
    obtain ⟨a₀, ha₀⟩ := hint v 0
    obtain ⟨a₁, ha₁⟩ := hint v 1
    have hv0 : (v : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ * algebraMap 𝒪 K a₀ := by rw [ha₀, inv_mul_cancel_left₀ hπK]
    have hv1 : (v : Fin 2 → K) 1 = (algebraMap 𝒪 K π)⁻¹ * algebraMap 𝒪 K a₁ := by rw [ha₁, inv_mul_cancel_left₀ hπK]
    by_contra hv0i
    have hndvd : ¬ π ∣ a₀ := by
      rintro ⟨c, rfl⟩
      apply hv0i
      exact ⟨c, by rw [hv0, map_mul, inv_mul_cancel_left₀ hπK]⟩
    obtain ⟨a, ha⟩ := isUnit_of_not_dvd π hπ hndvd
    have hinvK : algebraMap 𝒪 K ↑a⁻¹ * algebraMap 𝒪 K a₀ = 1 := by
      rw [← map_mul, ← ha, Units.inv_mul, map_one]

    have hf₀L : (algebraMap 𝒪 K π)⁻¹ • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ∈ L.1 := by
      have : (algebraMap 𝒪 K π)⁻¹ • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) =
          algebraMap 𝒪 K ↑a⁻¹ • ((v : Fin 2 → K) - algebraMap 𝒪 K a₁ • (f : Fin 2 → K)) := by
        ext i; fin_cases i
        · change (algebraMap 𝒪 K π)⁻¹ * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0 =
            algebraMap 𝒪 K ↑a⁻¹ * ((v : Fin 2 → K) 0 - algebraMap 𝒪 K a₁ * (f : Fin 2 → K) 0)
          rw [Pi.single_eq_same, mul_one, hf0, mul_zero, sub_zero, hv0, mul_left_comm, hinvK, mul_one]
        · change (algebraMap 𝒪 K π)⁻¹ * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1 =
            algebraMap 𝒪 K ↑a⁻¹ * ((v : Fin 2 → K) 1 - algebraMap 𝒪 K a₁ * (f : Fin 2 → K) 1)
          rw [Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), mul_zero, hv1, hf1, mul_comm (algebraMap 𝒪 K a₁),
            sub_self, mul_zero]
      rw [this, algebraMap_smul]
      exact L.1.smul_mem _ (L.1.sub_mem v.2 (by rw [algebraMap_smul]; exact L.1.smul_mem _ f.2))

    have hLeq : L.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹) (stdLattice 𝒪 K) := by
      apply le_antisymm
      · intro w hw
        rw [mem_latticeMap_scalarGL]
        obtain ⟨b₀, hb₀⟩ := hint ⟨w, hw⟩ 0
        obtain ⟨b₁, hb₁⟩ := hint ⟨w, hw⟩ 1
        refine ⟨![algebraMap 𝒪 K b₀, algebraMap 𝒪 K b₁], ?_, ?_⟩
        · intro i; fin_cases i; exacts [⟨b₀, rfl⟩, ⟨b₁, rfl⟩]
        · ext i; fin_cases i
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * algebraMap 𝒪 K b₀ = w 0
            rw [hcoe, hb₀, inv_mul_cancel_left₀ hπK]
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * algebraMap 𝒪 K b₁ = w 1
            rw [hcoe, hb₁, inv_mul_cancel_left₀ hπK]
      · intro w hw
        rw [mem_latticeMap_scalarGL] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        obtain ⟨b₀, hb₀⟩ := hw' 0
        obtain ⟨b₁, hb₁⟩ := hw' 1
        have : (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) • w' =
            algebraMap 𝒪 K b₀ • ((algebraMap 𝒪 K π)⁻¹ • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K)) +
            algebraMap 𝒪 K b₁ • (f : Fin 2 → K) := by
          ext i; fin_cases i
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * w' 0 =
              algebraMap 𝒪 K b₀ * ((algebraMap 𝒪 K π)⁻¹ * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0) +
              algebraMap 𝒪 K b₁ * (f : Fin 2 → K) 0
            rw [hcoe, Pi.single_eq_same, hf0, ← hb₀]; ring
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * w' 1 =
              algebraMap 𝒪 K b₀ * ((algebraMap 𝒪 K π)⁻¹ * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1) +
              algebraMap 𝒪 K b₁ * (f : Fin 2 → K) 1
            rw [hcoe, Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), hf1, ← hb₁]; ring
        rw [this]
        exact mem_of_coord b₀ b₁ rfl hf₀L f.2

    have hT : (FullLattice.act (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹) (stdFullLattice (𝒪 := 𝒪) K)).1 = L.1 :=
      hLeq.symm
    have hfval : (f : Fin 2 → K) =
        Matrix.mulVec ((scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          ((stdBasisVec (𝒪 := 𝒪) K 1 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) := by
      rw [scalarGL_mulVec]
      ext i; fin_cases i
      · change (f : Fin 2 → K) 0 = (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0
        rw [hf0, Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), mul_zero]
      · change (f : Fin 2 → K) 1 = (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1
        rw [Pi.single_eq_same, mul_one, hcoe, hf1]
    have hfnot : (f : Fin 2 → K) ∉ (stdFullLattice (𝒪 := 𝒪) K).1 := by
      intro hfm
      obtain ⟨c, hc⟩ := hfm 1
      rw [hf1] at hc
      apply hπu
      exact isUnit_iff_exists_inv.mpr ⟨c, IsFractionRing.injective 𝒪 K (by rw [map_mul, hc, mul_inv_cancel₀ hπK, map_one])⟩
    apply h1 f hfnot
    have key : (1 : B) ⊗ₜ[𝒪] f = transportEquiv B hT (actBaseChange B (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹)
        (stdFullLattice (𝒪 := 𝒪) K) ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 1)) := by
      have hv : f = LinearEquiv.ofEq _ _ hT
          (latticeMapEquiv (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹) (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 1)) := by
        apply Subtype.ext; rw [coe_ofEq_apply, coe_latticeMapEquiv_apply]; exact hfval
      rw [hv]; rfl
    rw [key, DeligneDatum.line_transport π d hT, d.homothety (unitOfNeZero (K := K) hπ.ne_zero)⁻¹ (stdFullLattice (𝒪 := 𝒪) K)]
    exact map_mem_sup_smul_top _ _ 𝔭 (map_mem_sup_smul_top _ _ 𝔭 he₁)

  apply le_antisymm
  · intro v hv
    rw [mem_inv_act_std_iff π hπ.ne_zero g hg]
    exact ⟨hint0 ⟨v, hv⟩, hint ⟨v, hv⟩ 1⟩
  · intro v hv
    rw [mem_inv_act_std_iff π hπ.ne_zero g hg] at hv
    obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := hv
    have hv1 : v 1 = (algebraMap 𝒪 K π)⁻¹ * algebraMap 𝒪 K b₁ := by rw [hb₁, inv_mul_cancel_left₀ hπK]
    have : v = algebraMap 𝒪 K b₀ • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) + algebraMap 𝒪 K b₁ • (f : Fin 2 → K) := by
      ext i; fin_cases i
      · change v 0 = algebraMap 𝒪 K b₀ * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0 + algebraMap 𝒪 K b₁ * (f : Fin 2 → K) 0
        rw [Pi.single_eq_same, hf0, ← hb₀]; ring
      · change v 1 = algebraMap 𝒪 K b₀ * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1 + algebraMap 𝒪 K b₁ * (f : Fin 2 → K) 1
        rw [Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), hf1, hv1]; ring
    rw [this]
    exact mem_of_coord b₀ b₁ rfl he₀L f.2

theorem mem_diagSnd_std_iff [IsDomain 𝒪] (hπ0 : π ≠ 0) (v : Fin 2 → K) :
    v ∈ latticeMap (diagSnd (unitOfNeZero (K := K) hπ0)) (stdLattice 𝒪 K) ↔
      IsLocalization.IsInteger 𝒪 (v 0) ∧ IsLocalization.IsInteger 𝒪 ((algebraMap 𝒪 K π)⁻¹ * v 1) := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h => hπ0 (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  rw [mem_latticeMap_diagSnd_stdLattice, unitOfNeZero_coe]
  constructor
  · rintro ⟨h0, w, hw, hw'⟩
    refine ⟨h0, ?_⟩
    rw [← hw', inv_mul_cancel_left₀ hπK]; exact hw
  · rintro ⟨h0, h1⟩
    exact ⟨h0, _, h1, by rw [mul_inv_cancel_left₀ hπK]⟩

theorem mem_inv_diagSnd_std_iff [IsDomain 𝒪] (hπ0 : π ≠ 0) (v : Fin 2 → K) :
    v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hπ0)⁻¹) (latticeMap (diagSnd (unitOfNeZero (K := K) hπ0)) (stdLattice 𝒪 K)) ↔
      IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K π * v 0) ∧ IsLocalization.IsInteger 𝒪 (v 1) := by
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h => hπ0 (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have hcoe : (((unitOfNeZero (K := K) hπ0)⁻¹ : Kˣ) : K) = (algebraMap 𝒪 K π)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, unitOfNeZero_coe]
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h0, h1⟩ := (mem_diagSnd_std_iff π hπ0 w).mp hw
    refine ⟨?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, hcoe, mul_inv_cancel_left₀ hπK]; exact h0
    · rw [Pi.smul_apply, smul_eq_mul, hcoe]; exact h1
  · rintro ⟨h0, h1⟩
    refine ⟨algebraMap 𝒪 K π • v, (mem_diagSnd_std_iff π hπ0 _).mpr ⟨?_, ?_⟩, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]; exact h0
    · rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hπK]; exact h1
    · rw [hcoe, smul_smul, inv_mul_cancel₀ hπK, one_smul]

theorem crossing_top' [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (hπ : Irreducible π)
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (y : B) (hy : y ∈ 𝔭)
    (hline : d.line (stdFullLattice (𝒪 := 𝒪) K) =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + y ⊗ₜ[𝒪] stdBasisVec K 1})
    (L' L : FullLattice 𝒪 K) (hL : L.1 = (stdFullLattice (𝒪 := 𝒪) K).1) (hE : d.EdgeNondegAt π 𝔭 L' L) :
    L'.1 = latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) := by
  obtain ⟨L₁, hL₁⟩ := L
  change L₁ = stdLattice 𝒪 K at hL
  subst hL
  change d.EdgeNondegAt π 𝔭 L' (stdFullLattice (𝒪 := 𝒪) K) at hE
  obtain ⟨hle, hπL, h1, h2⟩ := hE
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have he₀ := tmul_fst_mem_of_mem (𝒪 := 𝒪) (K := K) 𝔭 y hy
  rw [← hline] at he₀
  have he₀L' : ((stdBasisVec (𝒪 := 𝒪) K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) ∈ L'.1 := by
    by_contra h; exact h1 (stdBasisVec K 0) h he₀
  have he₀L'' : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ∈ L'.1 := he₀L'

  have hdiv : ∀ u : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (u : Fin 2 → K) ∈ L'.1 → π ∣ coordEquiv u 1 := by
    intro u hu
    by_contra hndvd
    obtain ⟨a, ha⟩ := isUnit_of_not_dvd π hπ hndvd
    have h0 := algebraMap_coordEquiv u 0
    have h1' := algebraMap_coordEquiv u 1
    have hinv : algebraMap 𝒪 K ↑a⁻¹ * algebraMap 𝒪 K (coordEquiv u 1) = 1 := by
      rw [← map_mul, ← ha, Units.inv_mul, map_one]
    have he₁L' : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ∈ L'.1 := by
      have : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
          algebraMap 𝒪 K ↑a⁻¹ • ((u : Fin 2 → K) -
            algebraMap 𝒪 K (coordEquiv u 0) • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K)) := by
        ext i; fin_cases i
        · change (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0 = algebraMap 𝒪 K ↑a⁻¹ *
            ((u : Fin 2 → K) 0 - algebraMap 𝒪 K (coordEquiv u 0) * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0)
          rw [Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), Pi.single_eq_same, mul_one, ← h0, sub_self, mul_zero]
        · change (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1 = algebraMap 𝒪 K ↑a⁻¹ *
            ((u : Fin 2 → K) 1 - algebraMap 𝒪 K (coordEquiv u 0) * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1)
          rw [Pi.single_eq_same, Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), mul_zero, sub_zero, ← h1', hinv]
      rw [this, algebraMap_smul]
      exact L'.1.smul_mem _ (L'.1.sub_mem hu (by rw [algebraMap_smul]; exact L'.1.smul_mem _ he₀L''))
    have hge : (stdFullLattice (𝒪 := 𝒪) K).1 ≤ L'.1 := by
      intro w hw
      exact mem_of_coord (coordEquiv ⟨w, hw⟩ 0) (coordEquiv ⟨w, hw⟩ 1)
        (by rw [algebraMap_coordEquiv, algebraMap_coordEquiv]; exact vec_eq_smul_add_smul w) he₀L'' he₁L'
    obtain ⟨L'₁, hL'₁⟩ := L'
    obtain rfl : L'₁ = stdLattice 𝒪 K := le_antisymm hle hge
    exact h2 (stdBasisVec K 0) (stdBasisVec_not_mem_smul π hπu 0) he₀
  apply le_antisymm
  · intro u hu
    obtain ⟨c, hc⟩ := hdiv ⟨u, hle hu⟩ hu
    refine (mem_diagSnd_std_iff π hπ.ne_zero u).mpr ⟨(hle hu) 0, ⟨c, ?_⟩⟩
    have hu1 : u 1 = algebraMap 𝒪 K (π * c) := by
      rw [← hc]; exact (algebraMap_coordEquiv (⟨u, hle hu⟩ : ↥(stdFullLattice (𝒪 := 𝒪) K).1) 1).symm
    rw [hu1, map_mul, inv_mul_cancel_left₀ hπK]
  · intro v hv
    obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := (mem_diagSnd_std_iff π hπ.ne_zero v).mp hv
    have hv1 : v 1 = algebraMap 𝒪 K π * algebraMap 𝒪 K c := by rw [hc, mul_inv_cancel_left₀ hπK]
    have : v = algebraMap 𝒪 K b • (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) +
        algebraMap 𝒪 K π • (algebraMap 𝒪 K c • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)) := by
      ext i; fin_cases i
      · change v 0 = algebraMap 𝒪 K b * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0 +
          algebraMap 𝒪 K π * (algebraMap 𝒪 K c * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0)
        rw [Pi.single_eq_same, Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), mul_one, mul_zero, mul_zero,
          add_zero, hb]
      · change v 1 = algebraMap 𝒪 K b * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1 +
          algebraMap 𝒪 K π * (algebraMap 𝒪 K c * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1)
        rw [Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), Pi.single_eq_same, mul_zero, zero_add, mul_one, hv1]
    rw [this, algebraMap_smul]
    refine L'.1.add_mem (L'.1.smul_mem _ he₀L'') ?_
    have hmem : algebraMap 𝒪 K c • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ∈ (stdFullLattice (𝒪 := 𝒪) K).1 := by
      rw [algebraMap_smul]; exact (stdFullLattice (𝒪 := 𝒪) K).1.smul_mem c (single_one_mem_stdLattice 𝒪 K 1)
    exact hπL ⟨_, hmem⟩

theorem crossing_bot' [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (hπ : Irreducible π)
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (y : B) (hy : y ∈ 𝔭)
    (hline : d.line (stdFullLattice (𝒪 := 𝒪) K) =
      Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + y ⊗ₜ[𝒪] stdBasisVec K 1})
    (L' L : FullLattice 𝒪 K) (hL' : L'.1 = (stdFullLattice (𝒪 := 𝒪) K).1) (hE : d.EdgeNondegAt π 𝔭 L' L) :
    L.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K)) := by
  obtain ⟨L'₁, hL'₁⟩ := L'
  change L'₁ = stdLattice 𝒪 K at hL'
  subst hL'
  change d.EdgeNondegAt π 𝔭 (stdFullLattice (𝒪 := 𝒪) K) L at hE
  obtain ⟨hle, hπL, h1, h2⟩ := hE
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have hcoe : (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) = (algebraMap 𝒪 K π)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, unitOfNeZero_coe]
  have he₀ := tmul_fst_mem_of_mem (𝒪 := 𝒪) (K := K) 𝔭 y hy
  rw [← hline] at he₀

  have hf : ∃ w : ↥L.1, ((stdBasisVec (𝒪 := 𝒪) K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) =
      algebraMap 𝒪 K π • (w : Fin 2 → K) := by
    by_contra h; exact h2 (stdBasisVec K 0) h he₀
  obtain ⟨f, hf⟩ := hf
  change (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) = algebraMap 𝒪 K π • (f : Fin 2 → K) at hf
  have hf1 : (f : Fin 2 → K) 1 = 0 := by
    have := congrFun hf 1
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0)] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hπK
    · exact h
  have hf0 : (f : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ := by
    have := congrFun hf 0
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have he₁L : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ∈ L.1 := hle (single_one_mem_stdLattice 𝒪 K 1)
  have hint : ∀ v : ↥L.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K π * (v : Fin 2 → K) i) := by
    intro v i
    have := hπL v i
    rwa [Pi.smul_apply, smul_eq_mul] at this

  have hint1 : ∀ v : ↥L.1, IsLocalization.IsInteger 𝒪 ((v : Fin 2 → K) 1) := by
    intro v
    obtain ⟨a₀, ha₀⟩ := hint v 0
    obtain ⟨a₁, ha₁⟩ := hint v 1
    have hv0 : (v : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ * algebraMap 𝒪 K a₀ := by rw [ha₀, inv_mul_cancel_left₀ hπK]
    have hv1 : (v : Fin 2 → K) 1 = (algebraMap 𝒪 K π)⁻¹ * algebraMap 𝒪 K a₁ := by rw [ha₁, inv_mul_cancel_left₀ hπK]
    by_contra hv1i
    have hndvd : ¬ π ∣ a₁ := by
      rintro ⟨c, rfl⟩
      apply hv1i
      exact ⟨c, by rw [hv1, map_mul, inv_mul_cancel_left₀ hπK]⟩
    obtain ⟨a, ha⟩ := isUnit_of_not_dvd π hπ hndvd
    have hinvK : algebraMap 𝒪 K ↑a⁻¹ * algebraMap 𝒪 K a₁ = 1 := by
      rw [← map_mul, ← ha, Units.inv_mul, map_one]

    have hf₁L : (algebraMap 𝒪 K π)⁻¹ • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ∈ L.1 := by
      have : (algebraMap 𝒪 K π)⁻¹ • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) =
          algebraMap 𝒪 K ↑a⁻¹ • ((v : Fin 2 → K) - algebraMap 𝒪 K a₀ • (f : Fin 2 → K)) := by
        ext i; fin_cases i
        · change (algebraMap 𝒪 K π)⁻¹ * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0 =
            algebraMap 𝒪 K ↑a⁻¹ * ((v : Fin 2 → K) 0 - algebraMap 𝒪 K a₀ * (f : Fin 2 → K) 0)
          rw [Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), mul_zero, hv0, hf0, mul_comm (algebraMap 𝒪 K a₀),
            sub_self, mul_zero]
        · change (algebraMap 𝒪 K π)⁻¹ * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1 =
            algebraMap 𝒪 K ↑a⁻¹ * ((v : Fin 2 → K) 1 - algebraMap 𝒪 K a₀ * (f : Fin 2 → K) 1)
          rw [Pi.single_eq_same, mul_one, hf1, mul_zero, sub_zero, hv1, mul_left_comm, hinvK, mul_one]
      rw [this, algebraMap_smul]
      exact L.1.smul_mem _ (L.1.sub_mem v.2 (by rw [algebraMap_smul]; exact L.1.smul_mem _ f.2))

    have hLeq : L.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹) (stdLattice 𝒪 K) := by
      apply le_antisymm
      · intro w hw
        rw [mem_latticeMap_scalarGL]
        obtain ⟨b₀, hb₀⟩ := hint ⟨w, hw⟩ 0
        obtain ⟨b₁, hb₁⟩ := hint ⟨w, hw⟩ 1
        refine ⟨![algebraMap 𝒪 K b₀, algebraMap 𝒪 K b₁], ?_, ?_⟩
        · intro i; fin_cases i; exacts [⟨b₀, rfl⟩, ⟨b₁, rfl⟩]
        · ext i; fin_cases i
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * algebraMap 𝒪 K b₀ = w 0
            rw [hcoe, hb₀, inv_mul_cancel_left₀ hπK]
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * algebraMap 𝒪 K b₁ = w 1
            rw [hcoe, hb₁, inv_mul_cancel_left₀ hπK]
      · intro w hw
        rw [mem_latticeMap_scalarGL] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        obtain ⟨b₀, hb₀⟩ := hw' 0
        obtain ⟨b₁, hb₁⟩ := hw' 1
        have : (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) • w' =
            algebraMap 𝒪 K b₀ • (f : Fin 2 → K) +
            algebraMap 𝒪 K b₁ • ((algebraMap 𝒪 K π)⁻¹ • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K)) := by
          ext i; fin_cases i
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * w' 0 =
              algebraMap 𝒪 K b₀ * (f : Fin 2 → K) 0 +
              algebraMap 𝒪 K b₁ * ((algebraMap 𝒪 K π)⁻¹ * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0)
            rw [hcoe, Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), hf0, ← hb₀]; ring
          · change (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * w' 1 =
              algebraMap 𝒪 K b₀ * (f : Fin 2 → K) 1 +
              algebraMap 𝒪 K b₁ * ((algebraMap 𝒪 K π)⁻¹ * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1)
            rw [hcoe, Pi.single_eq_same, hf1, ← hb₁]; ring
        rw [this]
        exact mem_of_coord b₀ b₁ rfl f.2 hf₁L

    have hT : (FullLattice.act (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹) (stdFullLattice (𝒪 := 𝒪) K)).1 = L.1 :=
      hLeq.symm
    have hfval : (f : Fin 2 → K) =
        Matrix.mulVec ((scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          ((stdBasisVec (𝒪 := 𝒪) K 0 : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) := by
      rw [scalarGL_mulVec]
      ext i; fin_cases i
      · change (f : Fin 2 → K) 0 = (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 0
        rw [Pi.single_eq_same, mul_one, hcoe, hf0]
      · change (f : Fin 2 → K) 1 = (((unitOfNeZero (K := K) hπ.ne_zero)⁻¹ : Kˣ) : K) * (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) 1
        rw [hf1, Pi.single_eq_of_ne (one_ne_zero : (1 : Fin 2) ≠ 0), mul_zero]
    have hfnot : (f : Fin 2 → K) ∉ (stdFullLattice (𝒪 := 𝒪) K).1 := by
      intro hfm
      obtain ⟨c, hc⟩ := hfm 0
      rw [hf0] at hc
      apply hπu
      exact isUnit_iff_exists_inv.mpr ⟨c, IsFractionRing.injective 𝒪 K (by rw [map_mul, hc, mul_inv_cancel₀ hπK, map_one])⟩
    apply h1 f hfnot
    have key : (1 : B) ⊗ₜ[𝒪] f = transportEquiv B hT (actBaseChange B (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹)
        (stdFullLattice (𝒪 := 𝒪) K) ((1 : B) ⊗ₜ[𝒪] stdBasisVec K 0)) := by
      have hv : f = LinearEquiv.ofEq _ _ hT
          (latticeMapEquiv (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)⁻¹) (stdFullLattice (𝒪 := 𝒪) K).1 (stdBasisVec K 0)) := by
        apply Subtype.ext; rw [coe_ofEq_apply, coe_latticeMapEquiv_apply]; exact hfval
      rw [hv]; rfl
    rw [key, DeligneDatum.line_transport π d hT, d.homothety (unitOfNeZero (K := K) hπ.ne_zero)⁻¹ (stdFullLattice (𝒪 := 𝒪) K)]
    exact map_mem_sup_smul_top _ _ 𝔭 (map_mem_sup_smul_top _ _ 𝔭 he₀)

  apply le_antisymm
  · intro v hv
    rw [mem_inv_diagSnd_std_iff π hπ.ne_zero]
    exact ⟨hint ⟨v, hv⟩ 0, hint1 ⟨v, hv⟩⟩
  · intro v hv
    rw [mem_inv_diagSnd_std_iff π hπ.ne_zero] at hv
    obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := hv
    have hv0 : v 0 = (algebraMap 𝒪 K π)⁻¹ * algebraMap 𝒪 K b₀ := by rw [hb₀, inv_mul_cancel_left₀ hπK]
    have : v = algebraMap 𝒪 K b₀ • (f : Fin 2 → K) + algebraMap 𝒪 K b₁ • (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) := by
      ext i; fin_cases i
      · change v 0 = algebraMap 𝒪 K b₀ * (f : Fin 2 → K) 0 + algebraMap 𝒪 K b₁ * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 0
        rw [Pi.single_eq_of_ne (zero_ne_one : (0 : Fin 2) ≠ 1), hf0, hv0]; ring
      · change v 1 = algebraMap 𝒪 K b₀ * (f : Fin 2 → K) 1 + algebraMap 𝒪 K b₁ * (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) 1
        rw [Pi.single_eq_same, hf1, ← hb₁]; ring
    rw [this]
    exact mem_of_coord b₀ b₁ rfl f.2 he₁L

end Crossing

end CerednikDrinfeld.FormalOmega.ChartIncidence

end

open CerednikDrinfeld.FormalOmega.ChartIncidence in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B)
    (hd : (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hd' : (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (k : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hk : DeligneDatum.IsPullback (K := K₀) (π := π) B k⁻¹ d d') :
    ((Vertex.act k (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act k (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀))) ∨
    (Vertex.act k (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) ∨
    (Vertex.act k (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)))) ∨
    (Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) ∨
    (Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)))) := by
  classical
  haveI := hdvr
  have hr0 : 0 < r := (Fact.out : r.Prime).pos
  have hπu : ¬ IsUnit π := hπ.not_isUnit

  let φ : chartERing 𝒪 π r →ₐ[𝒪] B :=
    xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))
  let φ' : chartERing 𝒪 π r →ₐ[𝒪] B :=
    xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))

  have hrel : ∀ ψ : chartERing 𝒪 π r →ₐ[𝒪] B,
      ψ (chartERing.ξ 𝒪 π r) * ψ (chartERing.η 𝒪 π r) = algebraMap 𝒪 B π ∧
      IsUnit (ψ (chartERing.ξ 𝒪 π r) ^ (r - 1) - 1) ∧ IsUnit (ψ (chartERing.η 𝒪 π r) ^ (r - 1) - 1) := by
    intro ψ
    have h := (chartERing.isUnit_discr 𝒪 π r).map ψ
    rw [map_mul, map_sub, map_sub, map_pow, map_pow, map_one] at h
    exact ⟨by rw [← map_mul, chartERing.ξ_mul_η, AlgHom.commutes], isUnit_of_mul_isUnit_left h,
      isUnit_of_mul_isUnit_right h⟩
  obtain ⟨-, hxq, hyq⟩ := hrel φ

  have hπnil : (algebraMap 𝒪 B π) ^ (n + 1) = 0 := by
    rw [← φ.commutes π, ← map_pow]
    show xq (Ideal.Quotient.mkₐ 𝒪 _ ((algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1))) = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)),
      map_zero]
  have h𝔪p : (IsLocalRing.maximalIdeal B).IsPrime := (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  haveI : (IsLocalRing.maximalIdeal B).IsPrime := h𝔪p
  have unit_iff : ∀ z : B, IsUnit z ↔ z ∉ IsLocalRing.maximalIdeal B := fun z => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hπ𝔪 : algebraMap 𝒪 B π ∈ IsLocalRing.maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (hu.pow (n + 1)).ne_zero hπnil

  have hdE := hd.2.2 _ h𝔪p
  have hd'E := hd'.2.2 _ h𝔪p
  have hd'eq : d' = DeligneDatum.pullback π B k⁻¹ d := eq_pullback_of_isPullback π hk
  have hdeq : d = DeligneDatum.pullback π B k d' := by rw [hd'eq, pullback_pullback_inv]

  have hEk : d.EdgeNondegAt π (IsLocalRing.maximalIdeal B)
      (FullLattice.act k⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀))) (FullLattice.act k⁻¹ (stdFullLattice (𝒪 := 𝒪) K₀)) := by
    have h := DeligneDatum.edgeNondegAt_pullback_act_inv π d' k (IsLocalRing.maximalIdeal B) _ _ hd'E
    rwa [← hdeq] at h

  have vtx : ∀ (c : K₀ˣ) (X Z : FullLattice 𝒪 K₀), latticeMap (scalarGL c) X.1 = (FullLattice.act k⁻¹ Z).1 →
      Vertex.act k (Vertex.mk 𝒪 K₀ X.1 X.2) = Vertex.mk 𝒪 K₀ Z.1 Z.2 := by
    intro c X Z hc
    apply act_eq_of_eq_act_inv
    rw [← vertexMk_act]
    exact (vertexMk_eq_of_latticeMap_scalarGL_eq hc).symm

  have toD' : ∀ Z : FullLattice 𝒪 K₀, d.VertexNondegAt π (IsLocalRing.maximalIdeal B) (FullLattice.act k⁻¹ Z) →
      d'.VertexNondegAt π (IsLocalRing.maximalIdeal B) Z := by
    intro Z hV
    have h := vertexNondegAt_pullback π d k⁻¹ (IsLocalRing.maximalIdeal B) _ hV
    rw [← hd'eq] at h
    exact vertexNondegAt_congr π d' _ (latticeMap_inv_latticeMap k⁻¹ Z.1) h

  have unit_x' : d'.VertexNondegAt π (IsLocalRing.maximalIdeal B) (stdFullLattice (𝒪 := 𝒪) K₀) →
      IsUnit (φ' (chartERing.ξ 𝒪 π r)) := fun hV =>
    (unit_iff _).mpr (not_mem_of_vertexNondegAt_fst π hπu d' _ _ hd'.1 hV)
  have unit_y' : d'.VertexNondegAt π (IsLocalRing.maximalIdeal B) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)) →
      IsUnit (φ' (chartERing.η 𝒪 π r)) := fun hV => by
    have h := vertexNondegAt_pullback π d' g₁ (IsLocalRing.maximalIdeal B) _ hV
    have h' : (DeligneDatum.pullback π B g₁ d').VertexNondegAt π (IsLocalRing.maximalIdeal B) (stdFullLattice (𝒪 := 𝒪) K₀) :=
      vertexNondegAt_congr π _ _ (latticeMap_inv_latticeMap g₁ _) h
    exact (unit_iff _).mpr (not_mem_of_vertexNondegAt_snd π hπu _ _ _ (line_pullback_std π d' g₁ _ hd'.2.1) h')
  by_cases hxU : IsUnit (φ (chartERing.ξ 𝒪 π r))
  ·
    have hV : d.VertexNondegAt π (IsLocalRing.maximalIdeal B) (stdFullLattice (𝒪 := 𝒪) K₀) :=
      vertexNondegAt_std_of_line_eq π d _ _ 1 hd.1
        (hab_fst π hπ r hres hr0 _ h𝔪p hπ𝔪 _ ((unit_iff _).mp hxU) ((unit_iff _).mp hxq))
    obtain ⟨c, hc⟩ := DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt hπ d
      (IsLocalRing.maximalIdeal B) hπ𝔪 (stdFullLattice (𝒪 := 𝒪) K₀) _ _ hV hEk
    have hVc := vertexNondegAt_act_scalarGL π d (IsLocalRing.maximalIdeal B) (stdFullLattice (𝒪 := 𝒪) K₀) c hV
    rcases hc with hc | hc
    · have hks : Vertex.act k (stdVertex 𝒪 K₀) = Vertex.act g₁ (stdVertex 𝒪 K₀) := vtx c _ _ hc
      have hV' := toD' _ (vertexNondegAt_congr π d _ hc hVc)
      exact Or.inr (Or.inr (Or.inl ⟨hks, hxU, unit_y' hV'⟩))
    · have hks : Vertex.act k (stdVertex 𝒪 K₀) = stdVertex 𝒪 K₀ := vtx c _ _ hc
      have hV' := toD' _ (vertexNondegAt_congr π d _ hc hVc)
      exact Or.inr (Or.inl ⟨hks, hxU, unit_x' hV'⟩)
  · by_cases hyU : IsUnit (φ (chartERing.η 𝒪 π r))
    ·
      have hV₁ : (DeligneDatum.pullback π B g₁ d).VertexNondegAt π (IsLocalRing.maximalIdeal B) (stdFullLattice (𝒪 := 𝒪) K₀) :=
        vertexNondegAt_std_of_line_eq π _ _ 1 _ (line_pullback_std π d g₁ _ hd.2.1)
          (hab_snd π hπ r hres hr0 _ h𝔪p hπ𝔪 _ ((unit_iff _).mp hyU) ((unit_iff _).mp hyq))
      have hV : d.VertexNondegAt π (IsLocalRing.maximalIdeal B) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)) := by
        have h := vertexNondegAt_pullback π (DeligneDatum.pullback π B g₁ d) g₁⁻¹ (IsLocalRing.maximalIdeal B) _ hV₁
        rwa [pullback_inv_pullback, inv_inv] at h
      obtain ⟨c, hc⟩ := DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt hπ d
        (IsLocalRing.maximalIdeal B) hπ𝔪 (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)) _ _ hV hEk
      have hVc := vertexNondegAt_act_scalarGL π d (IsLocalRing.maximalIdeal B) _ c hV
      rcases hc with hc | hc
      · have hks : Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act g₁ (stdVertex 𝒪 K₀) := vtx c _ _ hc
        have hV' := toD' _ (vertexNondegAt_congr π d _ hc hVc)
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hks, hyU, unit_y' hV'⟩)))
      · have hks : Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀ := vtx c _ _ hc
        have hV' := toD' _ (vertexNondegAt_congr π d _ hc hVc)
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hks, hyU, unit_x' hV'⟩)))
    ·
      have hx𝔪 : φ (chartERing.ξ 𝒪 π r) ∈ IsLocalRing.maximalIdeal B := by rwa [unit_iff, not_not] at hxU
      have hy𝔪 : φ (chartERing.η 𝒪 π r) ∈ IsLocalRing.maximalIdeal B := by rwa [unit_iff, not_not] at hyU
      obtain ⟨c, X, Y, hX, hY, hc⟩ :=
        DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt hπ d (IsLocalRing.maximalIdeal B) hπ𝔪
          (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)) (stdFullLattice (𝒪 := 𝒪) K₀)
          (FullLattice.act k⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀))) (FullLattice.act k⁻¹ (stdFullLattice (𝒪 := 𝒪) K₀)) hdE hEk

      have hEc : d.EdgeNondegAt π (IsLocalRing.maximalIdeal B)
          (FullLattice.act (scalarGL c)⁻¹ (FullLattice.act k⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀))))
          (FullLattice.act (scalarGL c)⁻¹ (FullLattice.act k⁻¹ (stdFullLattice (𝒪 := 𝒪) K₀))) := by
        have h := DeligneDatum.edgeNondegAt_pullback_act_inv π d (scalarGL c) (IsLocalRing.maximalIdeal B) _ _ hEk
        rwa [pullback_scalarGL] at h
      have hYc : (FullLattice.act (scalarGL c)⁻¹ Y).1 = X.1 := by
        show latticeMap (scalarGL c)⁻¹ Y.1 = X.1
        rw [← hc, latticeMap_inv_latticeMap]
      have vS : ∀ (Z : FullLattice 𝒪 K₀) (T : Submodule 𝒪 (Fin 2 → K₀)) (hT : IsFullLattice T),
          (FullLattice.act (scalarGL c)⁻¹ (FullLattice.act k⁻¹ Z)).1 = T →
          Vertex.act k (Vertex.mk 𝒪 K₀ T hT) = Vertex.mk 𝒪 K₀ Z.1 Z.2 := by
        intro Z T hT h
        apply act_eq_of_eq_act_inv
        rw [← vertexMk_act]
        refine Vertex.mk_eq_mk_iff.mpr ⟨c⁻¹, ?_⟩
        rw [scalarGL_inv]; exact h

      have e₁' : Vertex.mk 𝒪 K₀ (latticeMap (scalarGL (unitOfNeZero (K := K₀) hπ.ne_zero)⁻¹) (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)).1)
          ((FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)).2.map _) = Vertex.act g₁ (stdVertex 𝒪 K₀) :=
        (Vertex.mk_eq_mk_iff.mpr ⟨(unitOfNeZero (K := K₀) hπ.ne_zero)⁻¹, rfl⟩).symm
      have e₀' : Vertex.mk 𝒪 K₀ (latticeMap (scalarGL (unitOfNeZero (K := K₀) hπ.ne_zero)) (stdFullLattice (𝒪 := 𝒪) K₀).1) ((stdFullLattice (𝒪 := 𝒪) K₀).2.map _) =
          stdVertex 𝒪 K₀ :=
        (Vertex.mk_eq_mk_iff.mpr ⟨unitOfNeZero (K := K₀) hπ.ne_zero, rfl⟩).symm
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
      ·
        have hk1 : Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act g₁ (stdVertex 𝒪 K₀) := vtx c _ _ hc
        have hEg := DeligneDatum.edgeNondegAt_pullback_act_inv π d g₁ (IsLocalRing.maximalIdeal B) _ _ hEc
        have hL'g : (FullLattice.act g₁⁻¹ (FullLattice.act (scalarGL c)⁻¹
            (FullLattice.act k⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀))))).1 = (stdFullLattice (𝒪 := 𝒪) K₀).1 := by
          show latticeMap g₁⁻¹ _ = _
          rw [hYc]; exact latticeMap_inv_latticeMap g₁ _
        have hLg := crossing_bot' π hπ (DeligneDatum.pullback π B g₁ d) (IsLocalRing.maximalIdeal B) _ hy𝔪
          (line_pullback_std π d g₁ _ hd.2.1) _ _ hL'g hEg
        have hL : (FullLattice.act (scalarGL c)⁻¹ (FullLattice.act k⁻¹ (stdFullLattice (𝒪 := 𝒪) K₀))).1 = (stdFullLattice (𝒪 := 𝒪) K₀).1 := by
          have h := congrArg (latticeMap g₁) hLg
          rw [show latticeMap g₁ (FullLattice.act g₁⁻¹ (FullLattice.act (scalarGL c)⁻¹
              (FullLattice.act k⁻¹ (stdFullLattice (𝒪 := 𝒪) K₀)))).1 =
              (FullLattice.act (scalarGL c)⁻¹ (FullLattice.act k⁻¹ (stdFullLattice (𝒪 := 𝒪) K₀))).1 from
            latticeMap_latticeMap_inv g₁ _] at h
          rw [h, ← latticeMap_mul, ← latticeMap_mul, diag_mul_scalarGL_inv_mul_diagSnd hπ.ne_zero g₁ hg₁, latticeMap_one]
          rfl
        have hk0 : Vertex.act k (stdVertex 𝒪 K₀) = stdVertex 𝒪 K₀ := vS (stdFullLattice (𝒪 := 𝒪) K₀) _ (stdFullLattice (𝒪 := 𝒪) K₀).2 hL
        exact Or.inl (Or.inl ⟨hk0, hk1⟩)
      ·
        have hk1 : Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀ := vtx c _ _ hc
        have hEg := DeligneDatum.edgeNondegAt_pullback_act_inv π d g₁ (IsLocalRing.maximalIdeal B) _ _ hEc
        have hLg' : (FullLattice.act g₁⁻¹ (FullLattice.act (scalarGL c)⁻¹
            (FullLattice.act k⁻¹ (stdFullLattice (𝒪 := 𝒪) K₀)))).1 = (stdFullLattice (𝒪 := 𝒪) K₀).1 := by
          show latticeMap g₁⁻¹ _ = _
          rw [hYc]; exact latticeMap_inv_latticeMap g₁ _
        have hL'g := crossing_top' π hπ (DeligneDatum.pullback π B g₁ d) (IsLocalRing.maximalIdeal B) _ hy𝔪
          (line_pullback_std π d g₁ _ hd.2.1) _ _ hLg' hEg
        have hL' : (FullLattice.act (scalarGL c)⁻¹ (FullLattice.act k⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)))).1 =
            latticeMap (scalarGL (unitOfNeZero (K := K₀) hπ.ne_zero)) (stdFullLattice (𝒪 := 𝒪) K₀).1 := by
          have h := congrArg (latticeMap g₁) hL'g
          rw [show latticeMap g₁ (FullLattice.act g₁⁻¹ (FullLattice.act (scalarGL c)⁻¹
              (FullLattice.act k⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀))))).1 =
              (FullLattice.act (scalarGL c)⁻¹ (FullLattice.act k⁻¹ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)))).1 from
            latticeMap_latticeMap_inv g₁ _] at h
          rw [h, ← latticeMap_mul, diag_mul_diagSnd hπ.ne_zero g₁ hg₁]
          rfl
        have hk0 : Vertex.act k (stdVertex 𝒪 K₀) = Vertex.act g₁ (stdVertex 𝒪 K₀) :=
          (congrArg (Vertex.act k) e₀').symm.trans (vS (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)) _ _ hL')
        exact Or.inl (Or.inr ⟨hk0, hk1⟩)
      ·
        have hk0 : Vertex.act k (stdVertex 𝒪 K₀) = Vertex.act g₁ (stdVertex 𝒪 K₀) := vtx c _ _ hc
        have hL := crossing_bot π hπ g₁ hg₁ d (IsLocalRing.maximalIdeal B) _ hx𝔪 hd.1 _ _ hYc hEc
        have hk1 : Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀ :=
          (congrArg (Vertex.act k) e₁').symm.trans (vS (stdFullLattice (𝒪 := 𝒪) K₀) _ _ hL)
        exact Or.inl (Or.inr ⟨hk0, hk1⟩)
      ·
        have hk0 : Vertex.act k (stdVertex 𝒪 K₀) = stdVertex 𝒪 K₀ := vtx c _ _ hc
        have hL' := crossing_top π hπ g₁ hg₁ d (IsLocalRing.maximalIdeal B) _ hx𝔪 hd.1 _ _ hYc hEc
        have hk1 : Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act g₁ (stdVertex 𝒪 K₀) :=
          vS (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)) _ (FullLattice.act g₁ (stdFullLattice (𝒪 := 𝒪) K₀)).2 hL'
        exact Or.inl (Or.inl ⟨hk0, hk1⟩)

end S_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing (solution)
