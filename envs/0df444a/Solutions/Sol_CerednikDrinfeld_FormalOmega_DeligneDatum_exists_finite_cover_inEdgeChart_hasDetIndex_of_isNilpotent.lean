-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4d711505-1c25-55f8-b334-382a473400cb

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra"

set_option autoImplicit false

open scoped TensorProduct Matrix MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B24X1

theorem exists_unit_mul_zpow_of_ne_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : 𝒪ˣ), x = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx (by rw [map_zero, zero_div])
  obtain ⟨i, ua, hua⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hπ
  obtain ⟨j, ub, hub⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ

  refine ⟨(i : ℤ) - j, ua⁻¹ * ub, ?_⟩
  have ha : algebraMap 𝒪 K a = algebraMap 𝒪 K π ^ i * algebraMap 𝒪 K (ua⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hua, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hb' : algebraMap 𝒪 K b = algebraMap 𝒪 K π ^ j * algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hub, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hubK : algebraMap 𝒪 K (ub : 𝒪ˣ) ≠ 0 := by
    intro h
    apply ub.ne_zero
    exact IsFractionRing.injective 𝒪 K (by rw [h, map_zero])
  have hBi : algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) = (algebraMap 𝒪 K (ub : 𝒪ˣ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [ha, hb', hBi, zpow_sub₀ hπK, zpow_natCast, zpow_natCast, Units.val_mul, map_mul]
  field_simp

section Lattices

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

theorem latticeMap_diagFst_le {π : 𝒪} (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) :
    latticeMap (diagFst K c) (stdLattice 𝒪 K) ≤ stdLattice 𝒪 K := by
  apply latticeMap_le_stdLattice_of_isInteger
  intro i j
  rw [diagFst_coe]
  fin_cases i <;> fin_cases j
  · exact ⟨π, by simp [hc]⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

theorem smul_mem_latticeMap_diagFst {π : 𝒪} (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {v : Fin 2 → K} (hv : v ∈ stdLattice 𝒪 K) :
    algebraMap 𝒪 K π • v ∈ latticeMap (diagFst K c) (stdLattice 𝒪 K) := by
  refine mem_latticeMap.mpr ⟨![v 0, algebraMap 𝒪 K π * v 1], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hv 0
    · obtain ⟨r, hr⟩ := hv 1
      exact ⟨π * r, by simp [← hr]⟩
  · rw [diagFst_mulVec, hc]
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]

theorem smul_mem_latticeMap_of_forall {π : 𝒪} (l : GL (Fin 2) K) {S L : Submodule 𝒪 (Fin 2 → K)}
    (h : ∀ v ∈ L, algebraMap 𝒪 K π • v ∈ S) {v : Fin 2 → K} (hv : v ∈ latticeMap l L) :
    algebraMap 𝒪 K π • v ∈ latticeMap l S := by
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv
  rw [← Matrix.mulVec_smul]
  exact mulVec_mem_latticeMap (h w hw)

theorem val_det_scalarGL (a : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (scalarGL a) : Kˣ) : K) = (a : K) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

theorem val_det_diagFst (a : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (diagFst K a) : Kˣ) : K) = (a : K) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, diagFst_coe, Matrix.det_diagonal]
  simp

end Lattices

section Orient

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {C : Type} [CommRing C] [Algebra 𝒪 C]

theorem rescale (hπ : Irreducible π) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (e : DeligneDatum (K := K) π C)
    (s : GL (Fin 2) K) (S L : FullLattice 𝒪 K) (hS : S.1 = latticeMap s (stdLattice 𝒪 K))
    (hSL : S.1 ≤ L.1) (hπL : ∀ v ∈ L.1, algebraMap 𝒪 K π • v ∈ S.1) (hch : e.InEdgeChart π S L)
    (m : ℤ) (u : 𝒪ˣ)
    (hdet : ((Matrix.GeneralLinearGroup.det s : Kˣ) : K) = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ (2 * m)) :
    ∃ M' M : FullLattice 𝒪 K, M'.1 ≤ M.1 ∧ (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧ HasDetIndex π M'.1 0 ∧
      e.InEdgeChart π M' M := by
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  refine ⟨FullLattice.act (scalarGL (c ^ (-m))) S, FullLattice.act (scalarGL (c ^ (-m))) L,
    latticeMap_mono _ hSL, ?_, ?_, (DeligneDatum.inEdgeChart_act_scalarGL_iff e S L (c ^ (-m))).mpr hch⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [smul_comm]
    exact mem_latticeMap_scalarGL.mpr ⟨_, hπL w hw, rfl⟩
  · refine ⟨scalarGL (c ^ (-m)) * s, ?_, u, ?_⟩
    · show latticeMap (scalarGL (c ^ (-m)) * s) (stdLattice 𝒪 K) = latticeMap (scalarGL (c ^ (-m))) S.1
      rw [latticeMap_mul, hS]
    · rw [map_mul, Units.val_mul, val_det_scalarGL, hdet, Units.val_zpow_eq_zpow_val, hc, zpow_zero, mul_one]
      have h1 : (algebraMap 𝒪 K π ^ (-m)) ^ 2 * algebraMap 𝒪 K π ^ (2 * m) = 1 := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hπK, show -m * ((2 : ℕ) : ℤ) + 2 * m = 0 by push_cast; ring,
          zpow_zero]
      calc (algebraMap 𝒪 K π ^ (-m)) ^ 2 * (algebraMap 𝒪 K ↑u * algebraMap 𝒪 K π ^ (2 * m))
          = algebraMap 𝒪 K ↑u * ((algebraMap 𝒪 K π ^ (-m)) ^ 2 * algebraMap 𝒪 K π ^ (2 * m)) := by ring
        _ = algebraMap 𝒪 K ↑u := by rw [h1, mul_one]

theorem orient (hπ : Irreducible π) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (e : DeligneDatum (K := K) π C)
    (l : GL (Fin 2) K) (n : ℤ) (u : 𝒪ˣ)
    (hdet : ((Matrix.GeneralLinearGroup.det l : Kˣ) : K) = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n)
    (hch : e.InEdgeChart π (FullLattice.act l (FullLattice.act (diagFst K c) (stdFullLattice K)))
      (FullLattice.act l (stdFullLattice K))) :
    ∃ M' M : FullLattice 𝒪 K, M'.1 ≤ M.1 ∧ (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧ HasDetIndex π M'.1 0 ∧
      e.InEdgeChart π M' M := by
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  set S : FullLattice 𝒪 K := FullLattice.act l (FullLattice.act (diagFst K c) (stdFullLattice K)) with hSdef
  set L : FullLattice 𝒪 K := FullLattice.act l (stdFullLattice K) with hLdef
  have hS : S.1 = latticeMap (l * diagFst K c) (stdLattice 𝒪 K) := by
    rw [hSdef, latticeMap_mul]; rfl
  have hL : L.1 = latticeMap l (stdLattice 𝒪 K) := by rw [hLdef]; rfl
  have hSL : S.1 ≤ L.1 := by
    rw [hSdef, hLdef]
    exact latticeMap_mono l (latticeMap_diagFst_le c hc)
  have hπL : ∀ v ∈ L.1, algebraMap 𝒪 K π • v ∈ S.1 := by
    rw [hSdef, hLdef]
    intro v hv
    exact smul_mem_latticeMap_of_forall l (fun w hw => smul_mem_latticeMap_diagFst c hc hw) hv
  rcases Int.even_or_odd' n with ⟨m, hm | hm⟩
  ·
    have hch' := DeligneDatum.inEdgeChart_swap c hc hch
    refine rescale hπ c hc e (scalarGL c * l) (FullLattice.act (scalarGL c) L) S ?_ ?_ ?_ hch' (m + 1) u ?_
    · show latticeMap (scalarGL c) L.1 = _
      rw [hL, latticeMap_mul]
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
      rw [hc]
      exact hπL w hw
    · intro v hv
      rw [← hc]
      exact mem_latticeMap_scalarGL.mpr ⟨v, hSL hv, rfl⟩
    · rw [map_mul, Units.val_mul, val_det_scalarGL, hdet, hc, hm]
      rw [← zpow_natCast, mul_left_comm, ← zpow_add₀ hπK]
      congr 2
      push_cast
      ring
  ·
    refine rescale hπ c hc e (l * diagFst K c) S L hS hSL hπL hch (m + 1) u ?_
    rw [map_mul, Units.val_mul, val_det_diagFst, hdet, hc, hm, mul_assoc, ← zpow_add_one₀ hπK]
    congr 2
    ring

end Orient

end B24X1

open B24X1 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (k : ℕ) (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤) (M' M : Fin k → FullLattice 𝒪 K),
      ∀ i : Fin k, (M' i).1 ≤ (M i).1 ∧ (∀ v ∈ (M i).1, algebraMap 𝒪 K π • v ∈ (M' i).1) ∧ HasDetIndex π (M' i).1 0 ∧
        (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).InEdgeChart π (M' i) (M i) := by
  classical
  haveI := hfin
  have hc : ((unitOfNeZero (K := K) hπ.ne_zero : Kˣ) : K) = algebraMap 𝒪 K π := unitOfNeZero_coe hπ.ne_zero
  have hg : ((diagFst K (unitOfNeZero (K := K) hπ.ne_zero) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![algebraMap 𝒪 K π, 1] := by
    rw [diagFst_coe, hc]
  obtain ⟨k, f, hf, h, H⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_isPullback_inEdgeChart_of_finite π hπ
      (diagFst K (unitOfNeZero (K := K) hπ.ne_zero)) hg B hB d
  have key : ∀ i : Fin k, ∃ M' M : FullLattice 𝒪 K, M'.1 ≤ M.1 ∧ (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧
      HasDetIndex π M'.1 0 ∧ (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).InEdgeChart π M' M := by
    intro i
    obtain ⟨d', hpb, hch⟩ := H i (Localization.Away (f i))
    obtain ⟨n, u, hdet⟩ := exists_unit_mul_zpow_of_ne_zero hπ (Units.ne_zero (Matrix.GeneralLinearGroup.det (h i)))
    exact orient hπ _ hc _ (h i) n u hdet (CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_of_isPullback (h i) hpb hch)
  exact ⟨k, f, hf, fun i => (key i).choose, fun i => (key i).choose_spec.choose, fun i => (key i).choose_spec.choose_spec⟩

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent (solution)
