-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ca4c7027-6982-539b-99ea-589b2d9a7a4b

import Mathlib
import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_LocalLanglands_CartanDecomposition
import Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
import Theorems.Thm_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq
import Theorems.Thm_LT_LatticeTree_Vertex_isWithin_iff_dist_le
import Theorems.Thm_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit

set_option autoImplicit false

p2m_open "LT.LatticeTree CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit.CerednikDrinfeld.BruhatTits LocalGL2"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree BruhatTits.tree Mumford.GraphAction BruhatTits.dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq Mumford.GraphAction.dist_smul_smul"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq"
namespace CartanDist
p2m_open "CerednikDrinfeld.BruhatTits CerednikDrinfeld"

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)

local notation "cϖ" => unitOfNeZero (K := K) (Irreducible.ne_zero hϖ)
local notation "R²" => stdLattice R K
local notation "mapGL" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)

theorem mapGL_smul_stdVertex (M : Matrix.GeneralLinearGroup (Fin 2) R) : mapGL M • stdVertex R K = stdVertex R K := by
  show Vertex.mk R K (latticeMap (mapGL M) R²) _ = Vertex.mk R K R² _
  rw [Vertex.mk_eq_mk_iff, ← interLattice_zero_zero (K := K) (0 : R), latticeMap_map_interLattice]
  simp only [mulVecPair_zero, mulVecPair_one, mul_zero, add_zero]
  exact Homothetic.refl _

theorem scalar_comm (a b : Kˣ) (X : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL a) (latticeMap (scalarGL b) X) = latticeMap (scalarGL b) (latticeMap (scalarGL a) X) := by
  rw [← latticeMap_mul, ← scalarGL_mul, mul_comm, scalarGL_mul, latticeMap_mul]

include hϖ in

theorem le_of_isWithin_diagSnd_pow {k n : ℕ}
    (h : Vertex.IsWithin cϖ n (stdVertex R K) (diagSnd (cϖ ^ k) • stdVertex R K)) : k ≤ n := by
  obtain ⟨L, M, hL, hM, hLv, hMv, hlow, hup⟩ := h

  obtain ⟨e, he⟩ : Homothetic L R² := by
    rw [show stdVertex R K = Vertex.mk R K R² isFullLattice_stdLattice from rfl, Vertex.mk_eq_mk_iff] at hLv
    exact hLv
  obtain ⟨f, hf⟩ : Homothetic M (latticeMap (diagSnd (cϖ ^ k)) R²) := by
    rw [show diagSnd (cϖ ^ k) • stdVertex R K = Vertex.mk R K (latticeMap (diagSnd (cϖ ^ k)) R²)
      (isFullLattice_stdLattice.map _) from rfl, Vertex.mk_eq_mk_iff] at hMv
    exact hMv

  have hM' : latticeMap (scalarGL e) M = latticeMap (scalarGL (e * f⁻¹)) (latticeMap (diagSnd (cϖ ^ k)) R²) := by
    rw [← hf, ← latticeMap_mul, ← scalarGL_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hup' : latticeMap (scalarGL (e * f⁻¹)) (latticeMap (diagSnd (cϖ ^ k)) R²) ≤ R² := by
    rw [← hM', ← he]; exact latticeMap_mono _ hup
  have hlow' : latticeMap (scalarGL (cϖ ^ n)) R² ≤ latticeMap (scalarGL (e * f⁻¹)) (latticeMap (diagSnd (cϖ ^ k)) R²) := by
    rw [← hM', ← he, scalar_comm]; exact latticeMap_mono _ hlow
  set lam : Kˣ := e * f⁻¹ with hlam

  have hi : IsLocalization.IsInteger R (lam : K) := by
    have hmem : (lam : K) • (Pi.single 0 1 : Fin 2 → K) ∈ R² :=
      hup' (mem_latticeMap_scalarGL.mpr ⟨_, single_zero_one_mem_latticeMap_diagSnd _, rfl⟩)
    have := hmem 0
    rwa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
  obtain ⟨r, hr⟩ := hi

  have hmem : ((cϖ ^ n : Kˣ) : K) • (Pi.single 1 1 : Fin 2 → K) ∈
      latticeMap (scalarGL lam) (latticeMap (diagSnd (cϖ ^ k)) R²) :=
    hlow' (mem_latticeMap_scalarGL.mpr ⟨_, single_one_mem_stdLattice (R := R) (K := K) (j := 1), rfl⟩)
  obtain ⟨w, hw, hweq⟩ := mem_latticeMap_scalarGL.mp hmem
  obtain ⟨-, w', ⟨s, rfl⟩, hw1⟩ := mem_latticeMap_diagSnd_stdLattice.mp hw

  have h1 := congrArg (fun v : Fin 2 → K => v 1) hweq
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
  rw [← hw1, ← hr, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, unitOfNeZero_coe, ← map_pow, ← map_pow,
    ← map_mul, ← map_mul] at h1
  have h1R : r * (ϖ ^ k * s) = ϖ ^ n := IsFractionRing.injective R K h1
  exact (pow_irreducible_dvd_pow_iff hϖ).mp ⟨r * s, by rw [← h1R]; ring⟩

theorem map_cartanDiag_zero (k : ℕ) :
    (cartanDiag ϖ 0 k).map (algebraMap R K) = ((diagSnd (cϖ ^ k) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [diagSnd_coe, cartanDiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Units.val_pow_eq_pow_val, unitOfNeZero_coe]

theorem coe_mapGL (M : Matrix.GeneralLinearGroup (Fin 2) R) :
    ((mapGL M : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (M : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j M

include hϖ in
theorem main (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k)
    (hunit : ∃ i j : Fin 2, ∃ w : Rˣ, (g : Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K w) :
    (tree R K).dist (stdVertex R K) (g • stdVertex R K) = k := by

  have hint' := hint
  choose gR hgR using hint'
  set G : Matrix (Fin 2) (Fin 2) R := fun i j => gR i j with hG
  have hGmap : G.map (algebraMap R K) = (g : Matrix (Fin 2) (Fin 2) K) := by
    ext i j; exact hgR i j
  have hdetG : G.det = (u : R) * ϖ ^ k := by
    apply IsFractionRing.injective R K
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGmap, hdet, map_mul, map_pow]
  have hdetG0 : G.det ≠ 0 := by
    rw [hdetG]; exact mul_ne_zero (Units.ne_zero u) (pow_ne_zero k hϖ.ne_zero)

  obtain ⟨a, b, hab, k₁, k₂, hGeq⟩ := LocalGL2.exists_cartanRel_cartanDiag hϖ G hdetG0
  have hrel : CartanRel G (cartanDiag ϖ a b) := ⟨k₁, k₂, hGeq⟩

  have ha : a = 0 := by
    obtain ⟨i, j, w, hw⟩ := hunit
    have hGij : G i j = (w : R) := IsFractionRing.injective R K (by rw [← hw, ← hGmap]; rfl)
    have hmem : (w : R) ∈ entryIdeal G := hGij ▸ entry_mem_entryIdeal G i j
    rw [hrel.entryIdeal_eq, entryIdeal_cartanDiag ϖ hab, Ideal.mem_span_singleton] at hmem
    by_contra ha0
    exact hϖ.not_isUnit ((isUnit_pow_iff ha0).mp (isUnit_of_dvd_unit hmem w.isUnit))

  have hb : b = k := by
    have h1 : Associated G.det (ϖ ^ (a + b)) := (cartanDiag_det ϖ a b) ▸ hrel.det_associated
    have h2 : Associated G.det (ϖ ^ k) := by
      rw [hdetG]; exact (associated_isUnit_mul_left_iff u.isUnit).mpr (Associated.refl _)
    rw [ha, zero_add] at h1
    exact ((pow_irreducible_associated_iff hϖ).mp (h1.symm.trans h2))
  rw [ha, hb] at hGeq

  set D : GL (Fin 2) K := diagSnd (cϖ ^ k) with hD
  have hgfac : g = mapGL k₁ * D * mapGL k₂ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_mapGL, coe_mapGL, hD, ← map_cartanDiag_zero hϖ, ← Matrix.map_mul, ← Matrix.map_mul,
      ← hGeq, hGmap]

  have hdistD : (tree R K).dist (stdVertex R K) (g • stdVertex R K) = (tree R K).dist (stdVertex R K) (D • stdVertex R K) := by
    rw [hgfac, mul_smul, mul_smul, mapGL_smul_stdVertex k₂]
    have : (tree R K).dist (stdVertex R K) (mapGL k₁ • (D • stdVertex R K)) =
        (tree R K).dist (mapGL k₁ • stdVertex R K) (mapGL k₁ • (D • stdVertex R K)) := by
      rw [mapGL_smul_stdVertex k₁]
    rw [this]
    exact CerednikDrinfeld.Mumford.GraphAction.dist_smul_smul (tree R K) (mapGL k₁) _ _

  have hle := CerednikDrinfeld.BruhatTits.dist_stdVertex_smul_stdVertex_le_of_isInteger_of_det_eq R K ϖ hϖ g hint k u hdet
  refine le_antisymm hle ?_
  have hw : Vertex.IsWithin cϖ ((tree R K).dist (stdVertex R K) (g • stdVertex R K)) (stdVertex R K) (D • stdVertex R K) :=
    (LT.LatticeTree.Vertex.isWithin_iff_dist_le R K ϖ hϖ _ _ _).mpr (le_of_eq hdistD.symm)
  rw [hD] at hw
  exact le_of_isWithin_diagSnd_pow hϖ hw

end CerednikDrinfeld.BruhatTits.CartanDist

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k)
    (hunit : ∃ i j : Fin 2, ∃ w : Rˣ, (g : Matrix (Fin 2) (Fin 2) K) i j = algebraMap R K w) :
    (CerednikDrinfeld.BruhatTits.tree R K).dist (LT.LatticeTree.stdVertex R K)
      (g • LT.LatticeTree.stdVertex R K) = k :=
  CerednikDrinfeld.BruhatTits.CartanDist.main hϖ g hint k u hdet hunit

end S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit (solution)
