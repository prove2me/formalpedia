-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7fea48aa-a409-50d9-8132-c5f3056f14a8

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer.CerednikDrinfeld CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer.CerednikDrinfeld.BruhatTits LT.LatticeTree"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "VertRel tree tree_adj_iff BruhatTits.tree"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree_adj_iff VertRel tree"
namespace NbrDict
p2m_open "CerednikDrinfeld.BruhatTits CerednikDrinfeld"

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K₀ : Type} [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
variable {ϖ : R}

local notation "φ" => algebraMap R K₀
local notation "Λ" => stdLattice R K₀
local notation "ϖΛ" hϖ' => latticeMap (scalarGL (unitOfNeZero (K := K₀) hϖ')) (stdLattice R K₀)

theorem isUnit_of_not_dvd (hϖ : Irreducible ϖ) {a : R} (h : ¬ ϖ ∣ a) : IsUnit a := by
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  by_contra hu
  have : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hu
  rw [hmax, Ideal.mem_span_singleton] at this
  exact h this

theorem dvd_or_isUnit (hϖ : Irreducible ϖ) (a : R) : ϖ ∣ a ∨ IsUnit a := by
  by_cases h : ϖ ∣ a
  · exact Or.inl h
  · exact Or.inr (isUnit_of_not_dvd hϖ h)

theorem latticeMap_scalarGL_irreducible_eq (hϖ : Irreducible ϖ) {ϖ' : R} (hϖ' : Irreducible ϖ') :
    (ϖΛ hϖ'.ne_zero) = (ϖΛ hϖ.ne_zero) := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hϖ'

  have hunit : IsUnit (φ (u : R)) := (Units.isUnit u).map φ
  have hsplit : unitOfNeZero (K := K₀) hϖ'.ne_zero = unitOfNeZero (K := K₀) hϖ.ne_zero * hunit.unit := by
    ext
    rw [Units.val_mul, unitOfNeZero_coe, unitOfNeZero_coe, IsUnit.unit_spec, ← map_mul, hu]
  rw [hsplit, scalarGL_mul, latticeMap_mul,
    latticeMap_scalarGL_eq_self_of_isUnit (e := hunit.unit) (Units.isUnit u) hunit.unit_spec]

theorem exists_eq_vecPair {v : Fin 2 → K₀} (hv : v ∈ Λ) : ∃ a b : R, v = vecPair R K₀ a b := by
  obtain ⟨a, ha⟩ := hv 0
  obtain ⟨b, hb⟩ := hv 1
  refine ⟨a, b, funext fun i => ?_⟩
  fin_cases i
  · simpa [vecPair] using ha.symm
  · simpa [vecPair] using hb.symm

theorem vecPair_mem_scalar_iff (hϖ0 : ϖ ≠ 0) {a b : R} :
    vecPair R K₀ a b ∈ (ϖΛ hϖ0) ↔ ϖ ∣ a ∧ ϖ ∣ b := by
  refine ⟨dvd_of_vecPair_mem_latticeMap_scalarGL hϖ0, fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ?_⟩
  rw [mem_latticeMap_scalarGL_stdLattice hϖ0]
  intro i
  fin_cases i
  · exact ⟨φ x, ⟨x, rfl⟩, by simp [vecPair, hx, map_mul]⟩
  · exact ⟨φ y, ⟨y, rfl⟩, by simp [vecPair, hy, map_mul]⟩

theorem vecPair_lincomb (α β a b x y : R) :
    (α • vecPair R K₀ a b + β • vecPair R K₀ x y : Fin 2 → K₀) = vecPair R K₀ (α * a + β * x) (α * b + β * y) := by
  funext i
  fin_cases i <;> simp [vecPair, Algebra.smul_def]

theorem exists_eq_interLattice (hϖ : Irreducible ϖ) {M : Submodule R (Fin 2 → K₀)}
    (hlow : (ϖΛ hϖ.ne_zero) < M) (hup : M < Λ) :
    ∃ c d : R, ¬ (ϖ ∣ c ∧ ϖ ∣ d) ∧ M = interLattice R K₀ ϖ c d := by
  obtain ⟨v, hvM, hvlow⟩ := SetLike.exists_of_lt hlow
  obtain ⟨a, b, rfl⟩ := exists_eq_vecPair (hup.le hvM)
  have hab : ¬ (ϖ ∣ a ∧ ϖ ∣ b) := fun h => hvlow ((vecPair_mem_scalar_iff hϖ.ne_zero).2 h)
  refine ⟨a, b, hab, le_antisymm ?_ ?_⟩
  ·
    intro w hwM
    obtain ⟨x, y, rfl⟩ := exists_eq_vecPair (hup.le hwM)
    rw [vecPair_mem_interLattice_iff_dvd]
    by_contra hdet
    obtain ⟨D, hD⟩ := isUnit_of_not_dvd hϖ hdet
    apply hup.ne (le_antisymm hup.le ?_)
    intro u hu
    obtain ⟨p, q, rfl⟩ := exists_eq_vecPair hu

    have hD' : ((D⁻¹ : Rˣ) : R) * (b * x - a * y) = 1 := by rw [← hD, Units.inv_mul]
    have e1 : ((D⁻¹ : Rˣ) : R) * (x * q - y * p) * a + ((D⁻¹ : Rˣ) : R) * (b * p - a * q) * x = p := by
      linear_combination p * hD'
    have e2 : ((D⁻¹ : Rˣ) : R) * (x * q - y * p) * b + ((D⁻¹ : Rˣ) : R) * (b * p - a * q) * y = q := by
      linear_combination q * hD'
    have key : vecPair R K₀ p q =
        (((D⁻¹ : Rˣ) : R) * (x * q - y * p)) • vecPair R K₀ a b + (((D⁻¹ : Rˣ) : R) * (b * p - a * q)) • vecPair R K₀ x y := by
      rw [vecPair_lincomb, e1, e2]
    rw [key]
    exact M.add_mem (M.smul_mem _ hvM) (M.smul_mem _ hwM)
  ·
    intro w hw
    have hw' := hw
    obtain ⟨x, y, rfl⟩ := exists_eq_vecPair (interLattice_le_stdLattice ϖ a b hw)
    rw [vecPair_mem_interLattice_iff_dvd] at hw'
    obtain ⟨q, hq⟩ := hw'
    rcases dvd_or_isUnit hϖ a with ha | ⟨A, hA⟩
    · rcases dvd_or_isUnit hϖ b with hb | ⟨B, hB⟩
      · exact absurd ⟨ha, hb⟩ hab
      ·
        have hB' : ((B⁻¹ : Rˣ) : R) * b = 1 := by rw [← hB, Units.inv_mul]
        have e1 : y * ((B⁻¹ : Rˣ) : R) * a + 1 * (x - y * ((B⁻¹ : Rˣ) : R) * a) = x := by ring
        have e2 : y * ((B⁻¹ : Rˣ) : R) * b + 1 * 0 = y := by linear_combination y * hB'
        have key : vecPair R K₀ x y = (y * ((B⁻¹ : Rˣ) : R)) • vecPair R K₀ a b +
            (1 : R) • vecPair R K₀ (x - y * ((B⁻¹ : Rˣ) : R) * a) 0 := by
          rw [vecPair_lincomb, e1, e2]
        rw [key]
        refine M.add_mem (M.smul_mem _ hvM) (M.smul_mem _ (hlow.le ((vecPair_mem_scalar_iff hϖ.ne_zero).2 ⟨?_, dvd_zero _⟩)))
        exact ⟨((B⁻¹ : Rˣ) : R) * q, by linear_combination ((B⁻¹ : Rˣ) : R) * hq + (-x) * hB'⟩
    ·
      have hA' : ((A⁻¹ : Rˣ) : R) * a = 1 := by rw [← hA, Units.inv_mul]
      have e1 : x * ((A⁻¹ : Rˣ) : R) * a + 1 * 0 = x := by linear_combination x * hA'
      have e2 : x * ((A⁻¹ : Rˣ) : R) * b + 1 * (y - x * ((A⁻¹ : Rˣ) : R) * b) = y := by ring
      have key : vecPair R K₀ x y = (x * ((A⁻¹ : Rˣ) : R)) • vecPair R K₀ a b +
          (1 : R) • vecPair R K₀ 0 (y - x * ((A⁻¹ : Rˣ) : R) * b) := by
        rw [vecPair_lincomb, e1, e2]
      rw [key]
      refine M.add_mem (M.smul_mem _ hvM) (M.smul_mem _ (hlow.le ((vecPair_mem_scalar_iff hϖ.ne_zero).2 ⟨dvd_zero _, ?_⟩)))
      exact ⟨-(((A⁻¹ : Rˣ) : R) * q), by linear_combination (-((A⁻¹ : Rˣ) : R)) * hq + (-y) * hA'⟩

theorem interLattice_eq_normal (hϖ : Irreducible ϖ) {c d : R} (hcd : ¬ (ϖ ∣ c ∧ ϖ ∣ d)) :
    (∃ t : R, interLattice R K₀ ϖ c d = interLattice R K₀ ϖ t 1) ∨ interLattice R K₀ ϖ c d = interLattice R K₀ ϖ 1 0 := by
  rcases dvd_or_isUnit hϖ d with hd | ⟨D, hD⟩
  ·
    have hc : ¬ ϖ ∣ c := fun h => hcd ⟨h, hd⟩
    obtain ⟨C, hC⟩ := isUnit_of_not_dvd hϖ hc
    right
    rw [← interLattice_unit_mul ϖ C⁻¹ c d]
    refine interLattice_congr ?_ ?_
    · rw [← hC, Units.inv_mul, sub_self]; exact dvd_zero _
    · rw [sub_zero]; exact hd.mul_left _
  · left
    refine ⟨((D⁻¹ : Rˣ) : R) * c, ?_⟩
    rw [← interLattice_unit_mul ϖ D⁻¹ c d, ← hD, Units.inv_mul]

theorem interval_of_vertRel_stdVertex (hϖ : Irreducible ϖ) {y : Vertex R K₀} (h : VertRel R K₀ (stdVertex R K₀) y) :
    ∃ (M : Submodule R (Fin 2 → K₀)) (hM : IsFullLattice M),
      Vertex.mk R K₀ M hM = y ∧ (ϖΛ hϖ.ne_zero) < M ∧ M < Λ := by
  obtain ⟨L, L', hL, hL', hLv, hL'y, ϖ', hϖ', h1, h2⟩ := h

  have hhom : Homothetic L Λ := by
    rw [stdVertex] at hLv
    exact Vertex.mk_eq_mk_iff.1 hLv
  obtain ⟨e, he⟩ := hhom
  refine ⟨latticeMap (scalarGL e) L', hL'.map _, ?_, ?_, ?_⟩
  · rw [← hL'y, Vertex.mk_eq_mk_iff]
    exact Homothetic.symm ⟨e, rfl⟩
  · rw [← latticeMap_scalarGL_irreducible_eq hϖ hϖ', ← he, ← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
    exact (latticeMap_lt_latticeMap_iff _).2 h1
  · rw [← he]
    exact (latticeMap_lt_latticeMap_iff _).2 h2

theorem interval_of_vertRel_stdVertex' (hϖ : Irreducible ϖ) {y : Vertex R K₀} (h : VertRel R K₀ y (stdVertex R K₀)) :
    ∃ (M : Submodule R (Fin 2 → K₀)) (hM : IsFullLattice M),
      Vertex.mk R K₀ M hM = y ∧ (ϖΛ hϖ.ne_zero) < M ∧ M < Λ := by
  obtain ⟨L, L', hL, hL', hLy, hL'v, ϖ', hϖ', h1, h2⟩ := h
  have hhom : Homothetic L' Λ := by
    rw [stdVertex] at hL'v
    exact Vertex.mk_eq_mk_iff.1 hL'v
  obtain ⟨e, he⟩ := hhom

  refine ⟨latticeMap (scalarGL (unitOfNeZero (K := K₀) hϖ'.ne_zero)) (latticeMap (scalarGL e) L),
    (hL.map _).map _, ?_, ?_, ?_⟩
  · rw [← hLy, Vertex.mk_eq_mk_iff, ← latticeMap_mul, ← scalarGL_mul]
    exact Homothetic.symm ⟨_, rfl⟩
  ·
    rw [← latticeMap_scalarGL_irreducible_eq hϖ hϖ', ← he]
    exact (latticeMap_lt_latticeMap_iff _).2 ((latticeMap_lt_latticeMap_iff _).2 h2)
  ·
    have h1' := (latticeMap_lt_latticeMap_iff (scalarGL e)).2 h1
    have hcomm : latticeMap (scalarGL e) (latticeMap (scalarGL (unitOfNeZero (K := K₀) hϖ'.ne_zero)) L) =
        latticeMap (scalarGL (unitOfNeZero (K := K₀) hϖ'.ne_zero)) (latticeMap (scalarGL e) L) := by
      rw [← latticeMap_mul, ← latticeMap_mul, scalarGL_mul_comm]
    rw [hcomm, he] at h1'
    exact h1'

theorem eq_mk_interLattice_of_adj (hϖ : Irreducible ϖ) {y : Vertex R K₀} (h : (tree R K₀).Adj (stdVertex R K₀) y) :
    (∃ t : R, y = Vertex.mk R K₀ (interLattice R K₀ ϖ t 1) (isFullLattice_interLattice hϖ t 1)) ∨
      y = Vertex.mk R K₀ (interLattice R K₀ ϖ 1 0) (isFullLattice_interLattice hϖ 1 0) := by
  rw [tree_adj_iff] at h
  obtain ⟨M, hM, rfl, hlow, hup⟩ : ∃ (M : Submodule R (Fin 2 → K₀)) (hM : IsFullLattice M),
      Vertex.mk R K₀ M hM = y ∧ (ϖΛ hϖ.ne_zero) < M ∧ M < Λ := by
    rcases h.2 with h' | h'
    · exact interval_of_vertRel_stdVertex hϖ h'
    · exact interval_of_vertRel_stdVertex' hϖ h'
  obtain ⟨c, d, hcd, rfl⟩ := exists_eq_interLattice hϖ hlow hup
  rcases interLattice_eq_normal (K₀ := K₀) hϖ hcd with ⟨t, ht⟩ | h0
  · left; refine ⟨t, ?_⟩
    exact Vertex.mk_eq_mk_iff.2 (ht ▸ Homothetic.refl _)
  · right
    exact Vertex.mk_eq_mk_iff.2 (h0 ▸ Homothetic.refl _)

theorem mk_interLattice_eq_iff (hϖ : Irreducible ϖ) (t t' : R) :
    Vertex.mk R K₀ (interLattice R K₀ ϖ t 1) (isFullLattice_interLattice hϖ t 1) =
      Vertex.mk R K₀ (interLattice R K₀ ϖ t' 1) (isFullLattice_interLattice hϖ t' 1) ↔ ϖ ∣ t - t' := by
  have h1 : ∀ r : R, ¬ (ϖ ∣ r ∧ ϖ ∣ (1 : R)) := fun r h => hϖ.not_isUnit (isUnit_of_dvd_one h.2)
  rw [Vertex.mk_eq_mk_iff]
  constructor
  · intro h
    have heq := eq_of_homothetic_of_mem_interval hϖ.prime (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero (h1 t))
      (interLattice_le_stdLattice _ _ _) (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero (h1 t'))
      (interLattice_le_stdLattice _ _ _) h
    have := dvd_of_interLattice_eq heq
    rwa [one_mul, mul_one] at this
  · intro h
    rw [interLattice_congr h (show ϖ ∣ (1 : R) - 1 by rw [sub_self]; exact dvd_zero _)]
    exact Homothetic.refl _

theorem mk_interLattice_one_zero_ne (hϖ : Irreducible ϖ) (t : R) :
    Vertex.mk R K₀ (interLattice R K₀ ϖ 1 0) (isFullLattice_interLattice hϖ 1 0) ≠
      Vertex.mk R K₀ (interLattice R K₀ ϖ t 1) (isFullLattice_interLattice hϖ t 1) := by
  intro h
  rw [Vertex.mk_eq_mk_iff] at h
  have h10 : ¬ (ϖ ∣ (1 : R) ∧ ϖ ∣ (0 : R)) := fun h => hϖ.not_isUnit (isUnit_of_dvd_one h.1)
  have ht1 : ¬ (ϖ ∣ t ∧ ϖ ∣ (1 : R)) := fun h => hϖ.not_isUnit (isUnit_of_dvd_one h.2)
  have heq := eq_of_homothetic_of_mem_interval hϖ.prime (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero h10)
    (interLattice_le_stdLattice _ _ _) (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero ht1)
    (interLattice_le_stdLattice _ _ _) h
  have := dvd_of_interLattice_eq heq
  rw [one_mul, mul_zero, sub_zero] at this
  exact hϖ.not_isUnit (isUnit_of_dvd_one this)

def swapMat (t : R) : GL (Fin 2) R :=
  ⟨!![t, 1; 1, 0], !![0, 1; 1, -t], by ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem map_swapMat (t : R) (s : GL (Fin 2) K₀) (hs : (s : Matrix (Fin 2) (Fin 2) K₀) = !![φ t, 1; 1, 0]) :
    Matrix.GeneralLinearGroup.map φ (swapMat t) = s := by
  apply Units.ext
  rw [hs]
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem eq_diagSnd (hϖ : Irreducible ϖ) (n : GL (Fin 2) K₀) (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, φ ϖ]) :
    n = diagSnd (unitOfNeZero (K := K₀) hϖ.ne_zero) := by
  apply Units.ext
  rw [hn, diagSnd_coe, unitOfNeZero_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem latticeMap_n (hϖ : Irreducible ϖ) (n : GL (Fin 2) K₀) (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, φ ϖ]) :
    latticeMap n Λ = interLattice R K₀ ϖ 1 0 := by
  rw [eq_diagSnd hϖ n hn, interLattice_one_zero hϖ.ne_zero]

theorem latticeMap_s (t : R) (s : GL (Fin 2) K₀) (hs : (s : Matrix (Fin 2) (Fin 2) K₀) = !![φ t, 1; 1, 0]) :
    latticeMap s Λ = Λ :=
  (latticeMap_stdLattice_eq_iff_mem_range s).2 ⟨swapMat t, map_swapMat t s hs⟩

theorem latticeMap_s_n (hϖ : Irreducible ϖ) (t : R) (n s : GL (Fin 2) K₀)
    (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, φ ϖ]) (hs : (s : Matrix (Fin 2) (Fin 2) K₀) = !![φ t, 1; 1, 0]) :
    latticeMap (s * n) Λ = interLattice R K₀ ϖ t 1 := by
  rw [latticeMap_mul, latticeMap_n hϖ n hn, ← map_swapMat t s hs, latticeMap_map_interLattice]
  congr 1 <;> simp [swapMat]

theorem smul_stdVertex (g : GL (Fin 2) K₀) :
    g • stdVertex R K₀ = Vertex.mk R K₀ (latticeMap g Λ) (isFullLattice_stdLattice.map g) := rfl

theorem mk_congr {L L' : Submodule R (Fin 2 → K₀)} (hL : IsFullLattice L) (hL' : IsFullLattice L') (h : L = L') :
    Vertex.mk R K₀ L hL = Vertex.mk R K₀ L' hL' := by
  subst h; rfl

end CerednikDrinfeld.BruhatTits.NbrDict

end

open CerednikDrinfeld.BruhatTits.NbrDict LT.LatticeTree in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (n : GL (Fin 2) K₀) (hn : (n : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, algebraMap R K₀ ϖ])
    (s : R → GL (Fin 2) K₀) (hs : ∀ t : R, (s t : Matrix (Fin 2) (Fin 2) K₀) = !![algebraMap R K₀ t, 1; 1, 0]) :
    (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) (n • LT.LatticeTree.stdVertex R K₀) ∧
    (∀ t : R, s t • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀) ∧
    (∀ y : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y →
      y = n • LT.LatticeTree.stdVertex R K₀ ∨ ∃ t : R, y = (s t * n) • LT.LatticeTree.stdVertex R K₀) ∧
    (∀ t t' : R, (s t * n) • LT.LatticeTree.stdVertex R K₀ = (s t' * n) • LT.LatticeTree.stdVertex R K₀ ↔ ϖ ∣ t - t') ∧
    (∀ t : R, n • LT.LatticeTree.stdVertex R K₀ ≠ (s t * n) • LT.LatticeTree.stdVertex R K₀) := by

  have hnv : n • stdVertex R K₀ = Vertex.mk R K₀ (interLattice R K₀ ϖ 1 0) (isFullLattice_interLattice hϖ 1 0) := by
    rw [smul_stdVertex]; exact mk_congr _ _ (latticeMap_n hϖ n hn)
  have hsnv : ∀ t : R, (s t * n) • stdVertex R K₀ =
      Vertex.mk R K₀ (interLattice R K₀ ϖ t 1) (isFullLattice_interLattice hϖ t 1) := fun t => by
    rw [smul_stdVertex]; exact mk_congr _ _ (latticeMap_s_n hϖ t n (s t) hn (hs t))
  refine ⟨?_, fun t => ?_, fun y hy => ?_, fun t t' => ?_, fun t => ?_⟩
  ·
    rw [tree_adj_iff]
    refine ⟨?_, Or.inl ⟨stdLattice R K₀, latticeMap n (stdLattice R K₀), isFullLattice_stdLattice,
      isFullLattice_stdLattice.map n, rfl, rfl, ?_⟩⟩
    · rw [eq_diagSnd hϖ n hn]
      exact (stdVertex_ne_act_diagSnd (R := R) (K := K₀) hϖ).symm
    · rw [eq_diagSnd hϖ n hn]
      exact adjacentLattice_stdLattice_diagSnd (R := R) (K := K₀) hϖ
  ·
    rw [smul_stdVertex]
    exact mk_congr _ _ (latticeMap_s t (s t) (hs t))
  ·
    rcases eq_mk_interLattice_of_adj hϖ hy with ⟨t, ht⟩ | h0
    · exact Or.inr ⟨t, ht.trans (hsnv t).symm⟩
    · exact Or.inl (h0.trans hnv.symm)
  ·
    rw [hsnv t, hsnv t']
    exact mk_interLattice_eq_iff hϖ t t'
  ·
    rw [hnv, hsnv t]
    exact mk_interLattice_one_zero_ne hϖ t

end S_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer (solution)
