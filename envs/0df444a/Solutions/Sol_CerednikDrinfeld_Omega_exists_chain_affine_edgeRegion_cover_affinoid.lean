-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c6e6e21a-97e6-5c33-9fd7-b6b25570e888

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_CerednikDrinfeld_Omega_vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine
import Theorems.Thm_CerednikDrinfeld_Omega_exists_fin_ballEdges
import Theorems.Thm_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
import Theorems.Thm_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid.CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine Omega.exists_fin_ballEdges Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion Omega.chain_clauses_of_ballEdges"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "vertexTube edgeTube PseudoUniformizer affinoid vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine exists_fin_ballEdges edgeRegion_subset_affinoid_and_exists_mem_edgeRegion chain_clauses_of_ballEdges"
namespace CoverChainAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]

theorem region_subset_of_v_sub_le (ϖ : PseudoUniformizer K₀ C) (c c' : K₀) (m : ℤ)
    (hcc : Valued.v (algebraMap K₀ C c - algebraMap K₀ C c') ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)))
    (hmm : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1)))) :
    ({z : C | Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∪
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) < Valued.v (z - algebraMap K₀ C c) ∧
          Valued.v (z - algebraMap K₀ C c) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1)))} ∪
        {z : C | Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ≤ Valued.v (z - algebraMap K₀ C a)}) ⊆
    ({z : C | Valued.v (z - algebraMap K₀ C c') ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∪
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) < Valued.v (z - algebraMap K₀ C c') ∧
          Valued.v (z - algebraMap K₀ C c') < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1)))} ∪
        {z : C | Valued.v (z - algebraMap K₀ C c') ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ≤ Valued.v (z - algebraMap K₀ C a)}) := by
  have hsub : ∀ z : C, z - algebraMap K₀ C c' = (z - algebraMap K₀ C c) + (algebraMap K₀ C c - algebraMap K₀ C c') :=
    fun z => by ring
  rintro z ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
  · refine Or.inl (Or.inl ⟨?_, h2⟩)
    rw [hsub]
    exact (Valuation.map_add _ _ _).trans (max_le h1 (hcc.trans hmm))
  · have hlt : Valued.v (algebraMap K₀ C c - algebraMap K₀ C c') < Valued.v (z - algebraMap K₀ C c) :=
      lt_of_le_of_lt hcc h1
    have e : Valued.v (z - algebraMap K₀ C c') = Valued.v (z - algebraMap K₀ C c) := by
      rw [hsub, Valuation.map_add_eq_of_lt_left _ hlt]
    exact Or.inl (Or.inr ⟨by rw [e]; exact h1, by rw [e]; exact h2⟩)
  · refine Or.inr ⟨?_, h2⟩
    rw [hsub]
    exact (Valuation.map_add _ _ _).trans (max_le h1 hcc)

end CerednikDrinfeld.Omega.CoverChainAux

open CerednikDrinfeld.Omega.CoverChainAux in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (k : ℕ) (P : Fin (k + 1) → Set C) (g : Fin (k + 1) → GL (Fin 2) K₀)
      (t π : Fin (k + 1) → C) (Z : Fin (k + 1) → Finset C),

      (∀ j, P j = (vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪
            vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j * edgeFlip K₀ ϖ)))) ∧

      (∀ j, ∃ (c : K₀) (m : ℤ), ((g j : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1]) ∧

      (∀ j, P j ⊆ affinoid ϖ n) ∧ (affinoid ϖ n ⊆ ⋃ j, P j) ∧

      (∀ j, j ≠ 0 → π j ≠ 0) ∧
      (∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i, Valued.v (π j) ≤ Valued.v (z - t j)) ∧
      (∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨ Valued.v (z - t j) < Valued.v (π j)) ∧
      (∀ j, j ≠ 0 → ∀ z : C, Valued.v (z - t j) = Valued.v (π j) →
        (∀ ζ ∈ Z j, Valued.v (π j) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i) := by
  classical
  have hϖ0 : ϖ.ϖ ≠ 0 := by
    intro h0; have := ϖ.pos; rw [h0, map_zero, map_zero] at this; exact lt_irrefl _ this
  have hvpow : ∀ l : ℤ, 0 < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ l)) := fun l =>
    zero_lt_iff.2 (by rw [ne_eq, map_eq_zero, map_eq_zero]; exact zpow_ne_zero l hϖ0)

  have hintK : ∀ y : K₀, IsLocalization.IsInteger R y ↔ Valued.v (algebraMap K₀ C y) ≤ 1 := by
    intro y
    constructor
    · rintro ⟨r, rfl⟩; exact hint r
    · exact hv y
  have hconv : ∀ (x : K₀) (l : ℤ), IsLocalization.IsInteger R (x / algebraMap R K₀ ϖ₀ ^ l) ↔
      Valued.v (algebraMap K₀ C x) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ l)) := by
    intro x l
    rw [hintK, ← hϖ, map_div₀, map_div₀, div_le_one₀ (hvpow l)]
  have hconv' : ∀ x : K₀, IsLocalization.IsInteger R (x * algebraMap R K₀ ϖ₀ ^ n) ↔
      Valued.v (algebraMap K₀ C x) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) := by
    intro x
    rw [← hconv, zpow_neg, zpow_natCast, div_inv_eq_mul]
  have hanti : ∀ l l' : ℤ, l ≤ l' → Valued.v (algebraMap K₀ C (ϖ.ϖ ^ l')) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ l)) := by
    intro l l' hll
    obtain ⟨d, rfl⟩ := Int.le.dest hll
    rw [zpow_add₀ hϖ0, zpow_natCast, map_mul, Valuation.map_mul, map_pow, Valuation.map_pow]
    exact mul_le_of_le_one_right' (pow_le_one₀ zero_le' ϖ.lt_one.le)

  obtain ⟨k, cen, lev, hcen0, hlev0, hmono, hdistA, hparA, hinA, hcovA⟩ :=
    CerednikDrinfeld.Omega.exists_fin_ballEdges R K₀ ϖ₀ hϖ₀ n hn

  have hdet : ∀ j, (!![ϖ.ϖ ^ (lev j - 1), cen j; 0, 1] : Matrix (Fin 2) (Fin 2) K₀).det ≠ 0 := fun j => by
    rw [Matrix.det_fin_two_of]; simpa using zpow_ne_zero (lev j - 1) hϖ0
  set g : Fin (k + 1) → GL (Fin 2) K₀ := fun j => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet j) with hgdef
  have hg : ∀ j, (g j : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (lev j - 1), cen j; 0, 1] := fun j => rfl
  set P : Fin (k + 1) → Set C := fun j =>
    vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪
      vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j * edgeFlip K₀ ϖ)) with hPdef
  have hP : ∀ j, P j = ({z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∪
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) < Valued.v (z - algebraMap K₀ C (cen j)) ∧
          Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))} ∪
        {z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ≤ Valued.v (z - algebraMap K₀ C a)}) := by
    intro j
    obtain ⟨e1, e2, e3⟩ := CerednikDrinfeld.Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine R K₀ C ϖ ϖ₀ hϖ₀ hϖ hint hv
      (cen j) (lev j) (g j) (hg j)
    show vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪
      vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j * edgeFlip K₀ ϖ)) = _
    rw [e1, e2, e3]

  obtain ⟨h4, h5, h6, Z, h7⟩ := CerednikDrinfeld.Omega.chain_clauses_of_ballEdges R K₀ C ϖ ϖ₀ hϖ₀ hϖ hint hv n k cen lev hlev0
    (fun j => (hconv' (cen j)).1 (hinA j).2.2)
    (fun j => (hinA j).1)
    hmono
    (fun i j hij hl => by
      have := hdistA i j hij hl
      rw [hconv, map_sub] at this
      exact not_le.1 this)
    (fun j => (hparA j).imp_right fun ⟨i, hi, hl, hint'⟩ => ⟨i, hi, hl, by
      have := (hconv _ _).1 hint'; rwa [map_sub] at this⟩)
    P hP
  refine ⟨k, P, g, fun j => algebraMap K₀ C (cen j), fun j => algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)), Z,
    fun j => rfl, fun j => ⟨cen j, lev j, hg j⟩, ?_, ?_, h4, h5, h6, h7⟩
  ·
    intro j
    exact (CerednikDrinfeld.Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion R K₀ C ϖ ϖ₀ hϖ₀ hϖ hint hv n hn).1
      (cen j) (lev j) (g j) (hg j) (hinA j).1 (hinA j).2.1 ((hconv' (cen j)).1 (hinA j).2.2)
  ·
    intro z hz
    obtain ⟨c, m, g', hg', hm1, hm2, hc, hzmem⟩ :=
      (CerednikDrinfeld.Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion R K₀ C ϖ ϖ₀ hϖ₀ hϖ hint hv n hn).2 z hz
    obtain ⟨j, hj, hcj⟩ := hcovA c m ⟨hm1, hm2, (hconv' c).2 hc⟩
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    obtain ⟨e1, e2, e3⟩ := CerednikDrinfeld.Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine R K₀ C ϖ ϖ₀ hϖ₀ hϖ hint hv
      c m g' hg'
    rw [e1, e2, e3] at hzmem
    subst hj
    rw [hP j]
    have hcc : Valued.v (algebraMap K₀ C c - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ lev j)) := by
      have := (hconv _ _).1 hcj; rwa [map_sub] at this
    exact region_subset_of_v_sub_le ϖ c (cen j) (lev j) hcc (hanti (lev j - 1) (lev j) (by omega)) hzmem

end S_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid (solution)
