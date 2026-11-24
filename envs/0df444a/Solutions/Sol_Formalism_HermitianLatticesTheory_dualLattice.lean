-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.dualLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:44.86214+00:00
-- url     : https://prove2.me/submissions/1b835170-0368-4040-ac51-e5a40b5892e8

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_finitely_generated_projective_coords
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_basis
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_dualBasis
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_expand
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_repr
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : DualLattice := by
  intro R K V _ _ _ _ _ _ _ _ _ _ _ h hs hnd hst L hL
  classical
  have mem_dual : ∀ (M : Submodule R V) (x : V),
      x ∈ dual h M ↔ ∀ y ∈ M, ∃ r : R, algebraMap R K r = h y x := by
    intro M x
    simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]
  have hLfg := hL.fg
  have hLsp := hL.span_eq_top
  obtain ⟨s, hfs, b, hbi, hsL⟩ := dualLattice_basis (R := R) L hLsp
  have hbL : ∀ i, b i ∈ L := fun i => hsL (by rw [hbi]; exact i.2)
  obtain ⟨bs, hbs⟩ := dualLattice_dualBasis h hnd b
  obtain ⟨d, hd0, hdL⟩ := dualLattice_denom b L hLfg
  have hexp := dualLattice_expand h hnd b bs hbs
  have hdK : algebraMap R K d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K)]
    exact fun h0 => hd0 (IsFractionRing.injective R K h0)

  have hA : ∀ z ∈ Submodule.span R (Set.range b), ∀ j, ∃ r : R, algebraMap R K r = h z (bs j) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      refine ⟨if i = j then 1 else 0, ?_⟩
      rw [hbs]
      split_ifs <;> simp
    | zero => intro j; exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
      intro j
      obtain ⟨r1, hr1⟩ := ihx j
      obtain ⟨r2, hr2⟩ := ihy j
      exact ⟨r1 + r2, by rw [map_add, hr1, hr2, map_add, LinearMap.add_apply]⟩
    | smul r x _ ih =>
      intro j
      obtain ⟨r1, hr1⟩ := ih j
      obtain ⟨r', hr'⟩ := hst r
      refine ⟨r' * r1, ?_⟩
      rw [map_mul, hr', hr1, ← algebraMap_smul K r x, LinearMap.map_smulₛₗ₂]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]

  have hle : dual h L ≤ Submodule.span R (Set.range bs) := by
    intro x hx
    rw [hexp x]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := (mem_dual L x).mp hx (b j) (hbL j)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)
  have hfg : (dual h L).FG :=
    Submodule.FG.of_le (Submodule.fg_span (Set.finite_range bs)) hle

  have hbsK : ∀ j, bs j ∈ Submodule.span K (dual h L : Set V) := by
    intro j
    obtain ⟨d', hd'⟩ := hst d
    have hd'0 : algebraMap R K d' ≠ 0 := by rw [hd']; exact star_ne_zero.mpr hdK
    have hmem : d' • bs j ∈ dual h L := by
      rw [mem_dual]
      intro y hy
      obtain ⟨r, hr⟩ := hA _ (hdL y hy) j
      refine ⟨r, ?_⟩
      have e1 : h y (d' • bs j) = algebraMap R K d' * h y (bs j) := by
        rw [← algebraMap_smul K d' (bs j), LinearMap.map_smul, smul_eq_mul]
      have e2 : h (d • y) (bs j) = star (algebraMap R K d) * h y (bs j) := by
        rw [← algebraMap_smul K d y, LinearMap.map_smulₛₗ₂]
        simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      rw [hr, e1, e2, hd']
    have e : bs j = (algebraMap R K d')⁻¹ • (d' • bs j) := by
      rw [← algebraMap_smul K d' (bs j), smul_smul, inv_mul_cancel₀ hd'0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hspd : Submodule.span K (dual h L : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [hexp x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbsK j)
  refine ⟨⟨hfg, hspd⟩, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ((dualBasic R K V h hs hst).2.1 L)
    obtain ⟨n, g, f, hgf⟩ := finitely_generated_projective_coords L hLfg (IsFractionRing.injective R K)
    choose w hw using fun k => dualLattice_repr h hs b bs hbs L hbL d hd0 hdL (f k)
    have hwd : ∀ k, w k ∈ dual h L := by
      intro k
      rw [mem_dual]
      intro y hy
      obtain ⟨r', hr'⟩ := hst (f k ⟨y, hy⟩)
      refine ⟨r', ?_⟩
      rw [hr', ← hs.eq (w k) y, hw k y hy, starRingEnd_apply]
    let Pm : V →ₗ[K] V := ∑ k, (h (w k)).smulRight (g k : V)
    have hP : Pm = LinearMap.id := by
      refine LinearMap.ext_on hLsp ?_
      intro y hy
      have e := congrArg Subtype.val (hgf ⟨y, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      simp only [Pm, LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply, hw _ y hy, algebraMap_smul]
      exact e.symm
    intro x hx
    have ex : x = ∑ k, h (w k) x • (g k : V) := by
      have := LinearMap.congr_fun hP x
      simpa [Pm] using this.symm
    rw [ex]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := (mem_dual _ x).mp hx (w k) (hwd k)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (g k).2
  ·
    intro a ha
    have hsa : star a ≠ 0 := star_ne_zero.mpr ha
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    constructor
    · intro hx
      refine ⟨star a • x, ?_, by rw [smul_smul, inv_mul_cancel₀ hsa, one_smul]⟩
      rw [mem_dual] at hx ⊢
      intro z hz
      obtain ⟨r, hr⟩ := hx (a • z) ⟨z, hz, rfl⟩
      refine ⟨r, ?_⟩
      rw [hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [mem_dual] at hy ⊢
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨r, hr⟩ := hy z hz
      refine ⟨r, ?_⟩
      simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
      rw [hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hsa, one_mul]
end Formalism.HermitianLatticesTheory
