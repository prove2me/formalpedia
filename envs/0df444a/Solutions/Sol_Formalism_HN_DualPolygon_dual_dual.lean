-- Prove2me | solution 1 for Formalism.HN.DualPolygon.dual_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:21.00311+00:00
-- url     : https://prove2.me/submissions/f4d535ea-7a31-4b38-81cb-e49e7d735c8b

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_dualFrame_unit
import Theorems.Thm_Formalism_HN_DualPolygon_dualLat_fg
import Theorems.Thm_Formalism_HN_DualPolygon_dualLat_span
import Theorems.Thm_Formalism_HN_DualPolygon_ht_dual
import Theorems.Thm_Formalism_HN_DualPolygon_realize_eval
import Theorems.Thm_Formalism_F_covolPos
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_shiftInv_zl_mono
import Theorems.Thm_Formalism_RankSupermodularCovolume_covol_eq_relIndex_mul_covol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) = A := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set A2 := (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) with hA2
  set e := Module.evalEquiv K V with he
  have hee : ∀ x, e x = Module.Dual.eval K V x := fun x => rfl
  have hAA2 : A ≤ A2 := by
    intro x hx f hf
    exact hf x hx
  have hdfg := dualLat_fg A hsp
  have hdsp := dualLat_span A hA hsp
  have hddfg : (dualLat (dualLat A)).FG := dualLat_fg (dualLat A) hdsp
  have hddsp := dualLat_span (dualLat A) hdfg hdsp
  have hmap : A2.map (e.toLinearMap.restrictScalars (𝓞 K)) = dualLat (dualLat A) := by
    apply Submodule.map_comap_eq_of_surjective
    exact e.surjective
  have hA2fg : A2.FG := by
    have : A2 = (dualLat (dualLat A)).map (e.symm.toLinearMap.restrictScalars (𝓞 K)) := by
      ext x
      simp only [hA2, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        rw [← hee, e.apply_symm_apply]
        exact hy
    rw [this]
    exact hddfg.map _
  have hA2sp : Submodule.span K (A2 : Set V) = ⊤ :=
    eq_top_iff.2 (hsp ▸ Submodule.span_mono hAA2)

  have hht1 := ht_dual b X hX A hA hsp
  have hht2 := ht_dual b.dualBasis (dualFrame X) hX' (dualLat A) hdfg hdsp
  have hzl : zl (Formalism.HermitianLatticesTheory.realize b.dualBasis.dualBasis (dualFrame (dualFrame X)))
      (dualLat (dualLat A)) = zl (Formalism.HermitianLatticesTheory.realize b X) A2 := by
    rw [← hmap]
    ext w
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (realize_eval b X hX x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, realize_eval b X hX x⟩
  have hrk1 : rkK (dualLat (dualLat A)) = finrank K V := by
    unfold rkK
    rw [hddsp, finrank_top, Subspace.dual_finrank_eq, Subspace.dual_finrank_eq]
  have hrk2 : rkK A2 = finrank K V := by unfold rkK; rw [hA2sp, finrank_top]
  have hrkA : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hhtA2 : ht b X A2 = ht b X A := by
    have h3 : ht b.dualBasis.dualBasis (dualFrame (dualFrame X)) (dualLat (dualLat A)) =
        ht b X A2 := by
      unfold ht; rw [hzl, hrk1, hrk2]
    rw [← h3]
    have hpos : 0 < ht b.dualBasis (dualFrame X) (dualLat A) :=
      (place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg).2.2
    field_simp at hht1 hht2 ⊢
    nlinarith [hht1, hht2, hpos]

  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hcovEq : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A2) =
      Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) := by
    unfold ht at hhtA2
    rw [hrk2, hrkA] at hhtA2
    have hc : (0 : ℝ) < (2 : ℝ) ^ (nPl K * finrank K V) *
        |(NumberField.discr K : ℝ)| ^ (-(finrank K V : ℝ) / 2) := by positivity
    exact mul_left_cancel₀ hc.ne' hhtA2
  obtain ⟨hlat2, hrkz2, -⟩ := place_lattice_structure K V ι b X hX A2 hA2fg
  obtain ⟨hlat1, hrkz1, -⟩ := place_lattice_structure K V ι b X hX A hA
  haveI := hlat2.2
  have hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A2) := by
    have h : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A2 := by
      rw [hrkz1, hrkz2, hrkA, hrk2]
    exact h
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _
    (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hAA2) hrkeq
  have hpos := Formalism.F.covolPos _ _ hlat2.2
  rw [hcovEq] at hcov
  have hidx1 : ((zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex
      (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup : ℝ) = 1 := by
    have hp1 : 0 < Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) := by rw [← hcovEq]; exact hpos
    field_simp at hcov
    nlinarith [hcov, hp1]
  have hinj := Formalism.HN.PlaceLattice.realize_injective b X hX
  have hidx : A.toAddSubgroup.relIndex A2.toAddSubgroup = 1 := by
    have h : (zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex
        (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup = A.toAddSubgroup.relIndex A2.toAddSubgroup := by
      simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
      exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
    rw [← h]
    exact_mod_cast hidx1
  have hle : A2.toAddSubgroup ≤ A.toAddSubgroup := AddSubgroup.relIndex_eq_one.1 hidx
  exact le_antisymm (fun x hx => hle hx) hAA2
end Formalism.HN.DualPolygon
