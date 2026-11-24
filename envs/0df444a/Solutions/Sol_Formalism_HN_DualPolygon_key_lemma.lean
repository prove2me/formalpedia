-- Prove2me | solution 1 for Formalism.HN.DualPolygon.key_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:01.090173+00:00
-- url     : https://prove2.me/submissions/c62ae9d6-a15b-438f-9838-ea920ef98115

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
import Theorems.Thm_Formalism_HN_DualPolygon_cE_cE
import Theorems.Thm_Formalism_HN_DualPolygon_inner_cE
import Theorems.Thm_Formalism_HN_DualPolygon_dualZ_zl_eq
import Theorems.Thm_Formalism_HN_DualPolygon_dualZ_inf_orth
import Theorems.Thm_Formalism_HN_DualPolygon_covol_map_scaled
import Theorems.Thm_Formalism_HN_DualPolygon_dual_inf_ann_eq
import Theorems.Thm_Formalism_HN_DualPolygon_twist_span_smul
import Theorems.Thm_Formalism_HN_DualPolygon_twist_index
import Theorems.Thm_Formalism_HN_DualPolygon_dualFrame_unit
import Theorems.Thm_Formalism_HN_DualPolygon_dualLat_fg
import Theorems.Thm_Formalism_HN_DualPolygon_eq_mul_of_log_eq_add
import Theorems.Thm_Formalism_F_covolPos
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_F_discreteTopology_of_le
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_duality_basic
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
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    rkK (dualLat A ⊓ annO N) + rkK N = finrank K V ∧
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N)) *
              Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) *
              2 ^ (finrank ℚ K * rkK (dualLat A ⊓ annO N)) =
      |(NumberField.discr K : ℝ)| ^ rkK (dualLat A ⊓ annO N) *
        Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) with hρ'
  set Rp := tdualLat A ⊓ annO N with hRp
  set R := dualLat A ⊓ annO N with hR
  set 𝔡 := differentIdeal ℤ (𝓞 K) with h𝔡
  have h𝔡0 : 𝔡 ≠ ⊥ := differentIdeal_ne_bot
  have hRdR : R = 𝔡 • Rp := dual_inf_ann_eq A N
  have hNA : N ≤ A := hN.1
  have hNfg : N.FG := Submodule.FG.of_le hA hNA
  have hdfg : (dualLat A).FG := dualLat_fg A hsp
  have hRfg : R.FG := Submodule.FG.of_le hdfg inf_le_left
  have hRpfg : Rp.FG := by
    set m : ℕ := Ideal.absNorm 𝔡 with hm
    have hm0 : m ≠ 0 := fun h => h𝔡0 (Ideal.absNorm_eq_zero_iff.1 h)
    have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
    have hmem : (m : 𝓞 K) ∈ 𝔡 := Ideal.absNorm_mem 𝔡
    let ψ : Module.Dual K V →ₗ[𝓞 K] Module.Dual K V :=
      (((m : K)⁻¹) • (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V)).restrictScalars (𝓞 K)
    refine Submodule.FG.of_le (hdfg.map ψ) ?_
    intro g hg
    refine ⟨(m : 𝓞 K) • g, ?_, ?_⟩
    · have : (m : 𝓞 K) • g ∈ R := by rw [hRdR]; exact Submodule.smul_mem_smul hmem hg
      exact this.1
    · show ((m : K)⁻¹) • ((m : 𝓞 K) • g) = g
      rw [← algebraMap_smul K ((m : 𝓞 K)) g, map_natCast, smul_smul, inv_mul_cancel₀ hmK, one_smul]
  have hspR : Submodule.span K (R : Set (Module.Dual K V)) = Submodule.span K (Rp : Set _) := by
    rw [hRdR]; exact twist_span_smul Rp 𝔡 h𝔡0
  have hrkR : rkK R = rkK Rp := by unfold rkK; rw [hspR]
  obtain ⟨hlatA, hrkA, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨hlatN, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  obtain ⟨hlatR, hrkR', -⟩ := place_lattice_structure K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' R hRfg
  obtain ⟨hlatRp, hrkRp', -⟩ :=
    place_lattice_structure K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' Rp hRpfg
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  set L := zl ρ A with hL
  set S := zl ρ N with hS
  haveI hLd : DiscreteTopology L := hlatA.2
  have hSsat : Formalism.F.IsSaturated L S := hN.2
  obtain ⟨hQd, hrkQ, hdegQ⟩ := Formalism.F.degQuot _ L S hLd hSsat
  haveI := hQd
  obtain ⟨hDd, hrkD, hdegD, -⟩ := duality_basic (Formalism.F.quot L S)
  haveI := hDd
  have hSL : S ≤ L := hSsat.1
  have hE1 := dualZ_inf_orth L S hSL
  have hE2 := dualZ_zl_eq b X hX A hA hsp N
  set M' := zl ρ' Rp with hM'def
  set φ2 : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE with hφ2
  set φh : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := ((1 : ℝ) / 2) • cE with hφh
  have hcomp : φh.restrictScalars ℤ ∘ₗ φ2.restrictScalars ℤ = LinearMap.id := by
    ext w
    simp only [hφh, hφ2, LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.smul_apply, map_smul, cE_cE, smul_smul, LinearMap.id_apply]
    norm_num
  have hM' : M' = (dualZ (Formalism.F.quot L S)).map (φh.restrictScalars ℤ) := by
    rw [← hE1, hE2, ← Submodule.map_comp, hcomp, Submodule.map_id]
  have hφhi : ∀ x y, inner ℝ (φh x) (φh y) = ((1 : ℝ) / 2) ^ 2 * inner ℝ x y := by
    intro x y
    simp only [hφh, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, inner_cE]
    ring
  obtain ⟨hM'd, hrkM', hcovM'⟩ :=
    covol_map_scaled φh ((1 : ℝ) / 2) (by norm_num) hφhi (dualZ (Formalism.F.quot L S))
  rw [← hM'] at hM'd hrkM' hcovM'
  haveI := hM'd
  have hRRp : R ≤ Rp := by rw [hRdR]; exact Submodule.smul_le_right
  have hzlle : zl ρ' R ≤ M' := shiftInv_zl_mono ρ' hRRp
  have hn0 : 0 < finrank ℚ K := Module.finrank_pos
  have hrkeq : Formalism.F.rk (zl ρ' R) = Formalism.F.rk M' := by
    have h1 : Formalism.HN.rk ρ' R = Formalism.HN.rk ρ' Rp := by rw [hrkR', hrkRp', hrkR]
    exact h1
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol (zl ρ' R) M' hzlle hrkeq
  have hρ'inj := Formalism.HN.PlaceLattice.realize_injective b.dualBasis (dualFrame X) hX'
  have hidx : (zl ρ' R).toAddSubgroup.relIndex M'.toAddSubgroup =
      R.toAddSubgroup.relIndex Rp.toAddSubgroup := by
    simp only [hM'def, zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hρ'inj
  have htw : R.toAddSubgroup.relIndex Rp.toAddSubgroup = Ideal.absNorm 𝔡 ^ rkK Rp := by
    rw [hRdR]; exact twist_index Rp hRpfg 𝔡 h𝔡0
  have hnorm : (Ideal.absNorm 𝔡 : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [h𝔡, NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]

  have hSd : DiscreteTopology S := Formalism.F.discreteTopology_of_le hSL
  have hcL := Formalism.F.covolPos _ L hLd
  have hcS := Formalism.F.covolPos _ S hSd
  have hcQ := Formalism.F.covolPos _ _ hQd
  have hcD := Formalism.F.covolPos _ _ hDd
  have hLSQ : Formalism.F.covol L = Formalism.F.covol S * Formalism.F.covol (Formalism.F.quot L S) := by
    apply eq_mul_of_log_eq_add hcL hcS hcQ
    unfold Formalism.F.deg at hdegQ
    linarith
  have hDQ : Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S) = 1 := by
    have h1 : Real.log (Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S)) = 0 := by
      rw [Real.log_mul hcD.ne' hcQ.ne']
      unfold Formalism.F.deg at hdegD
      linarith
    have h2 := Real.eq_one_of_pos_of_log_eq_zero (mul_pos hcD hcQ) h1
    exact h2

  have hrkL : Formalism.F.rk L = finrank ℚ K * finrank K V := by
    have : Formalism.HN.rk ρ A = _ := hrkA
    rw [hrkAd] at this
    exact this
  have hrkS : Formalism.F.rk S = finrank ℚ K * rkK N := hrkN
  have hrkM'2 : Formalism.F.rk M' = finrank ℚ K * rkK Rp := hrkRp'
  have hrkQ' : Formalism.F.rk (Formalism.F.quot L S) = finrank ℚ K * rkK Rp := by
    rw [← hrkM'2, hrkM', hrkD]
  have hdim : rkK Rp + rkK N = finrank K V := by
    have h1 : finrank ℚ K * finrank K V = finrank ℚ K * rkK N + finrank ℚ K * rkK Rp := by
      rw [← hrkL, ← hrkS, ← hrkQ', hrkQ]
    have h2 : finrank ℚ K * finrank K V = finrank ℚ K * (rkK Rp + rkK N) := by rw [h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hn0 h2).symm
  refine ⟨by rw [hrkR]; exact hdim, ?_⟩
  rw [hcov, hidx, htw, hrkR, hcovM', hrkD, hrkQ', Nat.cast_pow, hnorm, hLSQ]
  have h2 : ((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * 2 ^ (finrank ℚ K * rkK Rp) = 1 := by
    rw [← mul_pow]; norm_num
  calc |(NumberField.discr K : ℝ)| ^ rkK Rp *
          (((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * Formalism.F.covol (dualZ (Formalism.F.quot L S))) *
          (Formalism.F.covol S * Formalism.F.covol (Formalism.F.quot L S)) * 2 ^ (finrank ℚ K * rkK Rp)
        = |(NumberField.discr K : ℝ)| ^ rkK Rp * Formalism.F.covol S *
          (Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S)) *
          (((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * 2 ^ (finrank ℚ K * rkK Rp)) := by ring
    _ = _ := by rw [hDQ, h2]; ring
end Formalism.HN.DualPolygon
