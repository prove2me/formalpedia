-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallA.volume_image_equivFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:39.835836+00:00
-- url     : https://prove2.me/submissions/da7d7c8d-2538-4b35-b7e3-7023773df11e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BallA
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]
private theorem volume_image_equivFun_eq_map_symm {ι : Type*} [Fintype ι] (B : Basis ι ℝ E)
    (s : Set E) : volume (B.equivFun '' s) = Measure.map B.equivFunL.symm volume s := by
  rw [LinearEquiv.image_eq_preimage_symm]
  exact (B.equivFunL.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm
private theorem volume_image_equivFun_fundamentalDomain_eq_one {ι : Type*} [Fintype ι] (B : Basis ι ℝ E) :
    volume (B.equivFun '' fundamentalDomain B) = 1 := by
  have h : B.equivFun '' fundamentalDomain B = Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_image, mem_fundamentalDomain, Set.mem_univ_pi]
    constructor
    · rintro ⟨m, hm, rfl⟩ i
      simpa [Basis.equivFun_apply] using hm i
    · intro hx
      refine ⟨B.equivFun.symm x, fun i ↦ ?_, B.equivFun.apply_symm_apply x⟩
      have hxi := congrFun (B.equivFun.apply_symm_apply x) i
      rw [Basis.equivFun_apply] at hxi
      rw [hxi]
      exact hx i
  rw [h, volume_pi_pi]
  simp
private theorem covolume_eq_addHaarScalarFactor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ν ν' : Measure E) [ν.IsAddHaarMeasure] [ν'.IsAddHaarMeasure] :
    ZLattice.covolume Λ ν =
      (Measure.addHaarScalarFactor ν ν' : ℝ) * ZLattice.covolume Λ ν' := by
  have h := Measure.isAddLeftInvariant_eq_smul ν ν'
  let b := Module.Free.chooseBasis ℤ Λ
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ ν (ZLattice.isAddFundamentalDomain b ν),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ ν' (ZLattice.isAddFundamentalDomain b ν')]
  generalize Measure.addHaarScalarFactor ν ν' = c at h ⊢
  rw [h]
  exact measureReal_nnreal_smul_apply _
end Formalism.HermitianLattices.Ext.L3.BallA
end
end

set_option autoImplicit false
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallA
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]
namespace Formalism.HermitianLattices.Ext.L3.BallA
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (s : Set E) :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) =
      μ s / ENNReal.ofReal (ZLattice.covolume L μ) := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (b.ofZLatticeBasis ℝ L).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have hcov : ZLattice.covolume L ν = 1 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν),
      measureReal_def, hν, ← volume_image_equivFun_eq_map_symm, volume_image_equivFun_fundamentalDomain_eq_one,
      ENNReal.toReal_one]
  rw [volume_image_equivFun_eq_map_symm, ← hν, covolume_eq_addHaarScalarFactor_mul_covolume L μ ν, hcov, mul_one,
    ENNReal.ofReal_coe_nnreal]
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  generalize Measure.addHaarScalarFactor μ ν = c at hc h ⊢
  have hc0 : (c : ENNReal) ≠ 0 := by simpa using hc.ne'
  rw [h, Measure.coe_nnreal_smul_apply, mul_comm, ENNReal.mul_div_cancel_right hc0 ENNReal.coe_ne_top]
end Formalism.HermitianLattices.Ext.L3.BallA
