-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.smul_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:02:12.809988+00:00
-- url     : https://prove2.me/submissions/1ec085c4-6150-47d9-82a3-8bc2bec9f971

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge
open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem solution {T : D →ₗ[ℂ] D} (r : ℝ)
    (hT : SymmetricOn D (D.subtype.comp T)) :
    SymmetricOn D (D.subtype.comp (((r : ℝ) : ℂ) • T)) := by
  intro x y
  simp only [SymmetricOn, LinearMap.comp_apply, LinearMap.smul_apply] at hT ⊢
  rw [LinearMap.map_smul, LinearMap.map_smul, inner_smul_left, inner_smul_right]
  rw [show (starRingEnd ℂ) ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) by simp]
  exact congrArg (fun z => ((r : ℝ) : ℂ) * z) (hT x y)
