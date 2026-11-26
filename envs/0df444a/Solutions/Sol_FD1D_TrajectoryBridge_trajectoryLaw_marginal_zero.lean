-- Prove2me | solution 1 for FD1D.TrajectoryBridge.trajectoryLaw_marginal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:43:28.238982+00:00
-- url     : https://prove2.me/submissions/68a37649-0161-4959-9284-630216764adb

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Definitions.Def_FD1D_TrajectoryBridge

set_option autoImplicit true
open FD1D FD1D.TrajectoryBridge
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
namespace FD1D.TrajectoryBridge
theorem _root_.solution
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] :
    Measure.map (fun path : ℕ → α => path 0) (trajectoryLaw μ₀ κ) = μ₀ := by
  rw [trajectoryLaw, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_pi_apply 0)]
  have hmap :
      (Kernel.traj (historyKernel κ) 0).map
          (fun path : ℕ → α => path 0) =
        Kernel.deterministic
          (fun h : (i : Finset.Iic 0) → α => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
          (by fun_prop) := by
    have heval :
        (fun path : ℕ → α => path 0) =
          (fun h : (i : Finset.Iic 0) → α =>
            h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
            Preorder.frestrictLe 0 := by
      rfl
    rw [heval, Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0)
        (measurable_pi_apply ⟨0, Finset.mem_Iic.mpr le_rfl⟩),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
      Kernel.id_map]
  rw [hmap, Measure.deterministic_comp_eq_map]
  rw [Measure.map_map
    (measurable_pi_apply ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm.measurable]
  have hcomp :
      (fun h : (i : Finset.Iic 0) → α =>
        h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm = id := by
    funext x
    rfl
  rw [hcomp, Measure.map_id]
end FD1D.TrajectoryBridge
