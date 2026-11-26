-- Prove2me | solution 1 for FD1D.TrajectoryBridge.trajectoryLaw_marginal_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:45:14.543183+00:00
-- url     : https://prove2.me/submissions/b2b06c29-0720-4c85-9028-b1f0c139ed89

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
    (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    Measure.map (fun path : ℕ → α => path (n + 1)) (trajectoryLaw μ₀ κ) =
      κ ∘ₘ Measure.map (fun path : ℕ → α => path n) (trajectoryLaw μ₀ κ) := by
  let P := trajectoryLaw μ₀ κ
  let pref : (ℕ → α) → ((i : Finset.Iic n) → α) :=
    Preorder.frestrictLe n
  let hP : IsProbabilityMeasure P := by
    dsimp [P, trajectoryLaw]
    infer_instance
  have hjoint :
      P.map pref ⊗ₘ historyKernel κ n =
        P.map (fun path => (pref path, path (n + 1))) := by
    simpa only [P, pref, trajectoryLaw] using
      (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => α) (μ₀ := μ₀) (κ := historyKernel κ) (a := n))
  have hsnd := congrArg Measure.snd hjoint
  rw [Measure.snd_compProd,
    Measure.snd_map_prodMk (show Measurable pref by fun_prop)] at hsnd
  rw [← hsnd]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [historyKernel, Kernel.comap_apply']
  dsimp only [pref, P]
  rw [lintegral_map
      (μ := trajectoryLaw μ₀ κ)
      (f := fun h : (i : Finset.Iic n) → α =>
        κ (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) s)
      (g := Preorder.frestrictLe n)
      ((κ.measurable_coe hs).comp
        (measurable_pi_apply
          (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)))
      (Preorder.measurable_frestrictLe n),
    lintegral_map
      (μ := trajectoryLaw μ₀ κ)
      (f := fun x : α => κ x s)
      (g := fun path : ℕ → α => path n)
      (κ.measurable_coe hs) (measurable_pi_apply n)]
  rfl
end FD1D.TrajectoryBridge
