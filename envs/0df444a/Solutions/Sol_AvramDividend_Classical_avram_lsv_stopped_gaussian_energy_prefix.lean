-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_stopped_gaussian_energy_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:19:15.121936+00:00
-- url     : https://prove2.me/submissions/26e3dda7-186e-4840-b652-c660788c3af3

import Mathlib
open MeasureTheory Set
open scoped Topology
noncomputable section

/-
Proof adapted from contributors to dufeteller/lean-lsv,
LSV/LocalizedItoStoppingIdentity.lean,
OriginalLSVCoefficientValues.stoppedIntegrand_energy_prefix,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719 (22 November 2026 inspected).
Upstream licence CC BY 4.0. Changes: remove LSV-specific scalarTimeClamp,
use a direct real-line stopped field and pointwise indicator identity.
-/

theorem solution
    {Ω : Type*} (H : ℝ → Ω → ℝ) (τ : Ω → ℝ) (t : ℝ) (ω : Ω) :
    (∫ s in Ioc (0 : ℝ) t, (if s ≤ τ ω then H s ω else 0)^2) =
      ∫ s in Ioc (0 : ℝ) (min t (τ ω)), (H s ω)^2 := by
  classical
  have he : (fun s : ℝ => (if s ≤ τ ω then H s ω else 0)^2) =ᵐ[volume.restrict (Ioc 0 t)]
      (Iic (τ ω)).indicator (fun s => (H s ω)^2) := by
    apply ae_of_all
    intro s
    simp only [Set.indicator_apply, Set.mem_Iic]
    split_ifs <;> simp_all
  rw [integral_congr_ae he, setIntegral_indicator measurableSet_Iic]
  have hset : Ioc (0 : ℝ) t ∩ Iic (τ ω) = Ioc 0 (min t (τ ω)) := by
    ext s
    change ((0 < s ∧ s ≤ t) ∧ s ≤ τ ω) ↔ (0 < s ∧ s ≤ min t (τ ω))
    rw [le_min_iff]
    tauto
  rw [hset]

