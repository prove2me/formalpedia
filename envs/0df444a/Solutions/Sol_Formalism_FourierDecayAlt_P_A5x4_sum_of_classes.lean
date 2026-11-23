-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.sum_of_classes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:59.060799+00:00
-- url     : https://prove2.me/submissions/0488ac3a-c8cc-43f2-86a1-a4eca5db4310

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {T Q : Type} [Fintype T] [Fintype Q] [DecidableEq Q] (f : T → Q)
    (μ : Q → ℝ) (c : T → ℂ) :
    ∑ i, ∑ j, c i * conj (c j) * (if f i = f j then (μ (f i) : ℂ) else 0) =
      ((∑ κ, μ κ * Complex.normSq (∑ i, if f i = κ then c i else 0) : ℝ) : ℂ) := by
  have h : ∀ κ, ((μ κ * Complex.normSq (∑ i, if f i = κ then c i else 0) : ℝ) : ℂ) =
      ∑ i, ∑ j, (μ κ : ℂ) * ((if f i = κ then c i else 0) *
        conj (if f j = κ then c j else 0)) := by
    intro κ
    rw [Complex.ofReal_mul, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun κ _ => h κ,
    Finset.sum_comm (s := (Finset.univ : Finset Q))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset Q))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (f i)]
  · by_cases h : f i = f j
    · simp [h]; ring
    · have h' : ¬ f j = f i := fun e => h e.symm
      simp [h, h']
  · intro κ _ hκ
    have : ¬ f i = κ := fun e => hκ e.symm
    simp [this]
  · simp
end Formalism.FourierDecayAlt.P.A5x4
