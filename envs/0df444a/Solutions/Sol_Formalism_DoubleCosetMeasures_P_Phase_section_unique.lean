-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.section_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:12.922796+00:00
-- url     : https://prove2.me/submissions/1b56ba04-99ce-4b84-b956-3ccdbb9df9af

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_mul_ptI
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_ptI_mul_pt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_eq_one_of_low_up
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_inv_mul_one_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_inv_mul_one_up
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution (s : List ℕ) (t : ℕ → Kˣ) {v u h v' u' h' : Matrix (Fin s.sum) (Fin s.sum) K}
    (hh : IsLowUni h) (hh' : IsLowUni h') (hu : IsUpUni u) (hu' : IsUpUni u')
    (hvw : v * pt s t = pt s t * h) (hvw' : v' * pt s t = pt s t * h')
    (heq : v' * pt s t * u' = v * pt s t * u) : v' = v ∧ u' = u := by
  have e1 : h' * u' = h * u := by
    have e0 : pt s t * (h' * u') = pt s t * (h * u) := by
      rw [← Matrix.mul_assoc, ← hvw', ← Matrix.mul_assoc, ← hvw, heq]
    calc h' * u' = ptI s t * (pt s t * (h' * u')) := by
          rw [← Matrix.mul_assoc, ptI_mul_pt, Matrix.one_mul]
      _ = ptI s t * (pt s t * (h * u)) := by rw [e0]
      _ = h * u := by rw [← Matrix.mul_assoc, ptI_mul_pt, Matrix.one_mul]
  have e2 : h⁻¹ * h' = u * u'⁻¹ := by
    calc h⁻¹ * h' = h⁻¹ * h' * (u' * u'⁻¹) := by rw [mul_inv_one_up hu', Matrix.mul_one]
      _ = h⁻¹ * (h' * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = h⁻¹ * (h * u) * u'⁻¹ := by rw [e1]
      _ = u * u'⁻¹ := by rw [← Matrix.mul_assoc h⁻¹ h, inv_mul_one_low hh, Matrix.one_mul]
  have hl : IsLowUni (h⁻¹ * h') := isLowUni_mul K (isLowUni_inv K hh) hh'
  have hup : IsUpUni (u * u'⁻¹) := isUpUni_mul K hu (isUpUni_inv K hu')
  have e3 : h⁻¹ * h' = 1 := eq_one_of_low_up hl (e2 ▸ hup)
  have e4 : u * u'⁻¹ = 1 := e2 ▸ e3
  have hheq : h' = h := by
    calc h' = h * (h⁻¹ * h') := by rw [← Matrix.mul_assoc, mul_inv_one_low hh, Matrix.one_mul]
      _ = h := by rw [e3, Matrix.mul_one]
  have hueq : u' = u := by
    calc u' = u * u'⁻¹ * u' := by rw [e4, Matrix.one_mul]
      _ = u := by rw [Matrix.mul_assoc, inv_mul_one_up hu', Matrix.mul_one]
  refine ⟨?_, hueq⟩
  calc v' = v' * pt s t * ptI s t := by rw [Matrix.mul_assoc, pt_mul_ptI, Matrix.mul_one]
    _ = pt s t * h' * ptI s t := by rw [hvw']
    _ = v * pt s t * ptI s t := by rw [hheq, hvw]
    _ = v := by rw [Matrix.mul_assoc, pt_mul_ptI, Matrix.mul_one]
end Formalism.DoubleCosetMeasures.P.Phase
