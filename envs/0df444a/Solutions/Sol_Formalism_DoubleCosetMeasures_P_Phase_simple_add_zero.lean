-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.simple_add_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:12.301677+00:00
-- url     : https://prove2.me/submissions/798d0bce-ea6f-4e52-8224-6b4c64daa43f

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
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
theorem _root_.solution {n : ℕ} {y z : Matrix (Fin n) (Fin n) K} (hy : IsUpUni y)
    (hz : IsUpUni z) (hyz : y * z = 1) (j k : Fin n) (hk : (k : ℕ) = j + 1) :
    y j k + z j k = 0 := by
  have hjk : j ≠ k := by
    intro h'
    rw [h'] at hk
    omega
  have h := congrFun (congrFun hyz j) k
  rw [Matrix.mul_apply, Matrix.one_apply_ne hjk, Fintype.sum_eq_add j k hjk ?_] at h
  · rw [hy.2 j, hz.2 k] at h
    linear_combination h
  · intro c ⟨hcj, hck⟩
    rcases lt_or_gt_of_ne hcj with hc | hc
    · rw [up_zero hy hc, zero_mul]
    · have hc' : (j : ℕ) < c := hc
      have hck' : (c : ℕ) ≠ k := fun h' => hck (Fin.ext h')
      have hkc : k < c := by
        show (k : ℕ) < c
        omega
      rw [up_zero hz hkc, mul_zero]
end Formalism.DoubleCosetMeasures.P.Phase
