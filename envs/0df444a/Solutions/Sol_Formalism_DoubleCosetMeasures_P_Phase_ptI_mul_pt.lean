-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.ptI_mul_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:10.49969+00:00
-- url     : https://prove2.me/submissions/d3a69fe7-a8a9-4060-b389-0bfb75000892

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mono_mul
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_eq_mono
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
theorem _root_.solution (s : List ℕ) (t : ℕ → Kˣ) : ptI s t * pt s t = (1 : Matrix _ _ K) := by
  rw [pt_eq_mono]
  ext a c
  rw [ptI, mono_mul]
  simp only [mono, revF_revF, blk_revF, Matrix.one_apply]
  by_cases h : c = a
  · subst h; simp
  · simp [h, Ne.symm h]
end Formalism.DoubleCosetMeasures.P.Phase
