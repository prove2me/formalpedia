-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:09.118692+00:00
-- url     : https://prove2.me/submissions/0169035f-16a8-43fd-bd5c-988dfcd73ad1

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mono_mul
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_mono
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
theorem _root_.solution (s : List ℕ) (t : ℕ → Kˣ) (M : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : (ptI s t * M * pt s t) a c =
      (((t (blk s a))⁻¹ : Kˣ) : K) * M (revF s a) (revF s c) * ((t (blk s c) : Kˣ) : K) := by
  rw [pt_eq_mono, mul_mono, ptI, mono_mul]
  simp only [blk_revF]
end Formalism.DoubleCosetMeasures.P.Phase
