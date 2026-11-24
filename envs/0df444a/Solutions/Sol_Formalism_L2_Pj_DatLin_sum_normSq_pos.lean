-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.sum_normSq_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:57.794725+00:00
-- url     : https://prove2.me/submissions/49fa8a30-559b-46ec-85e2-151ab85eadec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution {w : m → ℂ} (hw : w ≠ 0) : 0 < ∑ i, Complex.normSq (w i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
end Formalism.L2.Pj.DatLin
