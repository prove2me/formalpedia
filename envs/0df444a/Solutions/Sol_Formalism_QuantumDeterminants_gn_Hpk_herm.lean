-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_Hpk_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:45.522932+00:00
-- url     : https://prove2.me/submissions/5ce406df-f042-4a7d-8246-5d1212a6a83b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) : (Hpk k r).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Hpk, and_true]
  split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
end Formalism.QuantumDeterminants
