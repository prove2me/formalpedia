-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.nset_sset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:29:32.022669+00:00
-- url     : https://prove2.me/submissions/69505272-bb12-423f-8216-073a4cdf67c6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution {r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : m ∈ Nset k r) : m ∈ Sset k r z := by
  refine ⟨1, ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩, m, hm, by simp⟩
  · simp [UH]
  · simp
  · simp
  · simp
end Formalism.FourierDecayAlt.P.Ux3
