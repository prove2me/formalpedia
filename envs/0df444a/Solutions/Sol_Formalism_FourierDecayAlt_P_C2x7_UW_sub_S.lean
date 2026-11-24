-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x7.UW_sub_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:39.592228+00:00
-- url     : https://prove2.me/submissions/c4bf5fee-db4f-4ccd-ac7d-dbe37d2690f4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x7
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩
end Formalism.FourierDecayAlt.P.C2x7
