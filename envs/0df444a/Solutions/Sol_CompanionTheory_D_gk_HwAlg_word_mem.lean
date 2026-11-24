-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.word_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:34.917105+00:00
-- url     : https://prove2.me/submissions/a17ceba4-6db8-48bd-b631-3a4466972e6e

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Qr
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.HwAlg
variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}
namespace CompanionTheory.D.gk.HwAlg
theorem _root_.solution (F : Fin n → Fin n → Module.End ℂ U) (w : U) {l : List (Fin n × Fin n)} (hl : Lower l) :
    word F l w ∈ lowSpan F w :=
  Submodule.subset_span ⟨l, hl, rfl⟩
end CompanionTheory.D.gk.HwAlg
