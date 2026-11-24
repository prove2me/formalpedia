-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capelli_central_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:52:05.78091+00:00
-- url     : https://prove2.me/submissions/c208d770-12dc-4477-9a3b-c85753b6fd78

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Theorems.Thm_Formalism_QuantumDeterminants_ioE_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_mk
import Theorems.Thm_Formalism_QuantumDeterminants_io_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_gl
import Theorems.Thm_Formalism_REAL_qDetCentral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CapCentral := by
  intro n ε E _ _ f u c d g hf hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hq := qDetCentral (Module.End ℂ (ioS ε E)) n (ioE ε E) (io_gl ε E) u c d
  calc capelli ε u (EabV ε c d f) g
      = (qminor (ioE ε E) id id u (ioE ε E c d x) : IOPt ε → E) ⟨g, hg⟩ :=
        io_qminor_rep id id u (ioE_rep hx c d) g hg
    _ = (ioE ε E c d (qminor (ioE ε E) id id u x) : IOPt ε → E) ⟨g, hg⟩ :=
        congrArg (fun y : ioS ε E => (y : IOPt ε → E) ⟨g, hg⟩) (LinearMap.congr_fun hq x)
    _ = EabV ε c d (capelli ε u f) g := (ioE_rep (io_qminor_rep id id u hx) c d g hg).symm
end Formalism.QuantumDeterminants
