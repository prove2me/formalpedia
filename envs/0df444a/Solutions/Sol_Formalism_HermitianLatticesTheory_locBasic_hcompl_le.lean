-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_hcompl_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:21:58.213795+00:00
-- url     : https://prove2.me/submissions/02faa729-d37f-409c-a6bb-f71ded093aeb

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (p : Ideal R) [p.IsPrime] :
    hcompl (K := K) p ≤ p.primeCompl := by
  unfold hcompl
  rw [Submonoid.closure_le]
  intro s hs
  exact hs.1
end Formalism.HermitianLatticesTheory
