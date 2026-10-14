-- Prove2me | solution 2 for Freiman.gap_forcing_coverage_3
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T20:22:39.063785+00:00
-- url     : https://prove2.me/submissions/6c13cf55-34ac-4aa1-9ed3-eca4898f3c7b

import Definitions.Def_Freiman_gapCertificateData

/-!
Coverage certificate: every split node of the tree has its four children rooted
at the one-digit extensions 1, 2, 3, 4 of the parent, and every node has its
centre inside its word.
-/

namespace GapCoverageAux

open Freiman

/-- `gapCoverage` is decidable: at a leaf it is a comparison of naturals, and at
a split a conjunction of `GapState` equalities together with the coverage of the
four children. Structural recursion on the tree supplies the instance. -/
private def decCoverage : (t : GapTree) → Decidable (gapCoverage t)
  | .leaf s _ => by unfold gapCoverage; infer_instance
  | .split s left a b c d => by
      unfold gapCoverage
      haveI := decCoverage a; haveI := decCoverage b
      haveI := decCoverage c; haveI := decCoverage d
      infer_instance

instance : DecidablePred gapCoverage := decCoverage

end GapCoverageAux

open GapCoverageAux in
theorem solution : Freiman.gapCoverage Freiman.gapForcingTree3 := by decide
