-- Prove2me | solution 1 for BookProof.Prove2meReuse.qg_compact_spectral_edge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:20:01.998982+00:00
-- url     : https://prove2.me/submissions/8dd373a4-c2de-4341-b285-2b924a844cd2

-- Generated from ChapterProve2meReuse.lean — solution of BookProof.Prove2meReuse.qg_compact_spectral_edge
import Mathlib
import Definitions.Def_ChapterProve2meReuse
open BookProof.Prove2meReuse



open MeasureTheory
open scoped Convolution

set_option maxHeartbeats 1000000 in
theorem solution (H : RouteHypotheses) :
    CompactSymmetricOrthogonalEigenspace := H.compact_symmetric_orthogonal_eigenspace
