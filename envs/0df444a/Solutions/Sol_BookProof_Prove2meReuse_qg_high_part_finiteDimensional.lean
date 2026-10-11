-- Prove2me | solution 1 for BookProof.Prove2meReuse.qg_high_part_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:21:23.111833+00:00
-- url     : https://prove2.me/submissions/4187b582-8744-4ca8-8d1d-df86e63547b4

-- Generated from ChapterProve2meReuse.lean — solution of BookProof.Prove2meReuse.qg_high_part_finiteDimensional
import Mathlib
import Definitions.Def_ChapterProve2meReuse
open BookProof.Prove2meReuse



open MeasureTheory
open scoped Convolution

set_option maxHeartbeats 1000000 in
theorem solution (H : RouteHypotheses) :
    CompactSymmetricHighPart := H.compact_symmetric_high_part
