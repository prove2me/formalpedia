-- Prove2me | solution 1 for BookProof.Prove2meReuse.ns_convolution_compact
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:59.592519+00:00
-- url     : https://prove2.me/submissions/5d90b8b3-7fee-4513-9feb-ff23021ad3c1

-- Generated from ChapterProve2meReuse.lean — solution of BookProof.Prove2meReuse.ns_convolution_compact
import Mathlib
import Definitions.Def_ChapterProve2meReuse
open BookProof.Prove2meReuse



open MeasureTheory
open scoped Convolution

set_option maxHeartbeats 1000000 in
theorem solution (H : RouteHypotheses) :
    ExistsConvolutionCompact := H.convolution_compact
