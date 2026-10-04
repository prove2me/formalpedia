-- Prove2me | solution 1 for BirkhoffGlobalSection.EHConvex.corner_cert_part_09
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:27:08.608985+00:00
-- url     : https://prove2.me/submissions/0b5e459c-528e-4e19-81cb-340b5e1b74d5

import Definitions.Def_BirkhoffGlobalSection_CornerCertificate
open BirkhoffGlobalSection.TangentialHessian.Checker BirkhoffGlobalSection.TangentialHessian.Checker.Data

namespace BirkhoffGlobalSection.EHConvex.CornerPart09

set_option maxRecDepth 100000

/-- Chunk 0: 37 leaves. -/
theorem cornerK3_chunk0_ok :
    checkTree NP.centredEnc cornerK3 cornerK3_chunk0
      (lowerHalf cornerK3_box 0) = true := by
  decide +kernel

/-- Chunk 1: 39 leaves. -/
theorem cornerK3_chunk1_ok :
    checkTree NP.centredEnc cornerK3 cornerK3_chunk1
      (upperHalf cornerK3_box 0) = true := by
  decide +kernel

end BirkhoffGlobalSection.EHConvex.CornerPart09

open BirkhoffGlobalSection.EHConvex.CornerPart09 in
theorem solution :
    (checkTree NP.centredEnc cornerK3 cornerK3_chunk0 (lowerHalf cornerK3_box 0) = true) ∧
    (checkTree NP.centredEnc cornerK3 cornerK3_chunk1 (upperHalf cornerK3_box 0) = true) :=
  ⟨cornerK3_chunk0_ok, cornerK3_chunk1_ok⟩
