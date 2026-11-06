-- Prove2me | solution 1 for BookProof.EsaPair.ESAPair.norm_sub_smul_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:05:13.866445+00:00
-- url     : https://prove2.me/submissions/8437c5ca-90a3-4f56-8ff3-39aa2563c563

import Definitions.Def_ChapterEsaPairDGamma
import Theorems.Thm_BookProof_FarisLavine_norm_sub_smul_sq

open BookProof.TensorCore
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem solution (d : ℝ) (x : P.coreDomain) :
    ‖P.toOp x - ((d : ℂ) * Complex.I) • (x : Hs.carrier)‖ ^ 2
      = ‖P.toOp x‖ ^ 2 + d ^ 2 * ‖(x : Hs.carrier)‖ ^ 2 := by
  exact BookProof.FarisLavine.norm_sub_smul_sq P.closureOp P.symmetric d
    ⟨x, P.sub_domain x.property⟩
