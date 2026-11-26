-- Prove2me | solution 1 for FD1D.HaarSupportNested.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:48.716099+00:00
-- url     : https://prove2.me/submissions/2f8651ca-b177-4d46-ae44-b1000a732f6e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
namespace HaarSupportNested
theorem _root_.solution {L : ℕ} {u v w : CompleteHaarNode L}
    (huv : HaarSupportNested u v) (hvw : HaarSupportNested v w) :
    HaarSupportNested u w :=
  fun _ hz => hvw (huv hz)
end HaarSupportNested
end FD1D
