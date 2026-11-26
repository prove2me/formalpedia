-- Prove2me | solution 1 for FD1D.cdfTransportArea_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:11.804804+00:00
-- url     : https://prove2.me/submissions/7285e3d3-4a1d-4a33-981c-408bbe7fb819

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution (f : ℝ → ℝ) :
    0 ≤ cdfTransportArea f :=
  integral_nonneg fun _ => abs_nonneg _
end FD1D
