-- Prove2me | solution 1 for FD1D.haarNodeTent_eq_zero_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:51.710508+00:00
-- url     : https://prove2.me/submissions/c9916fbc-43a4-4c7f-a043-cc2bfdccd2d1

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_eq_zero_of_not_mem
import Theorems.Thm_FD1D_haarNodeWidth_pos

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution {L : ℕ} (v : CompleteHaarNode L) {z : ℝ}
    (hz : z ∉ Icc (haarNodeLeft v) (haarNodeLeft v + haarNodeWidth v)) :
    haarNodeTent v z = 0 :=
  dyadicTent_eq_zero_of_not_mem (haarNodeWidth_pos v).le hz
end FD1D
