-- Prove2me | solution 1 for FD1D.dyadicTent_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:21.379725+00:00
-- url     : https://prove2.me/submissions/e194afbd-57c8-4d70-84a3-4876cc8c7201

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution {l p z : ℝ} (hp : 0 ≤ p)
    (hz : z ∉ Icc l (l + p)) :
    dyadicTent l p z = 0 := by
  have hzL : z ∉ Icc l (l + p / 2) := by
    intro h
    apply hz
    constructor <;> linarith [h.1, h.2]
  have hzR : z ∉ Ioc (l + p / 2) (l + p) := by
    intro h
    apply hz
    constructor <;> linarith [h.1, h.2]
  simp [dyadicTent, hzL, hzR]
end FD1D
