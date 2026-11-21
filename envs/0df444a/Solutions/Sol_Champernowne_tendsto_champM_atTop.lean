-- Prove2me | solution 1 for Champernowne.tendsto_champM_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:20.263032+00:00
-- url     : https://prove2.me/submissions/32d2ee24-87c6-452a-a922-892806fd9e4a

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_tendsto_champIndex_atTop

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) :
    Tendsto (champM b) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  have h10 : Tendsto (fun n => champIndex b n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (champIndex b n))
      (tendsto_champIndex_atTop b)
  filter_upwards [h10.eventually_ge_atTop (b ^ K)] with n hn
  have hn' : b ^ K ≤ champIndex b n + 1 := hn
  have hlog := (Nat.le_log_iff_pow_le hb
    (show champIndex b n + 1 ≠ 0 by omega)).mpr hn'
  change K ≤ Nat.log b (champIndex b n + 1) + 1
  omega
end Champernowne
