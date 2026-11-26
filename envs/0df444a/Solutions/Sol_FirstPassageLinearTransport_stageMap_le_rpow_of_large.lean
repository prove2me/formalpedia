-- Prove2me | solution 1 for FirstPassageLinearTransport.stageMap_le_rpow_of_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:29.039783+00:00
-- url     : https://prove2.me/submissions/421bdb09-d430-4630-be7f-83b0d1f8760b

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell_log
import Theorems.Thm_FirstPassageLinearTransport_mem_initialWindowGood_of_mem_extended_of_large
import Theorems.Thm_FirstPassageLinearTransport_stageLength_isFirstPassage
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p)
    (hlarge : p.M0 ≤ Nat.log 2 n) :
    (stageMap p n : ℝ) ≤ (n : ℝ) ^ r := by
  let M := Nat.log 2 n
  have hshell : n ∈ dyadicShell M := mem_dyadicShell_log hn
  have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW hlarge
  have hfp := stageLength_isFirstPassage p hlarge hshell hgood
  have hstage : (stageMap p n : ℝ) ≤ targetScale r M := by
    exact_mod_cast hfp.1
  have hrM0 : 0 ≤ r * (M : ℝ) :=
    mul_nonneg p.r_pos.le (Nat.cast_nonneg M)
  have hfloor : (⌊r * (M : ℝ)⌋₊ : ℝ) ≤ r * M :=
    Nat.floor_le hrM0
  have htarget : (targetScale r M : ℝ) ≤ (2 : ℝ) ^ (r * M) := by
    unfold targetScale
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
  have hbase : (2 : ℝ) ^ M ≤ n := by
    exact_mod_cast (mem_dyadicShell.mp hshell).1
  have hpow : (2 : ℝ) ^ (r * M) ≤ (n : ℝ) ^ r := by
    calc
      (2 : ℝ) ^ (r * M) = (2 : ℝ) ^ ((M : ℝ) * r) := by ring_nf
      _ = ((2 : ℝ) ^ M) ^ r := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ (n : ℝ) ^ r :=
        Real.rpow_le_rpow (by positivity) hbase p.r_pos.le
  exact hstage.trans (htarget.trans hpow)
end FirstPassageLinearTransport
