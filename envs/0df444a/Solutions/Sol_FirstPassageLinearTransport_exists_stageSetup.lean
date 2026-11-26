-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_stageSetup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:29.038808+00:00
-- url     : https://prove2.me/submissions/9d7bbcf9-f751-4483-bc07-ce5953d28cfa

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Theorems.Thm_FirstPassageLinearTransport_central_terminal_identity
import Theorems.Thm_FirstPassageLinearTransport_eventually_horizon_small
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ}
    (ha0r : a0 < r) (hr1 : r < 1)
    (heta0 : 0 < eta) (hetaGap : eta < r - a0) :
    Nonempty (StageSetup r eta) := by
  have hr0 : 0 < r := a0_pos.trans ha0r
  have heta1 : eta ≤ 1 := by linarith [a0_pos]
  let g := r - a0 - eta
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨Mlin : ℕ, hMlin⟩ := exists_nat_gt ((2 + eta) / g)
  obtain ⟨Mone : ℕ, hMone⟩ := exists_nat_gt (2 / r)
  obtain ⟨Mhor : ℕ, hMhor⟩ :=
    (Filter.eventually_atTop.1 (eventually_horizon_small hr0))
  let M0 := max 1 (max Mlin (max Mone Mhor))
  have hM0one : 1 ≤ M0 := le_max_left _ _
  have hM0lin : Mlin ≤ M0 :=
    (le_max_left Mlin (max Mone Mhor)).trans (le_max_right 1 _)
  have hM0oneScale : Mone ≤ M0 :=
    (le_max_left Mone Mhor).trans
      ((le_max_right Mlin _).trans (le_max_right 1 _))
  have hM0hor : Mhor ≤ M0 :=
    (le_max_right Mone Mhor).trans
      ((le_max_right Mlin _).trans (le_max_right 1 _))
  refine ⟨{
    M0 := M0
    r_pos := hr0
    r_lt_one := hr1
    eta_pos := heta0
    eta_le_one := heta1
    target_one_lt := ?_
    target_lt_shell := ?_
    horizon_small := ?_
    terminal_budget := ?_ }⟩
  · intro M hM
    have hMoneLe : Mone ≤ M := hM0oneScale.trans hM
    have hMR : (Mone : ℝ) ≤ M := by exact_mod_cast hMoneLe
    have hlarge : 2 < r * (M : ℝ) := by
      have hbase : 2 / r < Mone := hMone
      have := hbase.trans_le hMR
      rw [div_lt_iff₀ hr0] at hbase
      nlinarith
    have hfloor : r * (M : ℝ) - 1 < (⌊r * (M : ℝ)⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor _
    have hfloorR : (1 : ℝ) < (⌊r * (M : ℝ)⌋₊ : ℝ) := by
      linarith
    have hfloorNat : 1 < ⌊r * (M : ℝ)⌋₊ := by exact_mod_cast hfloorR
    unfold targetScale
    exact Nat.one_lt_pow (by omega) (by omega)
  · intro M hM
    have hMpos : 0 < M := lt_of_lt_of_le (by omega) (hM0one.trans hM)
    have hx0 : 0 ≤ r * (M : ℝ) := by positivity
    have hfloorLe : (⌊r * (M : ℝ)⌋₊ : ℝ) ≤ r * M := Nat.floor_le hx0
    have hlt : (⌊r * (M : ℝ)⌋₊ : ℝ) < M := by
      have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
      nlinarith
    have hfloorNat : ⌊r * (M : ℝ)⌋₊ < M := by exact_mod_cast hlt
    unfold targetScale
    exact Nat.pow_lt_pow_right (by norm_num) hfloorNat
  · intro M hM
    have hreal := hMhor M (hM0hor.trans hM)
    have hcast :
        (((M : ℚ) / (2 * (targetScale r M : ℚ)) : ℚ) : ℝ) ≤
          (((1 / 3 : ℚ) : ℚ) : ℝ) := by
      norm_num
      exact hreal
    exact Rat.cast_le.1 hcast
  · intro M hM
    have hMlinLe : Mlin ≤ M := hM0lin.trans hM
    have hMR : (Mlin : ℝ) ≤ M := by exact_mod_cast hMlinLe
    have hbase : (2 + eta) / g < Mlin := hMlin
    have hgapM : 2 + eta < g * (M : ℝ) := by
      have h := hbase.trans_le hMR
      rw [div_lt_iff₀ hg] at hbase
      nlinarith
    have hfloor : r * (M : ℝ) - 1 < (⌊r * (M : ℝ)⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor _
    have hExp :
        (a0 + eta) * M + 1 + eta ≤ (⌊r * (M : ℝ)⌋₊ : ℝ) := by
      dsimp [g] at hgapM
      linarith
    rw [central_terminal_identity eta M]
    unfold targetScale
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
end FirstPassageLinearTransport
