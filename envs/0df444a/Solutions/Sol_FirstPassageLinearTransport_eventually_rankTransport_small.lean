-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_rankTransport_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:11.820241+00:00
-- url     : https://prove2.me/submissions/63c962c6-622f-453d-96f5-e55b0f37472e

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_one_div_two_pow_eq_exp
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℚ} (hr : 0 < r) :
    ∀ᶠ q : ℕ in atTop,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3 := by
  let rR : ℝ := (r : ℝ)
  have hrR : 0 < rR := by
    dsimp [rR]
    exact_mod_cast hr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htReal :
      Tendsto
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(Real.log 2) * x))
        atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log 2) hlog2
  have htNat :
      Tendsto
        (fun q : ℕ => (q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ)))
        atTop (nhds 0) := by
    simpa [Real.rpow_one, Function.comp_def] using
      htReal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ q : ℕ in atTop,
      (q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ)) < rR / 9 :=
    htNat.eventually (Iio_mem_nhds (div_pos hrR (by norm_num)))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with q hq hq1
  have hqBound : ((q + 2 : ℕ) : ℝ) ≤ 3 * (q : ℝ) := by
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    push_cast
    nlinarith
  have hreal :
      (((q + 2 : ℕ) : ℝ) / rR) / (2 : ℝ) ^ q ≤ 1 / 3 := by
    rw [show (((q + 2 : ℕ) : ℝ) / rR) / (2 : ℝ) ^ q =
        (((q + 2 : ℕ) : ℝ) / rR) * (1 / (2 : ℝ) ^ q) by ring,
      one_div_two_pow_eq_exp]
    have hscale :
        (((q + 2 : ℕ) : ℝ) / rR) *
            Real.exp (-(Real.log 2 * (q : ℝ))) ≤
          (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) := by
      have hexp0 : 0 ≤ Real.exp (-(Real.log 2 * (q : ℝ))) :=
        (Real.exp_pos _).le
      calc
        (((q + 2 : ℕ) : ℝ) / rR) *
            Real.exp (-(Real.log 2 * (q : ℝ))) ≤
          ((3 * (q : ℝ)) / rR) *
            Real.exp (-(Real.log 2 * (q : ℝ))) :=
              mul_le_mul_of_nonneg_right
                ((div_le_div_iff_of_pos_right hrR).2 hqBound) hexp0
        _ = (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) := by
              ring
    have hfinal :
        (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) < 1 / 3 := by
      calc
        (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) <
          (3 / rR) * (rR / 9) :=
            mul_lt_mul_of_pos_left hq (div_pos (by norm_num) hrR)
        _ = 1 / 3 := by
          field_simp [ne_of_gt hrR]
          norm_num
    exact hscale.trans hfinal.le
  have hcast :
      ((((((q + 2 : ℕ) : ℚ) / r) /
          ((2 ^ q : ℕ) : ℚ) : ℚ) : ℝ)) ≤
        (((1 / 3 : ℚ) : ℝ)) := by
    norm_num at hreal ⊢
    exact hreal
  exact Rat.cast_le.1 hcast
end FirstPassageLinearTransport
