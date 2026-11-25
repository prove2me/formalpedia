-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.first_small_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:15:35.21562+00:00
-- url     : https://prove2.me/submissions/540df9f6-50ba-41c1-bdfc-be3f6f60d6c5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (u l K J q s Lq c : ℝ) (hq : 0 < q) (hs : 0 < s) (hc0 : 0 < c)
    (hu : u ≤ 1 / (q * s)) (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 16 * q)
    (hJ0 : 0 < J) (hJ : J ≤ 25 * Lq) (hc : 87880000 / c ^ 2 * Lq ^ 7 ≤ s) :
    2 * u * l ^ 3 * K ≤ (c / (J * Lq)) ^ 2 / 2 := by
  have hL : 0 < Lq := by linarith
  have hlK : 0 ≤ l ^ 3 * K := by positivity
  have step1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by
    have := mul_le_mul_of_nonneg_right hu hlK
    nlinarith
  have step2 : 2 * (1 / (q * s)) * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) := by
    gcongr
  have step3 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) = 70304 * Lq ^ 3 / s := by
    field_simp
    ring
  have hJL : (c / (25 * Lq * Lq)) ^ 2 / 2 ≤ (c / (J * Lq)) ^ 2 / 2 := by
    gcongr
  have hc' : 87880000 * Lq ^ 7 ≤ s * c ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hc
    exact hc
  have step4 : 70304 * Lq ^ 3 / s ≤ (c / (25 * Lq * Lq)) ^ 2 / 2 := by
    have e : (c / (25 * Lq * Lq)) ^ 2 / 2 = c ^ 2 / (1250 * Lq ^ 4) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
