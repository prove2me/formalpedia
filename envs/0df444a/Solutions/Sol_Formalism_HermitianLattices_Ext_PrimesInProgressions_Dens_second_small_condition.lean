-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.second_small_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:52:48.325315+00:00
-- url     : https://prove2.me/submissions/78917736-b5bd-4b87-81e6-95194ae426d9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond

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
theorem _root_.solution (u l K J q s Lq : ℝ) (hq : 0 < q) (hs : 0 < s) (hu : u ≤ 1 / (q * s))
    (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 48 * q) (hJ0 : 0 < J) (hJ : J ≤ 24 * Lq)
    (hc : 971882496 * Lq ^ 5 ≤ s) : 2 * u * l ^ 3 * K ≤ (1 / (2 * J)) ^ 2 / 2 := by
  have hL : 0 < Lq := by nlinarith
  have h1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by
    have : 0 ≤ 1 / (q * s) := by positivity
    calc 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by gcongr
      _ ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by gcongr
  have h2 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) = 210912 * Lq ^ 3 / s := by
    field_simp; ring
  have h3 : 1 / (4608 * Lq ^ 2) ≤ (1 / (2 * J)) ^ 2 / 2 := by
    have : (1 / (2 * J)) ^ 2 / 2 = 1 / (8 * J ^ 2) := by field_simp; ring
    rw [this]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h4 : 210912 * Lq ^ 3 / s ≤ 1 / (4608 * Lq ^ 2) := by
    rw [div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
