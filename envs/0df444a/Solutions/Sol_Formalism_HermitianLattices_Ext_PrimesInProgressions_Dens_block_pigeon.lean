-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.block_pigeon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:48.48792+00:00
-- url     : https://prove2.me/submissions/7cc1ad9a-200e-42c2-978f-c08d6b0608ad

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDetect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneSubTwoCpowLower
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_sum_blocks


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (Y J' N' : ℕ) (f : ℕ → ℂ) (ρ : ℂ) (hN : N' = 2 ^ J') (hJ : 0 < J') (θ : ℝ)
    (h : θ ≤ ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖) :
    ∃ j ∈ range J', θ / (J' : ℝ) ≤ ‖blkD Y N' (Y * 2 ^ j) f ρ‖ := by
  by_contra hcon
  push Not at hcon
  have hsplit : ∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ) =
      ∑ j ∈ range J', blkD Y N' (Y * 2 ^ j) f ρ := by
    have h0 := sum_blocks (fun n => mco Y N' n * f n * (n : ℂ) ^ (-ρ)) Y J'
    rw [← hN] at h0
    exact h0
  have hJpos : (0 : ℝ) < J' := by exact_mod_cast hJ
  have hlt : ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖ < θ := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    calc ∑ j ∈ range J', ‖blkD Y N' (Y * 2 ^ j) f ρ‖
        < ∑ j ∈ range J', θ / (J' : ℝ) := sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hJ.ne') hcon
      _ = θ := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
