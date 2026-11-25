-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.zero_count_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:57.849178+00:00
-- url     : https://prove2.me/submissions/a760cc37-e37f-4fbb-86b4-ed00528ab021

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ZeroDetectionSecond
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_SecondBlockCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_second_block_count
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_dyadic_index_le_log_second
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_dyadic_size_le_pow_twelve_second
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_log_pow_five_le_sqrt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_one_le_log_of_three_le_second
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_zero_detection_second


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
theorem _root_.solution : Count1 := by
  obtain ⟨q₁, hq₁⟩ := log_pow_five_le_sqrt 971882496
  refine ⟨48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)), max q₁ 256, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq256 : 256 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_max_left _ _) hq)
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le_second (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let Sj : ℕ → Finset (DirichletCharacter ℂ M × ℂ) := fun j =>
    S.filter (fun p => 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => p.1 (n : ZMod M)) p.2‖)
  have hsub : S ⊆ (range (pJd M T)).biUnion Sj := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    obtain ⟨j, hj, hjb⟩ := zero_detection_second M p.1 h1 T hT hM p.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ B := by
    intro j hj
    have hjJ : j < pJd M T := mem_range.1 hj
    have hYN : qd M T ^ 3 * 2 ^ pJd M T ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve_second (qd M T) hq256
    apply second_block_count M T σ (Sj j) (pYd M T * 2 ^ j) hM hT hσ hσ1 hq256 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ j) = qd M T ^ 3 * 2 ^ (j + 1) := by unfold pYd; ring
        _ ≤ qd M T ^ 3 * 2 ^ pJd M T := by
            gcongr
            · norm_num
            · omega
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨-, h2, h3, h4, -⟩ := hS p (mem_filter.1 hp).1
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp'
      exact hsp p (mem_filter.1 hp).1 p' (mem_filter.1 hp').1
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ (pJd M T : ℝ) * B := by
    have := sum_le_card_nsmul (range (pJd M T)) (fun j => ((Sj j).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log (qd M T) := dyadic_index_le_log_second (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (256 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq256
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : (pJd M T : ℝ) * B ≤ 48 * Real.log ((M : ℝ) * T) * B := by gcongr
  have h4 : 48 * Real.log ((M : ℝ) * T) * B =
      48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 7 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 7 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
