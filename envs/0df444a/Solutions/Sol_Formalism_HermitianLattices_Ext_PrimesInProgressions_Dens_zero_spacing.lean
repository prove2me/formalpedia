-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.zero_spacing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:44.011549+00:00
-- url     : https://prove2.me/submissions/73261f95-4d3f-4280-b245-ae668b34b7a9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_floor_eq_close
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_space_side

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
theorem _root_.solution : Spacing := by
  intro P T hT hP hsp
  constructor
  · have hinj : Set.InjOn (fun x => ⌊x + T⌋₊) P := by
      intro x hx y hy hxy
      by_contra hne
      have hx' := abs_le.1 (hP x hx)
      have hy' := abs_le.1 (hP y hy)
      have := floor_eq_close (by linarith) (by linarith) hxy
      have := hsp x hx y hy hne
      rw [show x + T - (y + T) = x - y by ring] at *
      linarith
    have hsub : P.image (fun x => ⌊x + T⌋₊) ⊆ range (⌊2 * T⌋₊ + 1) := by
      intro k hk
      rw [mem_image] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      rw [mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (by linarith [(abs_le.1 (hP x hx)).2])
    have h1 : P.card ≤ ⌊2 * T⌋₊ + 1 := by
      rw [← card_image_of_injOn hinj]
      exact (card_le_card hsub).trans (by simp)
    have h2 : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T + 1 := by
      push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)]
    exact (by exact_mod_cast h1 : (P.card : ℝ) ≤ ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ)).trans h2
  · intro t ht
    have hsplit := sum_filter_add_sum_filter_not (P.erase t) (fun x => t < x) (fun x => 1 / |t - x|)
    rw [← hsplit]
    have hR : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / (x - t) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter] at hx
        rw [abs_sub_comm, abs_of_pos (by linarith [hx.2])]
      rw [e]
      refine space_side _ (fun x => x - t) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_pos (by linarith [hx.2])] at this
        exact this
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show x - t ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show x - t - (y - t) = x - y by ring]
    have hL : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / (t - x) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        rw [abs_of_pos (by linarith)]
      rw [e]
      refine space_side _ (fun x => t - x) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_neg (by linarith)] at this
        show 1 ≤ t - x
        linarith
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show t - x ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show t - x - (t - y) = -(x - y) by ring, abs_neg]
    linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
