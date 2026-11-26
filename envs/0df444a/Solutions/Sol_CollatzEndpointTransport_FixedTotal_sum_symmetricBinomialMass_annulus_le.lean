-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_symmetricBinomialMass_annulus_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:04.393052+00:00
-- url     : https://prove2.me/submissions/bb88e323-2508-460e-8630-3a5cd169a3e4

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_symmetricBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_choose_lower_tail
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_choose_upper_tail
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialCenterDistance_le_half_add_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_subset_tails
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_tails_disjoint
import Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_hoeffding


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H j : ℕ} (hH : 0 < H) :
    (∑ k ∈ binomialAnnulus H j, symmetricBinomialMass H k) ≤
      2 * Real.exp (-2 * (j : ℝ) ^ 2) := by
  by_cases hj0 : j = 0
  · subst j
    have hsub : binomialAnnulus H 0 ⊆ Finset.range (H + 1) := by
      intro k hk
      exact (Finset.mem_filter.mp hk).1
    calc
      (∑ k ∈ binomialAnnulus H 0, symmetricBinomialMass H k) ≤
          ∑ k ∈ Finset.range (H + 1), symmetricBinomialMass H k := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => by unfold symmetricBinomialMass; positivity)
      _ = 1 := sum_symmetricBinomialMass H
      _ ≤ 2 * Real.exp (-2 * ((0 : ℕ) : ℝ) ^ 2) := by norm_num
  · have hj : 0 < j := Nat.pos_of_ne_zero hj0
    let W := binomialAnnulusWidth H
    let d := j * W
    let K := binomialAnnulusCutoff H j
    let t : ℝ := ((d : ℝ) - 2) / H
    by_cases hdBound : d ≤ H / 2 + 1
    · have hd2 : 2 ≤ d := by
        have hW : 3 ≤ W := by
          dsimp [W, binomialAnnulusWidth]
          omega
        have hWle : W ≤ d := by
          dsimp [d]
          simpa using Nat.mul_le_mul_right W (Nat.succ_le_iff.mpr hj)
        omega
      have hKH : K ≤ H := by
        dsimp [K, binomialAnnulusCutoff]
        omega
      have ht0 : 0 ≤ t := by
        dsimp [t]
        exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hd2))
          (Nat.cast_nonneg H)
      have hcut : (K : ℝ) ≤ (1 / 2 - t) * H := by
        have hcastK : (K : ℝ) = (H / 2 + 1 : ℕ) - d := by
          dsimp [K, binomialAnnulusCutoff]
          rw [Nat.cast_sub hdBound]
        rw [hcastK]
        push_cast
        dsimp [t]
        have hHR : (0 : ℝ) < H := by exact_mod_cast hH
        field_simp
        have hfloor : (2 : ℝ) * (H / 2 : ℕ) ≤ H := by
          exact_mod_cast (show 2 * (H / 2) ≤ H by
            simpa [mul_comm] using Nat.div_mul_le_self H 2)
        nlinarith
      have htail := CollatzEndpointTransport.Terras.lowerBinomialSum_le_hoeffding
        ht0 hcut
      have hsubset := binomialAnnulus_subset_tails (H := H) hj
      have hdisjoint := binomialAnnulus_tails_disjoint (H := H) hH hj
      have hchoose :
          (∑ k ∈ binomialAnnulus H j, (H.choose k : ℝ)) ≤
            2 * ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) := by
        calc
          (∑ k ∈ binomialAnnulus H j, (H.choose k : ℝ)) ≤
              ∑ k ∈
                  Finset.Ico 0 (K + 1) ∪ Finset.Ico (H - K) (H + 1),
                (H.choose k : ℝ) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by simpa [K] using hsubset)
              (fun k _ _ => Nat.cast_nonneg _)
          _ = 2 * CollatzEndpointTransport.Terras.lowerBinomialSum H K := by
            rw [Finset.sum_union (by simpa [K] using hdisjoint),
              sum_choose_lower_tail, sum_choose_upper_tail hKH]
            ring
          _ ≤ 2 * ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H)) := by
            gcongr
      have hsqrt : Real.sqrt (H : ℝ) < (Nat.sqrt H : ℝ) + 1 :=
        Real.real_sqrt_lt_nat_sqrt_succ
      have hdroot : (j : ℝ) * Real.sqrt H ≤ (d : ℝ) - 2 := by
        have hnat : j * (Nat.sqrt H + 1) ≤ d - 2 := by
          apply Nat.le_sub_of_add_le
          dsimp [d, W, binomialAnnulusWidth]
          calc
            j * (Nat.sqrt H + 1) + 2 ≤
                j * (Nat.sqrt H + 1) + 2 * j := by omega
            _ = j * (Nat.sqrt H + 3) := by ring
        have hcast : (j : ℝ) * (Nat.sqrt H + 1 : ℕ) ≤ (d : ℝ) - 2 := by
          exact_mod_cast hnat
        have hmul : (j : ℝ) * Real.sqrt H <
            (j : ℝ) * ((Nat.sqrt H : ℝ) + 1) :=
          mul_lt_mul_of_pos_left hsqrt
            (by exact_mod_cast hj : (0 : ℝ) < j)
        exact hmul.le.trans (by simpa using hcast)
      have hsqroot : (Real.sqrt (H : ℝ)) ^ 2 = H :=
        Real.sq_sqrt (by positivity)
      have hsq : (j : ℝ) ^ 2 * H ≤ ((d : ℝ) - 2) ^ 2 := by
        have hleft0 : 0 ≤ (j : ℝ) * Real.sqrt H := by positivity
        have hright0 : 0 ≤ (d : ℝ) - 2 :=
          sub_nonneg.mpr (by exact_mod_cast hd2)
        nlinarith [sq_nonneg ((d : ℝ) - 2 - (j : ℝ) * Real.sqrt H)]
      have htSquare : (j : ℝ) ^ 2 ≤ t ^ 2 * H := by
        have hHR : (0 : ℝ) < H := by exact_mod_cast hH
        dsimp [t]
        calc
          (j : ℝ) ^ 2 ≤ ((d : ℝ) - 2) ^ 2 / H :=
            (le_div_iff₀ hHR).2 hsq
          _ = (((d : ℝ) - 2) / H) ^ 2 * H := by
            field_simp
      have hexp : Real.exp (-2 * t ^ 2 * H) ≤
          Real.exp (-2 * (j : ℝ) ^ 2) := by
        exact Real.exp_le_exp.mpr (by nlinarith)
      unfold symmetricBinomialMass
      rw [← Finset.sum_div]
      calc
        (∑ k ∈ binomialAnnulus H j, (H.choose k : ℝ)) / (2 : ℝ) ^ H ≤
            (2 * ((2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H))) /
              (2 : ℝ) ^ H := by
          exact div_le_div_of_nonneg_right hchoose (by positivity)
        _ = 2 * Real.exp (-2 * t ^ 2 * H) := by field_simp
        _ ≤ 2 * Real.exp (-2 * (j : ℝ) ^ 2) := by gcongr
    · have hempty : binomialAnnulus H j = ∅ := by
        unfold binomialAnnulus
        apply Finset.filter_false_of_mem
        intro k hk
        rintro ⟨hmin, _⟩
        have hkH : k ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hmax := binomialCenterDistance_le_half_add_one hkH
        exact hdBound (hmin.trans hmax)
      rw [hempty]
      simp
      positivity
end CollatzEndpointTransport.FixedTotal
