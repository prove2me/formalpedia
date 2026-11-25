-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.thickTerm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:15.609347+00:00
-- url     : https://prove2.me/submissions/6ea0c740-7aec-4e84-a18a-6fc14784daac

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_mul_lstar_le_b
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJ_eq_div
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJDenom_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_kmax_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_le_prime_cast
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_prime_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_choose_two_le_sq_div_two
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_h_bounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
private theorem size_bounds_of_large {P : Par} (H : P.Hyp) (G : P.Large) :
    P.S + P.η < P.lstar ∧ 2 * P.η + P.t + 8 * (P.b / P.lstar) + 7 < P.lstar ∧
      2 * P.lstar ≤ P.b ∧ 0 < P.b / P.lstar ∧ (P.kmax : ℝ) ≤ 2 * (P.b / P.lstar) ∧
      P.h = P.b + P.S + P.η + P.t + 1 ∧ 0 ≤ P.η ∧ (P.t : ℝ) ≤ P.η ∧ 0 ≤ P.S ∧ 0 < P.lstar := by
  have h1 := H.sum_lt
  have h2 := H.win_lt
  have hb' := H.b'_pos
  have hbl := b_div_lstar_pos H G
  have e : 8 * P.b / P.lstar = 8 * (P.b / P.lstar) := by ring
  exact ⟨by linarith, by linarith, two_mul_lstar_le_b H G, hbl, kmax_le H G, rfl, eta_nonneg' H,
    H.t_le, H.S_nonneg, lstar_pos H G⟩
private theorem log_h_pos_and_le {P : Par} (H : P.Hyp) (G : P.Large) :
    0 < Real.log P.h ∧ Real.log P.h ≤ P.L + 7 / 10 := by
  obtain ⟨h1, h2⟩ := log_h_bounds H G
  have d : (0.7 : ℝ) = 7 / 10 := by norm_num
  rw [d] at h2
  exact ⟨h1, h2⟩
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : TermC := by
  intro P H G ι D hA τ hτ l hl hlJ
  have nb := natBounds H
  have hb := b_pos' P
  have hL := G.L_ge
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := size_bounds_of_large H G
  obtain ⟨h1, h2, h3⟩ := hA τ hτ l hl
  have hl2 := two_le_prime_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hJpos := lJDenom_pos H G
  have hJeq : P.lJ * indexDenominator P = P.m * P.b * P.L := by
    rw [lJ_eq_div]
    field_simp
  have hlog0 := log_prime_nonneg hl
  have hex0 : (0 : ℝ) ≤ D.ex τ l := Nat.cast_nonneg _
  rw [le_div_iff₀ hl0]
  by_cases hbig : 2 * P.η + P.t ≤ l
  · have h3' := h3 hbig
    have hk1 := nb.k1
    have hSk : 1 ≤ P.S + P.k := by linarith
    have hSk3 : P.S + P.k ≤ 3 * P.h := by rw [a6]; linarith [nb.kt, nb.m1, hb]
    have hlg : Real.log (P.S + P.k) ≤ Real.log (3 * P.h) := Real.log_le_log (by linarith) hSk3
    have hlg0 : 0 ≤ Real.log (P.S + P.k) := Real.log_nonneg hSk
    have hkk : (P.k : ℝ) ^ 2 ≤ P.k * (P.m + P.t) := by
      nlinarith [nb.kt, nb.m1]
    have e1 : (P.k : ℝ) ^ 2 * Real.log (P.S + P.k) ≤ P.k * (P.m + P.t) * Real.log (3 * P.h) :=
      mul_le_mul hkk hlg hlg0 (by positivity)
    have e2 : (D.ex τ l : ℝ) * Real.log l ≤ 2 * indexDenominator P := by
      unfold indexDenominator
      linarith
    have e3 : indexDenominator P * l ≤ indexDenominator P * P.lJ := mul_le_mul_of_nonneg_left hlJ hJpos.le
    have e4 := mul_le_mul_of_nonneg_right e2 hl0.le
    linarith
  · push_neg at hbig
    have hl3 : (l : ℝ) < 3 * P.η := by linarith
    obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
    have hC := choose_two_le_sq_div_two P.Nr
    have hNr2 : (P.Nr : ℝ) ^ 2 ≤ 4 * (P.t : ℝ) ^ 2 := by
      have := nb.nr2
      have h0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
      nlinarith
    have e1 : (D.ex τ l : ℝ) * Real.log l ≤ ((P.Nr : ℝ) ^ 2 / 2) * (2 * P.L) :=
      h2.trans (mul_le_mul hC (by linarith) c1.le (by positivity))
    have e1' : (D.ex τ l : ℝ) * Real.log l ≤ 4 * (P.t : ℝ) ^ 2 * P.L := by
      have := mul_le_mul_of_nonneg_right hNr2 (by linarith : (0 : ℝ) ≤ P.L)
      linarith
    have hpos : 0 < (P.t : ℝ) ^ 3 * P.f * (P.k : ℝ) ^ 3 :=
      mul_pos (mul_pos (pow_pos (by linarith [nb.t6]) 3) (by linarith [nb.f1]))
        (pow_pos (by linarith [nb.k1]) 3)
    have hηb : P.η * ((P.t : ℝ) ^ 3 * P.f * (P.k : ℝ) ^ 3) ≤ P.b := (le_div_iff₀ hpos).1 H.η_le
    have hk2 := mul_le_mul nb.k1 nb.k1 zero_le_one (by linarith [nb.k1])
    have hk3' := mul_le_mul hk2 nb.k1 zero_le_one (by nlinarith [nb.k1])
    have hk3 : (1 : ℝ) ≤ (P.k : ℝ) ^ 3 := by
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (P.k : ℝ) * P.k * P.k := hk3'
        _ = (P.k : ℝ) ^ 3 := by ring
    have hmf1 := mul_le_mul nb.m1 nb.f1 zero_le_one (by linarith [nb.m1])
    have hmf : (1 : ℝ) ≤ P.m * P.f := by linarith
    have hmft1 := mul_le_mul hmf nb.t6 (by norm_num) (by linarith)
    have hmft : (6 : ℝ) ≤ P.m * P.f * P.t := by linarith
    have q6 := mul_le_mul hmft hk3 (by norm_num) (by linarith)
    have t2L : 0 ≤ 4 * (P.t : ℝ) ^ 2 * P.L := mul_nonneg (by positivity) (by linarith)
    have sa := mul_le_mul_of_nonneg_right e1' hl0.le
    have sb := mul_le_mul_of_nonneg_left hl3.le t2L
    have sc := mul_le_mul_of_nonneg_left q6
      (mul_nonneg (mul_nonneg (by positivity) (by linarith)) a7 : (0 : ℝ) ≤ 2 * (P.t : ℝ) ^ 2 * P.L * P.η)
    have sd := mul_le_mul_of_nonneg_left hηb (mul_nonneg (by positivity) (by linarith) : (0 : ℝ) ≤ 2 * (P.m : ℝ) * P.L)
    linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
