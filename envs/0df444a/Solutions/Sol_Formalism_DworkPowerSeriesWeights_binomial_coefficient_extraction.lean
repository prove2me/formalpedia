-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.binomial_coefficient_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:02.261807+00:00
-- url     : https://prove2.me/submissions/45847795-5175-4966-851d-e7090319a82a

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_norm_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_norm_ge
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_choose_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_torus_cong
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_sideE
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_sideO
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_div
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_side_cases
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_degE_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_degO_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_exE
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_exO
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
section Blocks
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
end Blocks
section Subst
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
end Subst
section De
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
end De
section NormNat
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end NormNat
section Sides
variable {K : Type u} [NormedField K] {d : ℕ} [NeZero d]
end Sides
private theorem monoWtGe_or_biPower_of_wtGe_de1_de2 {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {l d : ℕ} [NeZero d] (hl : l.Prime) (hl3 : 3 ≤ l) (hd2 : 2 ≤ d) (hde : Even d)
    (hl1 : ‖(l : K)‖ < 1) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) K) (htor : subst (torus l ζ) be = be) (hlow : NoLowBidegree be)
    (r w : ℝ) (h1 : WtGe ‖(l : K)‖ (fun _ => r) w (de1 be))
    (h2 : WtGe ‖(l : K)‖ (fun _ => r) w (de2 be))
    (n : ZMod d →₀ ℕ) (hn : coeff n be ≠ 0) :
    MonoWtGe ‖(l : K)‖ (fun _ => r) w n (coeff n be) ∨
      (IsBiPower l n ∧ MonoWtGe ‖(l : K)‖ (fun _ => r) (w - 1) n (coeff n be)) := by
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  obtain ⟨hE, hO, hEO⟩ := hlow n hn
  have hc0 := norm_nonneg (coeff n be)
  unfold MonoWtGe
  rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 = 0) n (bnx_exE n hE) with
    ⟨s, j, hs, hj, hpos, hnd⟩ | ⟨s, α, hs, hu, hα⟩
  · left
    have hb := bnx_sideE be _ _ _ h1 n s hs j hj hpos
    have hC := bnx_norm_one hl hl1 _ hnd
    nlinarith
  rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 ≠ 0) n (bnx_exO n hO) with
    ⟨s', j, hs', hj, hpos, hnd⟩ | ⟨s', β, hs', hu', hβ⟩
  · left
    have hb := bnx_sideO be _ _ _ h2 n s' hs' j hj hpos
    have hC := bnx_norm_one hl hl1 _ hnd
    nlinarith
  have hss : s ≠ s' := by
    rintro rfl
    exact hs' hs
  have hneq : n = Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) := by
    ext t
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    by_cases ht : t.val % 2 = 0
    · by_cases hts : t = s
      · subst hts
        simp [hss, Ne.symm hss, hα]
      · have h0 := hu t ht hts
        have hts' : t ≠ s' := by
          rintro rfl
          exact hs' ht
        simp [Ne.symm hts, Ne.symm hts', h0]
    · by_cases hts : t = s'
      · subst hts
        simp [hss, Ne.symm hss, hβ]
      · have h0 := hu' t ht hts
        have hts2 : t ≠ s := by
          rintro rfl
          exact ht hs
        simp [Ne.symm hts, Ne.symm hts2, h0]
  have hαβ : α ≠ 0 ∨ β ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨rfl, rfl⟩ := hc
    apply hEO
    rw [bnx_degE_eq n s hs hu, bnx_degO_eq n s' hs' hu', hα, hβ]
    simp
  have hc' : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0 := by
    rw [← hneq]
    exact hn
  have hcong := bnx_torus_cong l d hl hl3 hd2 hde ζ hζ be htor s s' hs hs' α β hc'
  have hbi : IsBiPower l n := by
    unfold IsBiPower
    exact ⟨s, s', α, β, hs, Nat.mod_two_ne_zero.1 hs', hαβ, hcong, hneq⟩
  right
  refine ⟨hbi, ?_⟩
  rcases hαβ with hα0 | hβ0
  · obtain ⟨hj0, hjlt, hCne, hC2⟩ := bnx_choose_pow hl α (Nat.one_le_iff_ne_zero.2 hα0)
    have hb := bnx_sideE be _ _ _ h1 n s hs (l ^ (α - 1)) (by rw [hα]; exact hjlt) (Or.inl hj0)
    rw [hα] at hb
    have hC := bnx_norm_ge hl hl1 _ hCne hC2
    have hb' := le_trans (mul_le_mul_of_nonneg_left hC hc0) hb
    have h3 := bnx_div (v := 1) hpi0 (le_of_eq (Real.rpow_one _)) hc0 hb'
    rw [← Real.rpow_sub hpi0] at h3
    convert h3 using 2
    ring
  · obtain ⟨hj0, hjlt, hCne, hC2⟩ := bnx_choose_pow hl β (Nat.one_le_iff_ne_zero.2 hβ0)
    have hb := bnx_sideO be _ _ _ h2 n s' hs' (l ^ (β - 1)) (by rw [hβ]; exact hjlt) (Or.inl hj0)
    rw [hβ] at hb
    have hC := bnx_norm_ge hl hl1 _ hCne hC2
    have hb' := le_trans (mul_le_mul_of_nonneg_left hC hc0) hb
    have h3 := bnx_div (v := 1) hpi0 (le_of_eq (Real.rpow_one _)) hc0 hb'
    rw [← Real.rpow_sub hpi0] at h3
    convert h3 using 2
    ring
end Formalism.DworkPowerSeriesWeights
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : BinomExtract.{u} := by
  unfold BinomExtract
  intro K _ _ _ l d _ hl hlo hd2 hde hl1 ζ hζ be htor hlow h1 h2
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    obtain ⟨m, hm⟩ := hlo
    omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have key := fun n hn => monoWtGe_or_biPower_of_wtGe_de1_de2 hl hl3 hd2 hde hl1 ζ hζ be htor hlow _ _ h1 h2 n hn
  constructor
  · unfold WtGe
    intro n
    by_cases hn : coeff n be = 0
    · unfold MonoWtGe
      rw [hn, norm_zero]
      positivity
    · rcases key n hn with h | ⟨_, h⟩
      · unfold MonoWtGe at h ⊢
        refine h.trans ?_
        first
        | exact Real.rpow_le_rpow_of_exponent_ge hpi0 hl1.le (by linarith)
        | exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hpi0 hl1).2 (by linarith)
      · exact h
  · intro n hnb
    by_cases hn : coeff n be = 0
    · unfold MonoWtGe
      rw [hn, norm_zero]
      positivity
    · rcases key n hn with h | ⟨hb, _⟩
      · exact h
      · exact absurd hb hnb
end Formalism.DworkPowerSeriesWeights
