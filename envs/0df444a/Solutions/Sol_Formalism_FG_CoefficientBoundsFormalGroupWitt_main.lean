-- Prove2me | solution 1 for Formalism.FG.CoefficientBoundsFormalGroupWitt.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:03.432452+00:00
-- url     : https://prove2.me/submissions/cae505e7-db55-408f-aa02-dcc2a731a953

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_sigma_norm_le_one
import Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_coeff_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CoefficientBoundsFormalGroupWitt
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.CoefficientBoundsFormalGroupWitt
theorem _root_.solution : Formalism.FG.CoeffBoundV.{u, v, w} := by
  unfold Formalism.FG.CoeffBoundV
  intro K _ _ _ p q hq σ hS ι _ M hM τ f h0 hF
  unfold FunctionalEquationSetting at hS
  unfold IntegralMat at hM
  unfold IsFunEqTypeV at hF
  obtain ⟨hpp, ⟨h, hh, hqe⟩, hp1, hσ⟩ := hS
  have hq1 : 1 < q := by
    rw [hqe]
    exact Nat.one_lt_pow hh.ne' hpp.one_lt
  have hP0 : 0 < ‖(p : K)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hpp.ne_zero
  have hg : ∀ j n, ‖MvPowerSeries.coeff n (f j - (p : K)⁻¹ •
      ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k)))‖ ≤ 1 := by
    intro j n
    have h3 := hF j
    unfold IntegralMv at h3
    exact h3 n
  have hσn : ∀ (x : K) (e : ℕ), ‖x‖ * ‖(p : K)‖ ^ e ≤ 1 → ‖σ x‖ * ‖(p : K)‖ ^ e ≤ 1 := by
    intro x e hx
    have h4 : ‖(p : K) ^ e * x‖ ≤ 1 := by
      rw [norm_mul, norm_pow, mul_comm]
      exact hx
    have h5 := sigma_norm_le_one hp1.le hσ _ h4
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, mul_comm] at h5
    exact h5
  have key : ∀ d : ℕ, ∀ n : τ →₀ ℕ, Finsupp.degree n = d → ∀ j, ∃ k, (∀ i, q ^ k ∣ n i) ∧
      ‖MvPowerSeries.coeff n (f j)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro n hn j
    have hc := coeff_split p q hq σ M f j n
    by_cases hdiv : ∀ i, q ∣ n i
    · by_cases hn0 : n = 0
      · refine ⟨0, fun i => by simp, ?_⟩
        subst hn0
        have h6 := h0 j
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h6
        rw [h6]
        simp
      · obtain ⟨m, hm⟩ : ∃ m : τ →₀ ℕ, n = q • m :=
          ⟨Finsupp.mapRange (fun e => e / q) (Nat.zero_div q) n, by
            ext i
            simp [Nat.mul_div_cancel' (hdiv i)]⟩
        have hm0 : m ≠ 0 := by
          rintro rfl
          apply hn0
          rw [hm, smul_zero]
        have hlt : Finsupp.degree m < d := by
          rw [← hn, hm, map_nsmul, smul_eq_mul]
          have h7 : Finsupp.degree m ≠ 0 := fun h8 => hm0 ((Finsupp.degree_eq_zero_iff m).mp h8)
          have h9 : 0 < Finsupp.degree m := Nat.pos_of_ne_zero h7
          nlinarith
        choose kk hkk using fun l => ih _ hlt m rfl l
        obtain ⟨l0, -, hl0⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨j, Finset.mem_univ _⟩ kk
        set K0 := Finset.univ.sup kk with hK0
        have hK : ∀ i, q ^ K0 ∣ m i := by
          rw [hl0]
          exact (hkk l0).1
        have hb : ∀ l, ‖MvPowerSeries.coeff m (f l)‖ * ‖(p : K)‖ ^ K0 ≤ 1 := by
          intro l
          have h10 : ‖(p : K)‖ ^ K0 ≤ ‖(p : K)‖ ^ kk l :=
            pow_le_pow_of_le_one hP0.le hp1.le (Finset.le_sup (Finset.mem_univ l))
          exact (mul_le_mul_of_nonneg_left h10 (norm_nonneg _)).trans (hkk l).2
        have hterm : ∀ l, MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l))) =
            σ (MvPowerSeries.coeff m (f l)) := by
          intro l
          rw [hm, MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map]
        have hPK : 0 < ‖(p : K)‖ ^ K0 := pow_pos hP0 K0
        have hS : ‖∑ l, M j l * MvPowerSeries.coeff n
            (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l)))‖ ≤ 1 / ‖(p : K)‖ ^ K0 := by
          apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
          intro l _
          rw [hterm, norm_mul, le_div_iff₀ hPK]
          have h11 := hσn _ _ (hb l)
          calc ‖M j l‖ * ‖σ (MvPowerSeries.coeff m (f l))‖ * ‖(p : K)‖ ^ K0
              ≤ 1 * ‖σ (MvPowerSeries.coeff m (f l))‖ * ‖(p : K)‖ ^ K0 := by gcongr; exact hM j l
            _ ≤ 1 := by rw [one_mul]; exact h11
        refine ⟨K0 + 1, fun i => ?_, ?_⟩
        · rw [hm, Finsupp.smul_apply, smul_eq_mul, pow_succ, mul_comm (q ^ K0)]
          exact mul_dvd_mul_left q (hK i)
        · rw [hc]
          refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
            (by positivity)).trans ?_
          rw [max_mul_of_nonneg _ _ (by positivity)]
          apply max_le
          · calc _ ≤ 1 * 1 := mul_le_mul (hg j n) (pow_le_one₀ hP0.le hp1.le) (by positivity) zero_le_one
              _ = 1 := one_mul 1
          · rw [norm_mul, norm_inv, pow_succ]
            have h12 := (le_div_iff₀ hPK).mp hS
            calc ‖(p : K)‖⁻¹ * ‖∑ l, M j l * MvPowerSeries.coeff n
                  (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l)))‖ * (‖(p : K)‖ ^ K0 * ‖(p : K)‖)
                = ‖∑ l, M j l * MvPowerSeries.coeff n
                  (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l)))‖ * ‖(p : K)‖ ^ K0 := by
                  field_simp
              _ ≤ 1 := h12
    · push_neg at hdiv
      obtain ⟨i, hi⟩ := hdiv
      refine ⟨0, fun i => by simp, ?_⟩
      have hz : ∀ l, MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f l))) = 0 :=
        fun l => MvPowerSeries.coeff_expand_of_not_dvd q hq _ hi
      rw [hc]
      simp only [hz, mul_zero, Finset.sum_const_zero, add_zero, pow_zero, mul_one]
      exact hg j n
  intro j n
  exact key _ n rfl j
end Formalism.FG.CoefficientBoundsFormalGroupWitt
