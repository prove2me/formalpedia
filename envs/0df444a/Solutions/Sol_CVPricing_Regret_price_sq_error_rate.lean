-- Prove2me | solution 1 for CVPricing.Regret.price_sq_error_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T21:48:47.837591+00:00
-- url     : https://prove2.me/submissions/348bbbbc-4249-4c19-ac8f-96a9069e9d37

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP
import Definitions.Def_CVPricing_Regret_Process
import Theorems.Thm_CVPricing_Regret_mqle_consistency_rate
import Theorems.Thm_CVPricing_Regret_price_near_optimum_taboo
import Theorems.Thm_CVPricing_Regret_optPrice_lipschitz

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace Red220

open CVPricing.Regret

theorem prices_mem (M : CVPricing.Regret.Model) (α c : ℝ) (p d : ℕ → ℝ) (h : IsCVPPath M α c p d) :
    ∀ t : ℕ, 1 ≤ t → p t ∈ Set.Icc M.pl M.ph := by
  obtain ⟨h1, h2, -, -, -, -, hstep⟩ := h
  intro t ht
  induction t with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact h1
      · exact h2
    · rcases hstep n hn with ⟨-, hF⟩ | ⟨a, -, -, hF⟩ | ⟨a, -, -, hE⟩
      · rcases hF.1 with e | e <;> rw [e] <;> assumption
      · rcases hF.1 with e | e <;> rw [e] <;> assumption
      · rcases hE with ⟨-, hm, -⟩ | ⟨-, hm⟩
        · exact hm.1
        · exact hm.1.1

theorem pOpt_mem (M : CVPricing.Regret.Model) : pOpt M ∈ Set.Ioo M.pl M.ph := by
  obtain ⟨U, _, ha0, hall⟩ := M.nbhd
  obtain ⟨q0, hq0, hstrict, _⟩ := hall M.a0 ha0
  have hmax : ∀ q ∈ Set.Icc M.pl M.ph, revenue M.h M.a0 q ≤ revenue M.h M.a0 q0 := by
    intro q hq
    by_cases h : q = q0
    · rw [h]
    · exact (hstrict q hq h).le
  have hex : ∃ q, ∀ q', IsRevMaxOn M M.a0 (Set.Icc M.pl M.ph) q' ↔ q' = q := by
    refine ⟨q0, fun q' => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra hne
      have := hstrict q' h.1 hne
      have := h.2 q0 (Set.Ioo_subset_Icc_self hq0)
      linarith
    · subst h
      exact ⟨Set.Ioo_subset_Icc_self hq0, hmax⟩
  have hp : pOpt M = q0 := by
    unfold pOpt optPriceOf
    rw [dif_pos hex]
    have hq0max : IsRevMaxOn M M.a0 (Set.Icc M.pl M.ph) q0 :=
      ⟨Set.Ioo_subset_Icc_self hq0, hmax⟩
    exact ((Classical.choose_spec hex q0).1 hq0max).symm
  rw [hp]
  exact hq0

/-- upper Bernoulli-type bound for the increment of a concave power -/
theorem rpow_diff_le (β x : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 0 < x) :
    (x + 1) ^ β - x ^ β ≤ β * x ^ (β - 1) := by
  have hs : -1 ≤ 1 / x := by
    have : 0 < 1 / x := by positivity
    linarith
  have key := rpow_one_add_le_one_add_mul_self hs hβ0 hβ1
  have e1 : x + 1 = x * (1 + 1 / x) := by field_simp
  have hnn : 0 ≤ 1 + 1 / x := by linarith
  rw [e1, Real.mul_rpow hx.le hnn, Real.rpow_sub_one hx.ne' β]
  have hxb : 0 ≤ x ^ β := Real.rpow_nonneg hx.le β
  have h3 := mul_le_mul_of_nonneg_left key hxb
  have e3 : x ^ β * (1 + β * (1 / x)) = x ^ β + β * (x ^ β / x) := by field_simp
  linarith

/-- squared half-width of the taboo interval -/
theorem tw_sq_le (α c : ℝ) (h0 : 0 < α) (h1 : α < 1) (hc : 0 < c) (s : ℕ) (hs : 1 ≤ s) :
    (tabooHalfWidth α c s) ^ 2 ≤ 4 * c * ((s : ℝ) + 1) ^ (α - 1) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hmono : (s : ℝ) ^ α ≤ ((s : ℝ) + 1) ^ α :=
    Real.rpow_le_rpow hs0.le (by linarith) h0.le
  have hnn : 0 ≤ c * (((s : ℝ) + 1) ^ α - (s : ℝ) ^ α) * (((s : ℝ) + 1) / s) := by
    have : 0 ≤ ((s : ℝ) + 1) ^ α - (s : ℝ) ^ α := by linarith
    positivity
  unfold tabooHalfWidth
  rw [Real.sq_sqrt hnn]
  have hd := rpow_diff_le α s h0.le h1.le hs0
  have hr : ((s : ℝ) + 1) / s ≤ 2 := by
    rw [div_le_iff₀ hs0]; linarith
  -- s^(α-1) ≤ 2 (s+1)^(α-1)
  have hpow : (s : ℝ) ^ (α - 1) ≤ 2 * ((s : ℝ) + 1) ^ (α - 1) := by
    have e : (s : ℝ) ^ (α - 1) = ((s : ℝ) + 1) ^ (α - 1) * (((s : ℝ) + 1) / s) ^ (1 - α) := by
      have haa : ((s : ℝ) + 1) ^ (α - 1) * ((s : ℝ) + 1) ^ (1 - α) = 1 := by
        rw [← Real.rpow_add (by linarith)]; simp
      have hbb : (s : ℝ) ^ (α - 1) * (s : ℝ) ^ (1 - α) = 1 := by
        rw [← Real.rpow_add hs0]; simp
      have hb' : 0 < (s : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hs0 _
      rw [Real.div_rpow (by linarith) hs0.le, ← mul_div_assoc, haa]
      exact eq_one_div_of_mul_eq_one_left hbb
    have h2 : (((s : ℝ) + 1) / s) ^ (1 - α) ≤ 2 ^ (1 - α) :=
      Real.rpow_le_rpow (by positivity) hr (by linarith)
    have h3 : (2 : ℝ) ^ (1 - α) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - α) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hp : 0 ≤ ((s : ℝ) + 1) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
    rw [e]
    calc ((s : ℝ) + 1) ^ (α - 1) * (((s : ℝ) + 1) / s) ^ (1 - α)
        ≤ ((s : ℝ) + 1) ^ (α - 1) * 2 := mul_le_mul_of_nonneg_left (h2.trans h3) hp
      _ = 2 * ((s : ℝ) + 1) ^ (α - 1) := by ring
  have hc1 : (0 : ℝ) ≤ ((s : ℝ) + 1) ^ α - (s : ℝ) ^ α := by linarith
  have hd2 : ((s : ℝ) + 1) ^ α - (s : ℝ) ^ α ≤ 2 * ((s : ℝ) + 1) ^ (α - 1) := by
    calc _ ≤ α * (s : ℝ) ^ (α - 1) := hd
      _ ≤ 1 * (s : ℝ) ^ (α - 1) :=
          mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hs0.le _)
      _ = (s : ℝ) ^ (α - 1) := one_mul _
      _ ≤ _ := hpow
  have hq : 0 ≤ ((s : ℝ) + 1) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
  calc c * (((s : ℝ) + 1) ^ α - (s : ℝ) ^ α) * (((s : ℝ) + 1) / s)
      ≤ c * (2 * ((s : ℝ) + 1) ^ (α - 1)) * 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hd2 hc.le) hr (by positivity)
        positivity
    _ = 4 * c * ((s : ℝ) + 1) ^ (α - 1) := by ring

end Red220

namespace Red220

open CVPricing.Regret KeskinZeevi.SufficientConditions

theorem sq_split (x pO w tw e D C ρ : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C) (hρ : 0 < ρ) (htw : 0 ≤ tw)
    (he : 0 ≤ e) (hx : |x - pO| ≤ D)
    (h : e ≤ ρ → |x - w| ≤ 2 * tw ∧ |w - pO| ≤ C * e) :
    (x - pO) ^ 2 ≤ 8 * tw ^ 2 + (2 * C ^ 2 + D ^ 2 / ρ ^ 2) * e ^ 2 := by
  have hpos : 0 ≤ D ^ 2 / ρ ^ 2 * e ^ 2 := by positivity
  by_cases hle : e ≤ ρ
  · obtain ⟨h1, h2⟩ := h hle
    have a1 : (x - w) ^ 2 ≤ (2 * tw) ^ 2 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
    have a2 : (w - pO) ^ 2 ≤ (C * e) ^ 2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    have e1 : (x - pO) ^ 2 ≤ 2 * (x - w) ^ 2 + 2 * (w - pO) ^ 2 := by
      nlinarith [sq_nonneg (x - w - (w - pO))]
    nlinarith [sq_nonneg C]
  · push_neg at hle
    have a1 : (x - pO) ^ 2 ≤ D ^ 2 := sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
    have a2 : ρ ^ 2 ≤ e ^ 2 := by nlinarith
    have a3 : D ^ 2 = D ^ 2 / ρ ^ 2 * ρ ^ 2 := by field_simp
    have a4 : D ^ 2 / ρ ^ 2 * ρ ^ 2 ≤ D ^ 2 / ρ ^ 2 * e ^ 2 :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    nlinarith [sq_nonneg tw, sq_nonneg C, sq_nonneg e]

theorem one_le_T (T : ℕ∞) (s : ℕ) (hs : 1 ≤ s) (h : (s : ℕ∞) ≤ T) :
    (1 : ℝ≥0∞) ≤ ((T : ℝ≥0∞)) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have h1 : ((s : ℕ∞) : ℝ≥0∞) ≤ (T : ℝ≥0∞) := ENat.toENNReal_le.2 h
  have h2 : ((s : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (s : ℝ) := by
    simp
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h3 : ENNReal.ofReal ((s : ℝ) ^ (1 / 2 : ℝ)) ≤ (T : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hs0.le (by norm_num), ← h2]
    exact ENNReal.rpow_le_rpow h1 (by norm_num)
  calc (1 : ℝ≥0∞) = ENNReal.ofReal ((s : ℝ) ^ (1 / 2 : ℝ)) * ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ))) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), ← Real.rpow_add hs0]
        simp
    _ ≤ _ := by gcongr

end Red220

namespace Red220

open CVPricing.Regret KeskinZeevi.SufficientConditions

theorem pointwise (M : CVPricing.Regret.Model) (hU : MQLEUnique M) {Ω : Type*}
    (p d : ℕ → Ω → ℝ) (ω : Ω) (α c ρ₀ ρ' C : ℝ) (s : ℕ) (hρ' : 0 < ρ') (hC : 0 < C)
    (hω : IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) (hs : 2 ≤ s)
    (hf : ∀ a, IsMQLE M (fun t => p t ω) (fun t => d t ω) s a → euclidNorm (a - M.a0) ≤ ρ' →
      |p (s + 1) ω - optPriceOf M a| ≤ 2 * tabooHalfWidth α c s)
    (hl : ∀ a, euclidNorm (a - M.a0) ≤ ρ' →
      |optPriceOf M a - pOpt M| ≤ C * euclidNorm (a - M.a0)) :
    ENNReal.ofReal ((p (s + 1) ω - pOpt M) ^ 2) ≤
      ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
      ENNReal.ofReal (2 * C ^ 2 + (M.ph - M.pl) ^ 2 / ρ' ^ 2) *
        ENNReal.ofReal (if (s : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d s ω - M.a0) ^ 2 else 0) +
      ENNReal.ofReal ((M.ph - M.pl) ^ 2) *
        (((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  have hpr := prices_mem M α c _ _ hω
  have hpO := pOpt_mem M
  have hx : |p (s + 1) ω - pOpt M| ≤ M.ph - M.pl := by
    have h1 := hpr (s + 1) (by omega)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, hpO.1, hpO.2]
  have hD : 0 ≤ M.ph - M.pl := le_trans (abs_nonneg _) hx
  have hfx : (p (s + 1) ω - pOpt M) ^ 2 ≤ (M.ph - M.pl) ^ 2 :=
    sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
  by_cases hT : (s : ℕ∞) > Tρ M p d ρ₀ ω
  · have hex : ∃ a, IsMQLE M (fun t => p t ω) (fun t => d t ω) s a ∧
        euclidNorm (a - M.a0) ≤ ρ₀ := by
      by_contra hno
      have hmem : (s : ℕ∞) ∈ {n : ℕ∞ | ∃ t : ℕ, (t : ℕ∞) = n ∧ 1 ≤ t ∧
          ¬ ∃ a, IsMQLE M (fun s => p s ω) (fun s => d s ω) t a ∧ euclidNorm (a - M.a0) ≤ ρ₀} :=
        ⟨s, rfl, by omega, hno⟩
      exact absurd (le_sSup hmem) (not_le.2 hT)
    obtain ⟨a, ha, hae⟩ := hex
    have hmq : mqle M p d s ω = a := by
      have hex' : ∃ a, IsMQLE M (fun t => p t ω) (fun t => d t ω) s a := ⟨a, ha⟩
      unfold mqle
      rw [dif_pos hex']
      exact hU (fun t => p t ω) (fun t => d t ω) s hs
        (fun i hi => hpr i (Finset.mem_Icc.1 hi).1) hω.2.2.1
        (Classical.choose_spec hex') ha
    have hI : (if (s : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d s ω - M.a0) ^ 2 else 0) = euclidNorm (a - M.a0) ^ 2 := by
      rw [if_pos hT, hmq]
    rw [hI]
    have hs1 : 1 ≤ s := by omega
    have htw : 0 ≤ tabooHalfWidth α c s := Real.sqrt_nonneg _
    have hB : 0 ≤ 2 * C ^ 2 + (M.ph - M.pl) ^ 2 / ρ' ^ 2 := by positivity
    have hnorm : 0 ≤ euclidNorm (a - M.a0) := Real.sqrt_nonneg _
    have key := sq_split (p (s + 1) ω) (pOpt M) (optPriceOf M a) (tabooHalfWidth α c s)
      (euclidNorm (a - M.a0)) (M.ph - M.pl) C ρ' hD hC.le hρ' htw hnorm hx
      (fun he => ⟨hf a ha he, hl a he⟩)
    calc ENNReal.ofReal ((p (s + 1) ω - pOpt M) ^ 2)
        ≤ ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2 +
            (2 * C ^ 2 + (M.ph - M.pl) ^ 2 / ρ' ^ 2) * euclidNorm (a - M.a0) ^ 2) :=
          ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
            ENNReal.ofReal (2 * C ^ 2 + (M.ph - M.pl) ^ 2 / ρ' ^ 2) *
              ENNReal.ofReal (euclidNorm (a - M.a0) ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul hB]
      _ ≤ _ := le_self_add
  · push_neg at hT
    have hone := one_le_T (Tρ M p d ρ₀ ω) s (by omega) hT
    calc ENNReal.ofReal ((p (s + 1) ω - pOpt M) ^ 2)
        ≤ ENNReal.ofReal ((M.ph - M.pl) ^ 2) := ENNReal.ofReal_le_ofReal hfx
      _ = ENNReal.ofReal ((M.ph - M.pl) ^ 2) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal ((M.ph - M.pl) ^ 2) *
          (((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ)))) := by gcongr
      _ ≤ _ := le_add_self

end Red220

namespace Red220

open CVPricing.Regret KeskinZeevi.SufficientConditions

theorem rpow_neg_comp (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) ^ (-γ) ≤ 2 * ((s : ℝ) + 1) ^ (-γ) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hr : ((s : ℝ) + 1) / s ≤ 2 := by
    rw [div_le_iff₀ hs0]; linarith
  have e : (s : ℝ) ^ (-γ) = ((s : ℝ) + 1) ^ (-γ) * (((s : ℝ) + 1) / s) ^ γ := by
    have haa : ((s : ℝ) + 1) ^ (-γ) * ((s : ℝ) + 1) ^ γ = 1 := by
      rw [← Real.rpow_add (by linarith)]; simp
    have hbb : (s : ℝ) ^ (-γ) * (s : ℝ) ^ γ = 1 := by
      rw [← Real.rpow_add hs0]; simp
    have hb' : 0 < (s : ℝ) ^ γ := Real.rpow_pos_of_pos hs0 _
    rw [Real.div_rpow (by linarith) hs0.le, ← mul_div_assoc, haa]
    exact eq_one_div_of_mul_eq_one_left hbb
  have h2 : (((s : ℝ) + 1) / s) ^ γ ≤ 2 ^ γ :=
    Real.rpow_le_rpow (by positivity) hr h0
  have h3 : (2 : ℝ) ^ γ ≤ 2 := by
    calc (2 : ℝ) ^ γ ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 := Real.rpow_one 2
  have hp : 0 ≤ ((s : ℝ) + 1) ^ (-γ) := Real.rpow_nonneg (by linarith) _
  rw [e]
  calc ((s : ℝ) + 1) ^ (-γ) * (((s : ℝ) + 1) / s) ^ γ
      ≤ ((s : ℝ) + 1) ^ (-γ) * 2 := mul_le_mul_of_nonneg_left (h2.trans h3) hp
    _ = 2 * ((s : ℝ) + 1) ^ (-γ) := by ring

theorem euclid_ball (a b : ℝ × ℝ) (ε : ℝ) (h : euclidNorm (a - b) < ε) : dist a b < ε := by
  have h1 : |a.1 - b.1| ≤ euclidNorm (a - b) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.2 - b.2)])
  have h2 : |a.2 - b.2| ≤ euclidNorm (a - b) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.1 - b.1)])
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt (lt_of_le_of_lt h1 h) (lt_of_le_of_lt h2 h)

end Red220

namespace Red220

open CVPricing.Regret KeskinZeevi.SufficientConditions

theorem bigstep (M : CVPricing.Regret.Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (p d : ℕ → Ω → ℝ)
    (α c ρ₀ ρ' C K₁ : ℝ) (s : ℕ) (hs : 2 ≤ s) (hρ' : 0 < ρ') (hC : 0 < C)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω))
    (hf : ∀ (p' d' : ℕ → ℝ), IsCVPPath M α c p' d' → ∀ a, IsMQLE M p' d' s a →
      euclidNorm (a - M.a0) ≤ ρ' → |p' (s + 1) - optPriceOf M a| ≤ 2 * tabooHalfWidth α c s)
    (hl : ∀ a, euclidNorm (a - M.a0) ≤ ρ' →
      |optPriceOf M a - pOpt M| ≤ C * euclidNorm (a - M.a0))
    (hTfin : (∫⁻ ω, ((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ∂P) < ⊤)
    (hIint : Integrable (fun ω => if (s : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d s ω - M.a0) ^ 2 else 0) P)
    (hIbd : ∫ ω, (if (s : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d s ω - M.a0) ^ 2 else 0) ∂P ≤ K₁ * (Real.log s / (s : ℝ) ^ α))
    (hK₁ : 0 < K₁) (hα0 : 0 < α) :
    ∫ ω, (p (s + 1) ω - pOpt M) ^ 2 ∂P ≤
      8 * tabooHalfWidth α c s ^ 2 +
      (2 * C ^ 2 + (M.ph - M.pl) ^ 2 / ρ' ^ 2) * (K₁ * (Real.log s / (s : ℝ) ^ α)) +
      (M.ph - M.pl) ^ 2 *
        ((∫⁻ ω, ((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ∂P).toReal * (s : ℝ) ^ (-(1 / 2 : ℝ))) := by
  set I : Ω → ℝ := fun ω => if (s : ℕ∞) > Tρ M p d ρ₀ ω then
          euclidNorm (mqle M p d s ω - M.a0) ^ 2 else 0 with hIdef
  have hInn : ∀ ω, 0 ≤ I ω := by
    intro ω; simp only [hIdef]; split_ifs
    · positivity
    · exact le_rfl
  set B : ℝ := 2 * C ^ 2 + (M.ph - M.pl) ^ 2 / ρ' ^ 2 with hBdef
  have hB : 0 ≤ B := by positivity
  set Wl : ℝ≥0∞ := ∫⁻ ω, ((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ∂P with hWl
  set E : ℝ := Wl.toReal with hEdef
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hlog : 0 ≤ Real.log s := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ s))
  have hRHSnn : 0 ≤ 8 * tabooHalfWidth α c s ^ 2 + B * (K₁ * (Real.log s / (s : ℝ) ^ α)) +
      (M.ph - M.pl) ^ 2 * (E * (s : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have : 0 ≤ (s : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
    have : 0 ≤ Real.log s / (s : ℝ) ^ α := by positivity
    positivity
  by_cases hI : Integrable (fun ω => (p (s + 1) ω - pOpt M) ^ 2) P
  swap
  · rw [integral_undef hI]; exact hRHSnn
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal ((p (s + 1) ω - pOpt M) ^ 2) ≤
      ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
      ENNReal.ofReal B * ENNReal.ofReal (I ω) +
      ENNReal.ofReal ((M.ph - M.pl) ^ 2) *
        (((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    filter_upwards [hCVP] with ω hω
    exact pointwise M hU p d ω α c ρ₀ ρ' C s hρ' hC hω hs
      (fun a ha he => hf (fun t => p t ω) (fun t => d t ω) hω a ha he) hl
  have h1 : ENNReal.ofReal (∫ ω, (p (s + 1) ω - pOpt M) ^ 2 ∂P) =
      ∫⁻ ω, ENNReal.ofReal ((p (s + 1) ω - pOpt M) ^ 2) ∂P :=
    ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have h2 : ENNReal.ofReal (∫ ω, I ω ∂P) = ∫⁻ ω, ENNReal.ofReal (I ω) ∂P :=
    ofReal_integral_eq_lintegral_ofReal hIint (Filter.Eventually.of_forall hInn)
  have hmeasJ : AEMeasurable (fun ω => ENNReal.ofReal (I ω)) P :=
    hIint.aemeasurable.ennreal_ofReal
  have hmeasA : AEMeasurable (fun ω => ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
      ENNReal.ofReal B * ENNReal.ofReal (I ω)) P :=
    (hmeasJ.const_mul _).const_add _
  have h3 : ∫⁻ ω, (ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
      ENNReal.ofReal B * ENNReal.ofReal (I ω) +
      ENNReal.ofReal ((M.ph - M.pl) ^ 2) *
        (((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ))))) ∂P
      = ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
        ENNReal.ofReal B * ∫⁻ ω, ENNReal.ofReal (I ω) ∂P +
        ENNReal.ofReal ((M.ph - M.pl) ^ 2) *
          (Wl * ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    rw [lintegral_add_left' hmeasA, lintegral_add_left' aemeasurable_const,
      lintegral_const, lintegral_const_mul'' _ hmeasJ,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    simp only [measure_univ, mul_one]
    rfl
  have hWE : Wl = ENNReal.ofReal E := (ENNReal.ofReal_toReal hTfin.ne).symm
  have hk0 : 0 ≤ (s : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
  have hA0 : 0 ≤ 8 * tabooHalfWidth α c s ^ 2 := by positivity
  have hq0 : 0 ≤ Real.log s / (s : ℝ) ^ α := by positivity
  have hfin : ENNReal.ofReal (∫ ω, (p (s + 1) ω - pOpt M) ^ 2 ∂P) ≤
      ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2 + B * (K₁ * (Real.log s / (s : ℝ) ^ α)) +
        (M.ph - M.pl) ^ 2 * (E * (s : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    rw [h1]
    calc ∫⁻ ω, ENNReal.ofReal ((p (s + 1) ω - pOpt M) ^ 2) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
          ENNReal.ofReal B * ENNReal.ofReal (I ω) +
          ENNReal.ofReal ((M.ph - M.pl) ^ 2) *
            (((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ))))) ∂P := lintegral_mono_ae hae
      _ = _ := h3
      _ ≤ ENNReal.ofReal (8 * tabooHalfWidth α c s ^ 2) +
          ENNReal.ofReal B * ENNReal.ofReal (K₁ * (Real.log s / (s : ℝ) ^ α)) +
          ENNReal.ofReal ((M.ph - M.pl) ^ 2) *
            (ENNReal.ofReal E * ENNReal.ofReal ((s : ℝ) ^ (-(1 / 2 : ℝ)))) := by
          rw [← h2, hWE]
          gcongr
      _ = _ := by
          have hX : 0 ≤ B * (K₁ * (Real.log s / (s : ℝ) ^ α)) := by positivity
          have hY : 0 ≤ (M.ph - M.pl) ^ 2 * (E * (s : ℝ) ^ (-(1 / 2 : ℝ))) := by positivity
          conv_rhs => rw [ENNReal.ofReal_add (add_nonneg hA0 hX) hY, ENNReal.ofReal_add hA0 hX,
            ENNReal.ofReal_mul hB, ENNReal.ofReal_mul (sq_nonneg _),
            ENNReal.ofReal_mul hE]
  exact (ENNReal.ofReal_le_ofReal_iff hRHSnn).1 hfin

end Red220

namespace Red220

open CVPricing.Regret KeskinZeevi.SufficientConditions

theorem main (M : CVPricing.Regret.Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
      ∫ ω, (p t ω - pOpt M) ^ 2 ∂P
        ≤ K * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) := by
  have : (ae P).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero P)
  obtain ⟨ω0, h0⟩ := hCVP.exists
  have hα0 : 0 < α := by linarith
  have hα1 : α < 1 := h0.2.2.2.1.2
  have hc0 : 0 < c := h0.2.2.2.2.1
  obtain ⟨-, -, ρ₀, hρ₀, hTfin, K₁, hK₁, hrate⟩ :=
    mqle_consistency_rate M hU P ℱ p d hD α c p₁ p₂ hα hp₁ hp₂ hCVP
  obtain ⟨ρf, hρf, tf, hf⟩ := price_near_optimum_taboo M hU α c
  obtain ⟨V, hV, C, hC, hlip⟩ := optPrice_lipschitz M
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hnear : ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ε / 2 → a ∈ V := fun a ha =>
    hball (Metric.mem_ball.2 (euclid_ball a M.a0 ε (by linarith)))
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ' : ℝ, ρ' = min ρf (ε / 2) := ⟨_, rfl⟩
  have hρ' : 0 < ρ' := by rw [hρ'def]; exact lt_min hρf (by linarith)
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = M.ph - M.pl := ⟨_, rfl⟩
  have hD0 : 0 < D := by have := M.pl_lt_ph; rw [hDdef]; linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * C ^ 2 + D ^ 2 / ρ' ^ 2 := ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = (∫⁻ ω, ((Tρ M p d ρ₀ ω : ℝ≥0∞)) ^ (1 / 2 : ℝ) ∂P).toReal :=
    ⟨_, rfl⟩
  have hE : 0 ≤ E := by rw [hEdef]; exact ENNReal.toReal_nonneg
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max tf 2 := ⟨_, rfl⟩
  have hN2 : 2 ≤ N := by rw [hNdef]; exact le_max_right _ _
  have hNtf : tf ≤ N := by rw [hNdef]; exact le_max_left _ _
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 32 * c + 2 * B * K₁ + 2 * D ^ 2 * E := ⟨_, rfl⟩
  have hK₂pos : 0 < K₂ := by
    have h1 : 0 ≤ 2 * B * K₁ := by positivity
    have h2 : 0 ≤ 2 * D ^ 2 * E := by positivity
    rw [hK₂]; linarith
  have hpO := pOpt_mem M
  -- the large-t bound
  have hbig : ∀ s : ℕ, N ≤ s → ∫ ω, (p (s + 1) ω - pOpt M) ^ 2 ∂P ≤
      K₂ * (((s : ℝ) + 1) ^ (α - 1) + Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) := by
    intro s hs
    have hs2 : 2 ≤ s := hN2.trans hs
    have hb := bigstep M hU P p d α c ρ₀ ρ' C K₁ s hs2 hρ' hC hCVP
      (fun p' d' hp' a ha he => hf s (hNtf.trans hs) p' d' hp' a ha
        (he.trans (by rw [hρ'def]; exact min_le_left _ _)))
      (fun a he => hlip a (hnear a (he.trans (by rw [hρ'def]; exact min_le_right _ _))))
      hTfin (hrate s hs2).1 (hrate s hs2).2 hK₁ hα0
    rw [← hDdef, ← hBdef, ← hEdef] at hb
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
    have hs0 : (0 : ℝ) < s := by linarith
    have htw := tw_sq_le α c hα0 hα1 hc0 s (by omega)
    have hlog : Real.log s ≤ Real.log ((s : ℝ) + 1) := Real.log_le_log hs0 (by linarith)
    have hlog0 : 0 ≤ Real.log s := Real.log_nonneg hs1
    have hY1 := rpow_neg_comp α hα0.le hα1.le s (by omega)
    have hY2 := rpow_neg_comp (1 / 2) (by norm_num) (by norm_num) s (by omega)
    have hY3 : ((s : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ ((s : ℝ) + 1) ^ (α - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hX0 : 0 ≤ ((s : ℝ) + 1) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
    have hL0 : 0 ≤ Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α := by
      have : 0 ≤ Real.log ((s : ℝ) + 1) := Real.log_nonneg (by linarith)
      positivity
    have hq : Real.log s / (s : ℝ) ^ α ≤ 2 * (Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) := by
      have e1 : Real.log s / (s : ℝ) ^ α = Real.log s * (s : ℝ) ^ (-α) := by
        rw [Real.rpow_neg hs0.le, div_eq_mul_inv]
      have e2 : Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α =
          Real.log ((s : ℝ) + 1) * ((s : ℝ) + 1) ^ (-α) := by
        rw [Real.rpow_neg (by linarith), div_eq_mul_inv]
      have hp0 : 0 ≤ ((s : ℝ) + 1) ^ (-α) := Real.rpow_nonneg (by linarith) _
      have hlog1 : 0 ≤ Real.log ((s : ℝ) + 1) := Real.log_nonneg (by linarith)
      rw [e1, e2]
      calc Real.log s * (s : ℝ) ^ (-α) ≤ Real.log ((s : ℝ) + 1) * (2 * ((s : ℝ) + 1) ^ (-α)) :=
            mul_le_mul hlog hY1 (Real.rpow_nonneg hs0.le _) hlog1
        _ = _ := by ring
    have t1 : 8 * tabooHalfWidth α c s ^ 2 ≤ 32 * c * ((s : ℝ) + 1) ^ (α - 1) := by linarith
    have t2 : B * (K₁ * (Real.log s / (s : ℝ) ^ α)) ≤
        B * (K₁ * (2 * (Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hK₁.le) hB
    have t3 : D ^ 2 * (E * (s : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        D ^ 2 * (E * (2 * ((s : ℝ) + 1) ^ (α - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hY2.trans (by linarith)) hE)
        (sq_nonneg _)
    have p1 : 0 ≤ c * (Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) := mul_nonneg hc0.le hL0
    have p2 : 0 ≤ B * K₁ * ((s : ℝ) + 1) ^ (α - 1) := by positivity
    have p3 : 0 ≤ D ^ 2 * E * (Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) := by positivity
    rw [hDdef] at hb
    rw [hK₂]
    rw [← hDdef] at hb
    nlinarith [hb, t1, t2, t3, p1, p2, p3]
  -- the crude bound
  have hsmall : ∀ t : ℕ, 1 ≤ t → ∫ ω, (p t ω - pOpt M) ^ 2 ∂P ≤ D ^ 2 := by
    intro t ht
    by_cases hI : Integrable (fun ω => (p t ω - pOpt M) ^ 2) P
    · calc ∫ ω, (p t ω - pOpt M) ^ 2 ∂P ≤ ∫ _ : Ω, D ^ 2 ∂P := by
            apply integral_mono_ae hI (integrable_const _)
            filter_upwards [hCVP] with ω hω
            have h1 := prices_mem M α c _ _ hω t ht
            have : |p t ω - pOpt M| ≤ D := by
              rw [abs_le, hDdef]; constructor <;> linarith [h1.1, h1.2, hpO.1, hpO.2]
            exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
        _ = D ^ 2 := by simp
    · rw [integral_undef hI]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨K₂ + D ^ 2 * (N : ℝ) ^ (1 - α) + 1, by positivity, fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have ht0 : (0 : ℝ) < t := by linarith
  have hX0 : 0 ≤ (t : ℝ) ^ (α - 1) := Real.rpow_nonneg ht0.le _
  have hL0 : 0 ≤ Real.log t / (t : ℝ) ^ α := by
    have : 0 ≤ Real.log t := Real.log_nonneg ht1
    positivity
  have hR0 : 0 ≤ (t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α := by linarith
  have hK3 : 0 ≤ D ^ 2 * (N : ℝ) ^ (1 - α) := by positivity
  rcases le_or_gt (N + 1) t with h | h
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have := hbig s (by omega)
    push_cast at hR0 this ⊢
    have e : (K₂ + D ^ 2 * (N : ℝ) ^ (1 - α) + 1) *
        (((s : ℝ) + 1) ^ (α - 1) + Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) =
        K₂ * (((s : ℝ) + 1) ^ (α - 1) + Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) +
        D ^ 2 * (N : ℝ) ^ (1 - α) *
          (((s : ℝ) + 1) ^ (α - 1) + Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) +
        (((s : ℝ) + 1) ^ (α - 1) + Real.log ((s : ℝ) + 1) / ((s : ℝ) + 1) ^ α) := by ring
    rw [e]
    linarith [mul_nonneg hK3 hR0]
  · have hle : (t : ℝ) ≤ N := by exact_mod_cast (by omega : t ≤ N)
    have h1 : (N : ℝ) ^ (α - 1) ≤ (t : ℝ) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos ht0 hle (by linarith)
    have h2 : (N : ℝ) ^ (1 - α) * (N : ℝ) ^ (α - 1) = 1 := by
      rw [← Real.rpow_add hNpos]; simp
    have h3 : D ^ 2 ≤ D ^ 2 * (N : ℝ) ^ (1 - α) * (t : ℝ) ^ (α - 1) := by
      calc D ^ 2 = D ^ 2 * ((N : ℝ) ^ (1 - α) * (N : ℝ) ^ (α - 1)) := by rw [h2, mul_one]
        _ = D ^ 2 * (N : ℝ) ^ (1 - α) * (N : ℝ) ^ (α - 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hK3
    have h4 := hsmall t (by omega)
    have h5 : D ^ 2 * (N : ℝ) ^ (1 - α) * (t : ℝ) ^ (α - 1) ≤
        D ^ 2 * (N : ℝ) ^ (1 - α) * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) :=
      mul_le_mul_of_nonneg_left (by linarith) hK3
    have e : (K₂ + D ^ 2 * (N : ℝ) ^ (1 - α) + 1) *
        ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) =
        K₂ * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) +
        D ^ 2 * (N : ℝ) ^ (1 - α) * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) +
        ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) := by ring
    rw [e]
    linarith [mul_nonneg hK₂pos.le hR0]

end Red220

open CVPricing.Regret MeasureTheory in
theorem solution (M : Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
      ∫ ω, (p t ω - pOpt M) ^ 2 ∂P
        ≤ K * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α) := by
  exact Red220.main M hU P ℱ p d hD α c p₁ p₂ hα hp₁ hp₂ hCVP
