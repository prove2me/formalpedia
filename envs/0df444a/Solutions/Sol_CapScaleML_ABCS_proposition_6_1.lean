-- Prove2me | solution 1 for CapScaleML.ABCS.proposition_6_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:22:00.813419+00:00
-- url     : https://prove2.me/submissions/8441f8db-4b84-4b1a-993d-910b98f1c937

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS.CostBug411

noncomputable abbrev T0 : ℝ := Real.pi / 16
noncomputable abbrev L1 : ℝ → ℝ := fun _ => 1
noncomputable abbrev Z0 : ℝ → ℝ := fun _ => 0
noncomputable abbrev MA : ℝ → ℝ := apOnline 32 1 L1 Z0
noncomputable abbrev mT : ℝ → ℝ := fun t => 1 - Real.cos (8 * t)
noncomputable abbrev qT : ℝ → ℝ := fun t => Real.sin (8 * t) / 8

lemma T0_pos : 0 < T0 := by positivity
lemma T0_lt : T0 < 1 / 4 := by
  have := Real.pi_lt_four; show Real.pi / 16 < 1 / 4; linarith

lemma ofReal_sum_le (n : ℕ) (f : ℕ → ℝ) :
    ENNReal.ofReal (∑ i ∈ Finset.range n, f i) ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact ENNReal.ofReal_add_le.trans (add_le_add ih le_rfl)

/-- The switching functional dominates every value of a schedule starting at zero. -/
lemma switching_ge (T : ℝ) (m : ℝ → ℝ) (hm0 : m 0 = 0) (t : ℝ) (ht : t ∈ Ioc 0 T) :
    ENNReal.ofReal (m t) ≤ switching T m := by
  unfold switching
  refine Filter.le_limsup_of_frequently_le ?_ (by isBoundedDefault)
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hU
  obtain ⟨k, hk⟩ := exists_nat_gt (t / ε)
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  set n : ℕ := k + 1 with hndef
  have hn : (n : ℝ) = k + 1 := by rw [hndef]; push_cast; ring
  have hnpos : (0:ℝ) < n := by rw [hn]; exact hk1
  set δ := t / (n : ℝ) with hδdef
  have hδ : 0 < δ := div_pos ht.1 hnpos
  refine ⟨δ, hsub ⟨hδ, ?_⟩, ?_⟩
  · rw [hδdef, div_lt_iff₀ hnpos, hn]
    have hε' : (0:ℝ) < ε := hε
    rw [div_lt_iff₀ hε'] at hk
    nlinarith
  · unfold switchSum
    have hnδ : (n : ℝ) * δ = t := by
      rw [hδdef]; field_simp
    have hNn : n ≤ ⌊T / δ⌋₊ := by
      apply Nat.le_floor
      rw [le_div_iff₀ hδ, hnδ]; exact ht.2
    have hsub' : Finset.range n ⊆ Finset.range (⌊T / δ⌋₊ + 1) :=
      Finset.range_subset_range.mpr (by omega)
    calc ENNReal.ofReal (m t)
        = ENNReal.ofReal (∑ i ∈ Finset.range n, (m ((((i:ℕ):ℝ) + 1) * δ) - m ((i:ℝ) * δ))) := by
          congr 1
          have tele := Finset.sum_range_sub (fun i : ℕ => m ((i:ℝ) * δ)) n
          push_cast at tele
          rw [tele, hnδ]; simp [hm0]
      _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (m ((((i:ℕ):ℝ) + 1) * δ) - m ((i:ℝ) * δ)) :=
          ofReal_sum_le n _
      _ = ∑ i ∈ Finset.range n,
            ENNReal.ofReal (m (min ((((i:ℕ):ℝ) + 1) * δ) T) - m ((i:ℝ) * δ)) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi' : ((i:ℝ) + 1) ≤ n := by
            have := Finset.mem_range.mp hi
            exact_mod_cast this
          rw [min_eq_left]
          calc ((i:ℝ) + 1) * δ ≤ n * δ := by gcongr
            _ = t := hnδ
            _ ≤ T := ht.2
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub'

lemma switching_zero (t : ℝ) : switching t (fun _ => (0:ℝ)) = 0 := by
  unfold switching switchSum
  simp

lemma cost_zero (t ω β θ : ℝ) : cost ω β θ t Z0 Z0 = 0 := by
  unfold cost
  rw [switching_zero]
  simp

lemma workload_zero (T : ℝ) : IsWorkload T Z0 Z0 Z0 := by
  refine ⟨?_, ?_⟩
  · simp
  · intro t _; simp

lemma adm_zero (T : ℝ) : Admissible T Z0 := ⟨rfl, fun _ _ => le_rfl, intervalIntegrable_const⟩

lemma opt_zero (ω β θ T : ℝ) : opt ω β θ T Z0 = 0 :=
  le_antisymm (iInf_le_of_le Z0 (iInf_le_of_le Z0 (iInf_le_of_le ⟨adm_zero T, workload_zero T⟩
    (cost_zero T ω β θ).le))) bot_le

lemma ap_advice : IsAPAdvice 32 1 0 T0 L1 Z0 MA :=
  ⟨Z0, Z0, ⟨adm_zero _, workload_zero _, by rw [cost_zero, opt_zero]⟩, fun t _ => by simp [MA]⟩

lemma sqrt16 : Real.sqrt 16 = 4 := by
  rw [show (16:ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

lemma sqrt_inv16 : Real.sqrt (1 / 16) = 1 / 4 := by
  rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

lemma MA_val (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/4)) : MA t = 4 * t := by
  show apOnline 32 1 L1 Z0 t = 4 * t
  unfold apOnline
  rw [show (32 / (2 * 1) : ℝ) = 16 by norm_num, show (2 * 1 / 32 : ℝ) = 1 / 16 by norm_num,
    sqrt16, sqrt_inv16]
  rw [intervalIntegral.integral_congr_Ioo_of_le (g := fun _ => (4:ℝ)) ht.1]
  · simp; ring
  · intro s hs
    simp only [deltaLam]
    rw [if_pos hs.1.le, if_neg (by linarith [hs.2, ht.2])]
    simp

lemma workload_MA : IsWorkload T0 L1 MA (fun t => ∫ s in (0:ℝ)..t, (1 - MA s)) := by
  have hT := T0_lt
  have hT0 := T0_pos
  have hpt : ∀ s ∈ Icc (0:ℝ) T0, ∀ Q : ℝ,
      (if 0 < Q ∨ MA s ≤ L1 s then L1 s - MA s else 0) = 1 - MA s := by
    intro s hs Q
    rw [if_pos (Or.inr (by rw [MA_val s ⟨hs.1, by linarith [hs.2]⟩]; show 4 * s ≤ 1; linarith [hs.2]))]
  have hii : IntervalIntegrable (fun s => 1 - MA s) volume 0 T0 := by
    have hc : IntervalIntegrable (fun s : ℝ => 1 - 4 * s) volume 0 T0 :=
      (continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _
    refine hc.congr (fun s hs => ?_)
    rw [uIoc_of_le hT0.le] at hs
    rw [MA_val s ⟨hs.1.le, by linarith [hs.2]⟩]
  refine ⟨?_, ?_⟩
  · refine hii.congr (fun s hs => ?_)
    rw [uIoc_of_le hT0.le] at hs
    exact (hpt s ⟨hs.1.le, hs.2⟩ _).symm
  · intro t ht
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le ht.1] at hs
    exact (hpt s ⟨hs.1, hs.2.trans ht.2⟩ _).symm

/-- The explicit ABCS trajectory with constant rates `r₁ = R₁ = r₂ = R₂ = 2`. -/
lemma abcs_traj_gen (mA qA : ℝ → ℝ) : IsABCS 32 1 0 T0 2 2 2 2 L1 mA qA mT qT := by
  have hT0 := T0_pos
  have hcos : ∀ s ∈ Icc (0:ℝ) T0, 0 ≤ Real.cos (8 * s) := by
    intro s hs
    apply Real.cos_nonneg_of_mem_Icc
    have : s ≤ Real.pi / 16 := hs.2
    have := hs.1
    constructor <;> [skip; show 8 * s ≤ Real.pi / 2] <;> nlinarith [Real.pi_pos]
  have hdrift : abcsDrift 32 1 0 2 2 2 2 mA qA mT qT =
      fun s => 8 * Real.sin (8 * s) := by
    funext s
    simp only [abcsDrift, rateUp, rateDown, ite_self]
    ring
  have hptq : ∀ s ∈ Icc (0:ℝ) T0,
      (if 0 < qT s ∨ mT s ≤ L1 s then L1 s - mT s else 0) = Real.cos (8 * s) := by
    intro s hs
    rw [if_pos (Or.inr (by simp only [mT, L1]; linarith [hcos s hs]))]
    simp [mT]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have hc : IntervalIntegrable (fun s : ℝ => Real.cos (8 * s)) volume 0 T0 :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    refine hc.congr (fun s hs => ?_)
    rw [uIoc_of_le hT0.le] at hs
    exact (hptq s ⟨hs.1.le, hs.2⟩).symm
  · intro t ht
    rw [intervalIntegral.integral_congr (g := fun s => Real.cos (8 * s)) (fun s hs => by
      rw [uIcc_of_le ht.1] at hs; exact hptq s ⟨hs.1, hs.2.trans ht.2⟩)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.sin (8 * x) / 8)]
    · simp
    · intro x _
      have := ((hasDerivAt_id x).const_mul 8).sin.div_const 8
      simp only [id] at this
      exact this.congr_deriv (by ring)
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · rw [hdrift]
    exact (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · intro t ht
    rw [hdrift]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => 1 - Real.cos (8 * x))]
    · simp
    · intro x _
      have := (((hasDerivAt_id x).const_mul 8).cos).const_sub 1
      simp only [id] at this
      exact this.congr_deriv (by ring)
    · exact (continuous_const.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _

lemma vol_T0 : volume (Icc (0:ℝ) T0) = ENNReal.ofReal T0 := by
  rw [Real.volume_Icc, sub_zero]

/-- Lower bound on the ABCS cost: `2π`. -/
lemma cost_abcs_ge : ENNReal.ofReal (2 * Real.pi) ≤ cost 32 1 0 T0 mT qT := by
  have hS := switching_ge T0 mT (by simp [mT]) T0 ⟨T0_pos, le_rfl⟩
  have hmT : mT T0 = 1 := by
    simp only [mT, T0]
    rw [show 8 * (Real.pi / 16) = Real.pi / 2 by ring, Real.cos_pi_div_two]; simp
  rw [hmT, ENNReal.ofReal_one] at hS
  unfold cost
  calc ENNReal.ofReal (2 * Real.pi) = ENNReal.ofReal 32 * ∫⁻ _ in Icc (0:ℝ) T0, (1 : ℝ≥0∞) := by
        rw [setLIntegral_const, vol_T0, one_mul, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; simp only [T0]; ring
    _ ≤ _ := by
        gcongr with s
        calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal 1 * switching T0 mT := by
              rw [ENNReal.ofReal_one, one_mul]; exact hS
          _ ≤ _ := le_trans le_add_self le_self_add

lemma workload_id : IsWorkload T0 L1 Z0 (fun t => t) := by
  refine ⟨?_, ?_⟩
  · simp
  · intro t _; simp

lemma lint_half (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ s in Icc (0:ℝ) T0, ENNReal.ofReal (c * s) = ENNReal.ofReal (c * (T0 ^ 2 / 2)) := by
  have hint : IntegrableOn (fun s : ℝ => c * s) (Icc (0:ℝ) T0) :=
    (continuous_const.mul continuous_id).integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => mul_nonneg hc hx.1))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le T0_pos.le,
    intervalIntegral.integral_const_mul, integral_id]
  congr 1; ring

lemma opt_le : opt 32 1 0 T0 L1 ≤ ENNReal.ofReal (Real.pi ^ 2 / 16) := by
  refine iInf_le_of_le Z0 (iInf_le_of_le (fun t => t)
    (iInf_le_of_le ⟨adm_zero _, workload_id⟩ ?_))
  unfold cost
  rw [switching_zero]
  simp only [ENNReal.ofReal_one, mul_zero, add_zero, ENNReal.ofReal_zero, zero_mul]
  have := lint_half 1 zero_le_one
  simp only [one_mul] at this
  rw [this, ← ENNReal.ofReal_mul (by norm_num)]
  apply le_of_eq; congr 1; simp only [T0]; ring

lemma integrand_ge (q lam m : ℝ) :
    lam - m ≤ (if 0 < q ∨ m ≤ lam then lam - m else 0) := by
  split_ifs with h
  · exact le_rfl
  · push_neg at h; linarith [h.2]

/-- A positive lower bound on the offline optimum. -/
lemma opt_ge : ENNReal.ofReal (4 * T0 ^ 2) ≤ opt 32 1 0 T0 L1 := by
  have hT0 := T0_pos
  have hT4 := T0_lt
  refine le_iInf (fun m => le_iInf (fun q => le_iInf (fun h => ?_)))
  obtain ⟨⟨hm0, hmnn, hmI⟩, hqI, hqeq⟩ := h
  unfold cost
  by_cases hc : ∃ t ∈ Ioc 0 T0, 1 / 2 ≤ m t
  · obtain ⟨t, ht, hmt⟩ := hc
    have hS := (ENNReal.ofReal_le_ofReal hmt).trans (switching_ge T0 m hm0 t ht)
    calc ENNReal.ofReal (4 * T0 ^ 2) ≤ ENNReal.ofReal 32 * ∫⁻ _ in Icc (0:ℝ) T0,
          ENNReal.ofReal (1 / 2) := by
          rw [setLIntegral_const, vol_T0, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num)]
          apply ENNReal.ofReal_le_ofReal; nlinarith
      _ ≤ _ := by
          gcongr with s
          calc ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal 1 * switching T0 m := by
                rw [ENNReal.ofReal_one, one_mul]; exact hS
            _ ≤ _ := le_trans le_add_self le_self_add
  · push_neg at hc
    have hq : ∀ t ∈ Icc (0:ℝ) T0, (1 / 2) * t ≤ q t := by
      intro t ht
      have hsub : uIcc 0 t ⊆ uIcc 0 T0 := by
        rw [uIcc_of_le ht.1, uIcc_of_le hT0.le]; exact Icc_subset_Icc le_rfl ht.2
      rw [hqeq t ht]
      calc (1 / 2) * t = ∫ s in (0:ℝ)..t, (1 / 2 : ℝ) := by simp; ring
        _ ≤ ∫ s in (0:ℝ)..t, (1 - m s) := by
            apply intervalIntegral.integral_mono_on ht.1 intervalIntegrable_const
              ((intervalIntegrable_const.sub hmI).mono_set hsub)
            intro s hs
            rcases eq_or_lt_of_le hs.1 with h0 | h0
            · rw [← h0, hm0]; norm_num
            · have := hc s ⟨h0, hs.2.trans ht.2⟩; linarith
        _ ≤ _ := by
            apply intervalIntegral.integral_mono_on ht.1
              ((intervalIntegrable_const.sub hmI).mono_set hsub) (hqI.mono_set hsub)
            intro s _
            exact integrand_ge (q s) 1 (m s)
    calc ENNReal.ofReal (4 * T0 ^ 2) ≤ ENNReal.ofReal 32 *
          ∫⁻ s in Icc (0:ℝ) T0, ENNReal.ofReal ((1 / 2) * s) := by
          rw [lint_half _ (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
          apply ENNReal.ofReal_le_ofReal; nlinarith
      _ ≤ _ := by
          refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc (fun s hs => ?_))
          calc ENNReal.ofReal ((1 / 2) * s) ≤ ENNReal.ofReal (q s) := ENNReal.ofReal_le_ofReal (hq s hs)
            _ ≤ _ := le_trans le_self_add le_self_add

lemma PCR_val : PCR 2 2 2 2 = 8 := by
  unfold PCR c6 c5
  rw [show (2 / 2 : ℝ) = 1 by norm_num, Real.sqrt_one]
  norm_num

lemma mae_val : mae T0 Z0 L1 = 1 := by
  unfold mae
  simp only [Z0, L1, zero_sub, abs_neg, abs_one, intervalIntegral.integral_const, smul_eq_mul,
    mul_one, sub_zero]
  exact inv_mul_cancel₀ T0_pos.ne'

lemma acc : IsEtaAccurate 32 1 0 T0 (1 / (4 * T0)) L1 Z0 := by
  have hT0 := T0_pos
  unfold IsEtaAccurate
  rw [mae_val]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hT0])) (Or.inl ENNReal.ofReal_ne_top)]
  calc ENNReal.ofReal 1 * ENNReal.ofReal T0 = ENNReal.ofReal (1 / (4 * T0)) *
        ENNReal.ofReal (4 * T0 ^ 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ _ := mul_le_mul' le_rfl opt_ge

lemma MA_adm : Admissible T0 MA := by
  have hT := T0_lt
  have hT0 := T0_pos
  refine ⟨by rw [MA_val 0 ⟨le_rfl, by norm_num⟩]; ring, fun t ht => ?_, ?_⟩
  · rw [MA_val t ⟨ht.1.le, by linarith [ht.2]⟩]; linarith [ht.1]
  · have hc : IntervalIntegrable (fun s : ℝ => 4 * s) volume 0 T0 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    refine hc.congr (fun s hs => ?_)
    rw [uIoc_of_le hT0.le] at hs
    rw [MA_val s ⟨hs.1.le, by linarith [hs.2]⟩]

lemma OCR_le : OCR 2 2 2 2 ≤ 8 := by
  have h5 : (0:ℝ) < Real.sqrt (1 + 2 * 2) := Real.sqrt_pos.mpr (by norm_num)
  have h5' : (1:ℝ) ≤ Real.sqrt (1 + 2 * 2) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hc2 : c2 2 2 2 = 2 := by
    unfold c2 c1 c3
    field_simp
    ring
  unfold OCR c4 c1 c3
  rw [hc2]
  have : 2 * 2 / Real.sqrt (1 + 2 * 2) ≤ 8 := by
    rw [div_le_iff₀ h5]; nlinarith
  simp only [max_le_iff]
  refine ⟨⟨by norm_num, this⟩, by norm_num, by norm_num⟩

end CapScaleML.ABCS.CostBug411


open CapScaleML.ABCS CapScaleML.ABCS.CostBug411 in
theorem solution : ¬ (∀ (ω β θ T r₁ r₂ R₁ R₂ : ℝ)
    (hω : 0 < ω) (hβ : 0 < β) (hθ : 0 ≤ θ) (hT : 0 < T)
    (hr₁ : 0 < r₁) (hR₁ : r₁ ≤ R₁) (hr₂ : 0 < r₂) (hR₂ : r₂ ≤ R₂)
    (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (mAdv qAdv : ℝ → ℝ) (hAdv : Admissible T mAdv)
    (hqAdv : IsWorkload T lam mAdv qAdv) (m q : ℝ → ℝ)
    (hm : IsABCS ω β θ T r₁ r₂ R₁ R₂ lam mAdv qAdv m q),
    cost ω β θ T m q ≤ ENNReal.ofReal (PCR r₁ r₂ R₁ R₂) * opt ω β θ T lam) := by
  intro H
  have hT0 := T0_pos
  have h := H 32 1 0 T0 2 2 2 2 (by norm_num) (by norm_num) le_rfl hT0
    (by norm_num) le_rfl (by norm_num) le_rfl L1
    (fun _ _ => zero_le_one) intervalIntegrable_const
    MA _ MA_adm workload_MA mT qT (abcs_traj_gen _ _)
  have h2 := cost_abcs_ge.trans h
  rw [PCR_val] at h2
  have h3 := h2.trans (mul_le_mul' le_rfl opt_le)
  rw [← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have := Real.pi_lt_four
  have := Real.pi_pos
  nlinarith
