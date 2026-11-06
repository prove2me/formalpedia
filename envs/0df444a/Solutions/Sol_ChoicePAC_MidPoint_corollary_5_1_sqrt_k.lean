-- Prove2me | solution 1 for ChoicePAC.MidPoint.corollary_5_1_sqrt_k
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:15:07.014627+00:00
-- url     : https://prove2.me/submissions/74277589-501d-45d5-b119-2027339e8ef4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions
import Definitions.Def_ChoicePAC_MidPoint_GF
import Theorems.Thm_ChoicePAC_MidPoint_theorem_5_3_general_bound

open ChoicePAC.MidPoint MeasureTheory

namespace CorAux

lemma telescope (f : ℕ → ℝ) (a : ℕ) :
    ∑ j ∈ Finset.Icc 1 a, (f j - f (j - 1)) = f a - f 0 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]; ring

lemma time_succ (s : Schedule) (j : ℕ) (h1 : 1 ≤ j) (hj : j ≤ s.M) :
    s.time j = s.t ⟨j - 1, by omega⟩ := by
  unfold Schedule.time
  rw [if_neg (by omega), dif_pos (by omega)]

lemma time_lt_one (s : Schedule) (j : ℕ) (hj : j ≤ s.M) : s.time j < 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | h
  · simp [Schedule.time]
  · rw [time_succ s j h hj]; exact s.lt_one _

lemma time_mono (s : Schedule) (j : ℕ) (h1 : 1 ≤ j) (hj : j ≤ s.M) :
    s.time (j - 1) ≤ s.time j := by
  rw [time_succ s j h1 hj]
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · subst h; simp [Schedule.time]; exact (s.pos _).le
  · rw [time_succ s (j - 1) (by omega) (by omega)]
    apply s.strictMono.monotone
    show j - 1 - 1 ≤ j - 1
    omega

/-- For every schedule, `G(k, t) ≤ t` on `[0, 1]`. -/
lemma G_le (s : Schedule) (t : ℝ) (ht1 : t ≤ 1) : s.G t ≤ t := by
  classical
  unfold Schedule.G Schedule.idx
  set a := (Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t)).card with ha
  rw [Nat.add_sub_cancel]
  have haM : a ≤ s.M := by
    have := Finset.card_le_univ (Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t))
    simpa using this
  have hj : ∀ j, 1 ≤ j → j ≤ a → s.time j ≤ t := by
    intro j h1 hja
    rw [time_succ s j h1 (hja.trans haM)]
    by_contra hlt
    push Not at hlt
    have hsub : Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t) ⊆
        Finset.univ.filter (fun l : Fin s.M => l.val < j - 1) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      have : s.t l < s.t ⟨j - 1, by omega⟩ := lt_of_le_of_lt hl hlt
      exact s.strictMono.lt_iff_lt.mp this
    have hc := Finset.card_le_card hsub
    have hc2 : (Finset.univ.filter (fun l : Fin s.M => l.val < j - 1)).card ≤ j - 1 := by
      calc (Finset.univ.filter (fun l : Fin s.M => l.val < j - 1)).card
          ≤ (Finset.range (j - 1)).card := by
            apply Finset.card_le_card_of_injOn (fun l => l.val)
            · intro l hl; simp at hl ⊢; exact hl
            · intro x _ y _ h; exact Fin.ext h
        _ = j - 1 := Finset.card_range _
    rw [← ha] at hc
    omega
  have hterm : ∀ j ∈ Finset.Icc 1 a,
      (s.time j - s.time (j - 1)) * (1 - t) ^ 2 / (1 - s.time j) ^ 2 ≤
        s.time j - s.time (j - 1) := by
    intro j hjm
    rw [Finset.mem_Icc] at hjm
    have hx : 0 ≤ s.time j - s.time (j - 1) := by
      linarith [time_mono s j hjm.1 (hjm.2.trans haM)]
    have hlt1 := time_lt_one s j (hjm.2.trans haM)
    have htj := hj j hjm.1 hjm.2
    have hden : 0 < (1 - s.time j) ^ 2 := by
      have : 0 < 1 - s.time j := by linarith
      positivity
    rw [div_le_iff₀ hden]
    have h1 : (1 - t) ^ 2 ≤ (1 - s.time j) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    nlinarith
  have := Finset.sum_le_sum hterm
  rw [telescope (fun j => s.time j)] at this
  have h0 : s.time 0 = 0 := by simp [Schedule.time]
  rw [h0] at this
  linarith

end CorAux

theorem solution {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) :
    ∃ ρ ρhat : ℝ, 0 < ρ ∧ 0 < ρhat ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s : Schedule, ∀ sel, I.IsAdmissibleSelector sel →
        I.dlpValue ((k : ℝ) • I.C) ((k : ℝ) • I.lam) - I.pacValue sel k s ≤
          ρ + ρhat * Real.sqrt k := by
  obtain ⟨ρ, ρhat, ρ', hρ, hρhat, hρ', h53⟩ := theorem_5_3_general_bound I hI h21 h22
  set c0 : ℝ := 1 / (1 + |I.ξmax|) with hc0
  have hc0pos : 0 < c0 := by positivity
  have hc0le : c0 ≤ 1 := by
    rw [hc0, div_le_one (by positivity)]; linarith [abs_nonneg I.ξmax]
  have hc0ξ : c0 * I.ξmax ≤ 1 := by
    rw [hc0, one_div_mul_eq_div, div_le_one (by positivity)]
    linarith [le_abs_self I.ξmax]
  set v : ℕ → ℝ → ℝ := fun k _ => c0 / Real.sqrt (max 1 (k : ℝ)) with hv
  have hvprop : ∀ k' : ℕ, 1 ≤ k' → ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 < v k' t ∧ v k' t ≤ 1 ∧ v k' t * I.ξmax ≤ 1 := by
    intro k' _ t _ _
    have hs : 1 ≤ Real.sqrt (max 1 (k' : ℝ)) := by
      rw [Real.one_le_sqrt]; exact le_max_left _ _
    have hspos : 0 < Real.sqrt (max 1 (k' : ℝ)) := by linarith
    have hvle : v k' t ≤ c0 := by
      show c0 / _ ≤ c0
      rw [div_le_iff₀ hspos]; nlinarith
    have hvpos : 0 < v k' t := div_pos hc0pos hspos
    refine ⟨hvpos, hvle.trans hc0le, ?_⟩
    rcases le_or_gt 0 I.ξmax with hx | hx
    · calc v k' t * I.ξmax ≤ c0 * I.ξmax := mul_le_mul_of_nonneg_right hvle hx
        _ ≤ 1 := hc0ξ
    · nlinarith
  have hvint : ∀ k' : ℕ, 1 ≤ k' → IntervalIntegrable (v k') volume 0 1 := by
    intro k' _
    exact intervalIntegrable_const
  refine ⟨ρ, ρhat * ρ' * Real.exp 1 / c0, hρ, by positivity, ?_⟩
  intro k hk s sel hsel
  have hmain := h53 k hk s v hvprop hvint sel hsel
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hmax : max 1 (k : ℝ) = k := max_eq_right hk1
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hssq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  set a : ℝ := c0 * Real.sqrt k with ha
  have hapos : 0 < a := by positivity
  set f : ℝ → ℝ := fun t => min 1 (ρ' * s.F k (v k t) t) with hf
  set h : ℝ → ℝ := fun t => ρ' * Real.exp 1 * Real.exp (a * t + -a) with hh
  have hhint : IntervalIntegrable h volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hhval : ∫ t in (0 : ℝ)..1, h t = ρ' * Real.exp 1 * (a⁻¹ * (1 - Real.exp (-a))) := by
    simp only [hh]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add (fun x => Real.exp x) hapos.ne', integral_exp]
    simp
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ h t := by
    intro t ht
    have hG := CorAux.G_le s t ht.2
    have hvk : v k t = c0 / Real.sqrt k := by simp only [hv, hmax]
    have e1 : (k : ℝ) * v k t ^ 2 = c0 ^ 2 := by
      rw [hvk, div_pow, Real.sq_sqrt hk0.le]; field_simp
    have e2 : (k : ℝ) * v k t = a := by
      rw [hvk, ha]
      field_simp
      nlinarith
    have hexp : (k : ℝ) * v k t ^ 2 * s.G t - (k : ℝ) * v k t * (1 - t) ≤ 1 + (a * t + -a) := by
      rw [e1, e2]
      have : c0 ^ 2 * s.G t ≤ c0 ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (hG.trans ht.2) (sq_nonneg _)
      have : c0 ^ 2 ≤ 1 := by nlinarith
      nlinarith
    calc f t ≤ ρ' * s.F k (v k t) t := min_le_right _ _
      _ ≤ ρ' * Real.exp (1 + (a * t + -a)) := by
          apply mul_le_mul_of_nonneg_left _ hρ'.le
          unfold Schedule.F
          exact Real.exp_le_exp.mpr hexp
      _ = h t := by simp only [hh]; rw [Real.exp_add]; ring
  have hfh : ∫ t in (0 : ℝ)..1, f t ≤ ∫ t in (0 : ℝ)..1, h t := by
    by_cases hfint : IntervalIntegrable f volume 0 1
    · exact intervalIntegral.integral_mono_on (by norm_num) hfint hhint hpt
    · rw [intervalIntegral.integral_undef hfint, hhval]
      have : 0 ≤ 1 - Real.exp (-a) := by
        have : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      positivity
  have hkint : (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤ ρ' * Real.exp 1 / c0 * Real.sqrt k := by
    calc (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤ (k : ℝ) * ∫ t in (0 : ℝ)..1, h t :=
          mul_le_mul_of_nonneg_left hfh hk0.le
      _ = (k : ℝ) * (ρ' * Real.exp 1 * (a⁻¹ * (1 - Real.exp (-a)))) := by rw [hhval]
      _ ≤ (k : ℝ) * (ρ' * Real.exp 1 * (a⁻¹ * 1)) := by
          apply mul_le_mul_of_nonneg_left _ hk0.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [Real.exp_pos (-a)]
      _ = ρ' * Real.exp 1 / c0 * Real.sqrt k := by
          rw [ha]; field_simp; nlinarith
  have : ρhat * (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤
      ρhat * ρ' * Real.exp 1 / c0 * Real.sqrt k := by
    rw [mul_assoc]
    calc ρhat * ((k : ℝ) * ∫ t in (0 : ℝ)..1, f t)
        ≤ ρhat * (ρ' * Real.exp 1 / c0 * Real.sqrt k) := mul_le_mul_of_nonneg_left hkint hρhat.le
      _ = ρhat * ρ' * Real.exp 1 / c0 * Real.sqrt k := by ring
  linarith
