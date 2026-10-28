-- Prove2me | solution 1 for DataDrivenRO.KS.var_le_worst_case_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:04.587484+00:00
-- url     : https://prove2.me/submissions/e8294210-ac79-4015-a49d-8767abbd8fc9

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

-- carved verbatim out of submission 69bb39be-babe-4de8-bc95-b3c6c4a93315, lines 1403-1440

section
set_option autoImplicit false
open MeasureTheory
open DataDrivenRO
open DataDrivenRO.KS

noncomputable def qLn (N : ℕ) (Γ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then Γ
  else if j ≤ ⌊(N : ℝ) * (1 - Γ)⌋₊ then 1 / N
  else if j = ⌊(N : ℝ) * (1 - Γ)⌋₊ + 1 then 1 - Γ - (⌊(N : ℝ) * (1 - Γ)⌋₊ : ℝ) / N
  else 0

lemma qLn_partial (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), qLn N Γ j = min (Γ + (n : ℝ) / N) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set m := ⌊(N : ℝ) * (1 - Γ)⌋₊ with hm
  have hm1 : (m : ℝ) ≤ N * (1 - Γ) := Nat.floor_le (by nlinarith)
  have hm2 : (N : ℝ) * (1 - Γ) < m + 1 := Nat.lt_floor_add_one _
  -- facts: k ≤ m → k/N ≤ 1 - Γ ; k ≥ m+1 → k/N > 1 - Γ
  have hle : ∀ k : ℕ, k ≤ m → Γ + (k : ℝ) / N ≤ 1 := by
    intro k hk
    have : (k : ℝ) ≤ m := by exact_mod_cast hk
    have : (k : ℝ) / N ≤ 1 - Γ := by rw [div_le_iff₀ hNr]; linarith
    linarith
  have hgt : ∀ k : ℕ, m + 1 ≤ k → 1 < Γ + (k : ℝ) / N := by
    intro k hk
    have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have : 1 - Γ < (k : ℝ) / N := by rw [lt_div_iff₀ hNr]; linarith
    linarith
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, qLn, if_true, Nat.cast_zero,
      zero_div, add_zero]
    rw [min_eq_left hΓ1.le]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h1 : n + 1 ≤ m
    · have hq : qLn N Γ (n + 1) = 1 / N := by
        simp only [qLn]; rw [if_neg (by omega), if_pos h1]
      rw [hq, min_eq_left (hle n (by omega)), min_eq_left (hle (n + 1) h1)]
      push_cast; ring
    · by_cases h2 : n + 1 = m + 1
      · have hq : qLn N Γ (n + 1) = 1 - Γ - (m : ℝ) / N := by
          simp only [qLn]; rw [if_neg (by omega), if_neg h1, if_pos h2]
        have hnm : (n : ℝ) = m := by
          have : n = m := by omega
          rw [this]
        rw [hq, min_eq_left (hle n (by omega)), min_eq_right (hgt (n + 1) (by omega)).le, hnm]
        ring
      · have hq : qLn N Γ (n + 1) = 0 := by
          simp only [qLn]; rw [if_neg (by omega), if_neg h1, if_neg h2]
        rw [hq, min_eq_right (hgt n (by omega)).le, min_eq_right (hgt (n + 1) (by omega)).le]
        ring

lemma abel_sum (p w : ℕ → ℝ) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), p j * w j =
      w M * ∑ j ∈ Finset.range (M + 1), p j
        - ∑ k ∈ Finset.range M, (w (k + 1) - w k) * ∑ j ∈ Finset.range (k + 1), p j := by
  induction M with
  | zero => simp [mul_comm]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (w (k + 1) - w k) *
      ∑ j ∈ Finset.range (k + 1), p j) M, Finset.sum_range_succ p (M + 1)]
    ring

lemma abel_qL (N : ℕ) (hN : 0 < N) (Γ : ℝ) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (w : ℕ → ℝ) :
    ∑ j ∈ Finset.range (N + 2), qLn N Γ j * w j =
      w (N + 1) + ∑ k ∈ Finset.range (N + 1), (w k - w (k + 1)) * min (Γ + (k : ℝ) / N) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have := abel_sum (qLn N Γ) w (N + 1)
  simp only [qLn_partial N hN Γ hΓ0 hΓ1] at this
  rw [show N + 1 + 1 = N + 2 from rfl] at this
  rw [this]
  have hone : min (Γ + ((N + 1 : ℕ) : ℝ) / N) 1 = 1 := by
    apply min_eq_right
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / N := by
      rw [le_div_iff₀ hNr]; push_cast; linarith
    linarith
  rw [hone, mul_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro k _; ring

lemma pw_anti (u : ℕ → ℝ) (hu : Monotone u) (g : ℝ → ℝ) (hg : Antitone g) :
    ∀ (M : ℕ) (x : ℝ), u 0 ≤ x → x ≤ u M →
      g x ≤ g (u M) + ∑ k ∈ Finset.range M,
        (g (u k) - g (u (k + 1))) * (if x < u (k + 1) then (1 : ℝ) else 0) := by
  intro M
  induction M with
  | zero =>
    intro x h0 h1
    have : x = u 0 := le_antisymm h1 h0
    simp [this]
  | succ M ih =>
    intro x h0 h1
    rw [Finset.sum_range_succ]
    by_cases hx : u M < x
    · have hz : ∀ k ∈ Finset.range M, (g (u k) - g (u (k + 1))) *
          (if x < u (k + 1) then (1 : ℝ) else 0) = 0 := by
        intro k hk
        have : u (k + 1) ≤ u M := hu (by simpa using hk)
        rw [if_neg (by linarith), mul_zero]
      rw [Finset.sum_eq_zero hz, zero_add]
      by_cases hlt : x < u (M + 1)
      · rw [if_pos hlt, mul_one]
        have := hg hx.le
        linarith
      · rw [if_neg hlt, mul_zero, add_zero]
        have : x = u (M + 1) := le_antisymm h1 (not_lt.1 hlt)
        rw [this]
    · have hxM : x ≤ u M := not_lt.1 hx
      have ih' := ih x h0 hxM
      by_cases hlt : x < u (M + 1)
      · rw [if_pos hlt, mul_one]
        linarith
      · have hle : u (M + 1) ≤ x := not_lt.1 hlt
        have heq : u M = u (M + 1) := le_antisymm (hu (Nat.le_succ M)) (le_trans hle hxM)
        rw [if_neg hlt, mul_zero, add_zero, ← heq]
        linarith

lemma pw_mono (u : ℕ → ℝ) (hu : Monotone u) (g : ℝ → ℝ) (hg : Monotone g) :
    ∀ (M : ℕ) (x : ℝ), u 0 ≤ x → x ≤ u M →
      g x ≤ g (u 0) + ∑ k ∈ Finset.range M,
        (g (u (k + 1)) - g (u k)) * (if u k < x then (1 : ℝ) else 0) := by
  intro M
  induction M with
  | zero =>
    intro x h0 h1
    have : x = u 0 := le_antisymm h1 h0
    simp [this]
  | succ M ih =>
    intro x h0 h1
    rw [Finset.sum_range_succ]
    by_cases hx : u M < x
    · have hall : ∀ k ∈ Finset.range (M + 1), (g (u (k + 1)) - g (u k)) *
          (if u k < x then (1 : ℝ) else 0) = g (u (k + 1)) - g (u k) := by
        intro k hk
        have : u k ≤ u M := hu (by simpa [Nat.lt_succ_iff] using hk)
        rw [if_pos (by linarith), mul_one]
      have hs := Finset.sum_congr rfl hall
      rw [Finset.sum_range_succ] at hs
      rw [hs, Finset.sum_range_sub (fun k => g (u k))]
      · have := hg h1
        linarith
    · have hxM : x ≤ u M := not_lt.1 hx
      have ih' := ih x h0 hxM
      rw [if_neg hx, mul_zero, add_zero]
      exact ih'

lemma int_le_step {Q : Measure ℝ} [IsProbabilityMeasure Q] (g : ℝ → ℝ) (hgm : Measurable g)
    (a b C : ℝ) (hsupp : Q (Set.Icc a b)ᶜ = 0) (hbd : ∀ x ∈ Set.Icc a b, |g x| ≤ C)
    (c : ℝ) (s : ℕ → Set ℝ) (hs : ∀ k, MeasurableSet (s k)) (coef : ℕ → ℝ) (M : ℕ)
    (hle : ∀ x ∈ Set.Icc a b, g x ≤ c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) :
    ∫ x, g x ∂Q ≤ c + ∑ k ∈ Finset.range M, coef k * Q.real (s k) := by
  have hae : ∀ᵐ x ∂Q, x ∈ Set.Icc a b := mem_ae_iff.mpr hsupp
  have hint : Integrable g Q := by
    refine Integrable.of_bound hgm.aestronglyMeasurable C ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]; exact hbd x hx
  have hind : ∀ k, Integrable (fun x => coef k * (s k).indicator (1 : ℝ → ℝ) x) Q := by
    intro k
    have : Integrable ((s k).indicator (1 : ℝ → ℝ)) Q :=
      (integrable_const (1 : ℝ)).indicator (hs k)
    exact this.const_mul _
  have hrint : Integrable (fun x => c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) Q :=
    (integrable_const c).add (integrable_finset_sum _ (fun k _ => hind k))
  have h1 : ∫ x, g x ∂Q ≤ ∫ x, (c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) ∂Q := by
    apply integral_mono_ae hint hrint
    filter_upwards [hae] with x hx
    exact hle x hx
  have h2 : ∫ x, (c + ∑ k ∈ Finset.range M, coef k * (s k).indicator (1 : ℝ → ℝ) x) ∂Q
      = c + ∑ k ∈ Finset.range M, coef k * Q.real (s k) := by
    rw [integral_add (integrable_const c) (integrable_finset_sum _ (fun k _ => hind k))]
    rw [integral_finset_sum _ (fun k _ => hind k)]
    simp only [integral_const, probReal_univ, one_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, integral_indicator_one (hs k)]
  linarith

noncomputable def uSeq {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (i : Fin d) (k : ℕ) : ℝ :=
  uhat i ⟨min k (N + 1), by omega⟩

lemma uSeq_of_lt {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (i : Fin d) {k : ℕ} (hk : k < N + 2) :
    uSeq uhat i k = uhat i ⟨k, hk⟩ := by
  unfold uSeq
  congr 1
  apply Fin.ext
  simp only
  omega

lemma uSeq_mono {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (hmono : ∀ i, Monotone (uhat i))
    (i : Fin d) : Monotone (uSeq uhat i) := by
  intro a b hab
  exact hmono i (Fin.mk_le_mk.2 (min_le_min_right _ hab))

lemma ind_Iio (a x : ℝ) : (Set.Iio a).indicator (1 : ℝ → ℝ) x = if x < a then 1 else 0 := by
  simp [Set.indicator_apply]

lemma ind_Ioi (a x : ℝ) : (Set.Ioi a).indicator (1 : ℝ → ℝ) x = if a < x then 1 else 0 := by
  simp [Set.indicator_apply]

lemma real_Iio_le {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hcons : ∀ j : Fin N, Q (Set.Iio (uhat i (obsIdx j))) ≤ ENNReal.ofReal ((j : ℝ) / N + Γ))
    (k : ℕ) (hk : k ≤ N) (hN : 0 < N) (hΓ0 : 0 < Γ) :
    Q.real (Set.Iio (uSeq uhat i (k + 1))) ≤ min (Γ + (k : ℝ) / N) 1 := by
  apply le_min
  · rcases Nat.lt_or_ge k N with hlt | hge
    · have h := hcons ⟨k, hlt⟩
      have e : uSeq uhat i (k + 1) = uhat i (obsIdx (⟨k, hlt⟩ : Fin N)) :=
        uSeq_of_lt uhat i (by omega)
      rw [e]
      have : (0 : ℝ) ≤ (k : ℝ) / N + Γ := by positivity
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rw [ENNReal.toReal_ofReal this] at h2
      simp only [measureReal_def]
      linarith
    · have hkN : k = N := le_antisymm hk hge
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have : (k : ℝ) / N = 1 := by rw [hkN]; exact div_self hNr.ne'
      have h1 : Q.real (Set.Iio (uSeq uhat i (k + 1))) ≤ 1 := by
        have := measureReal_le_one (μ := Q) (s := Set.Iio (uSeq uhat i (k + 1)))
        exact this
      linarith
  · exact measureReal_le_one

lemma real_Ioi_le {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hcons : ∀ j : Fin N, ENNReal.ofReal (((j : ℝ) + 1) / N - Γ) ≤ Q (Set.Iic (uhat i (obsIdx j))))
    (m : ℕ) (hm : m ≤ N) (hN : 0 < N) (hΓ0 : 0 < Γ) :
    Q.real (Set.Ioi (uSeq uhat i m)) ≤ min (Γ + ((N - m : ℕ) : ℝ) / N) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_min
  · have h1 : Q.real (Set.Ioi (uSeq uhat i m)) ≤ 1 := measureReal_le_one
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · have : ((N - m : ℕ) : ℝ) / N = 1 := by
        rw [h0, Nat.sub_zero]; exact div_self hNr.ne'
      linarith
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hj : j < N := by omega
      have h := hcons ⟨j, hj⟩
      have e : uSeq uhat i (j + 1) = uhat i (obsIdx (⟨j, hj⟩ : Fin N)) :=
        uSeq_of_lt uhat i (by omega)
      rw [e] at *
      have h2 := ENNReal.toReal_mono (measure_ne_top Q _) h
      rw [ENNReal.toReal_ofReal'] at h2
      have h3 : Q.real (Set.Ioi (uhat i (obsIdx (⟨j, hj⟩ : Fin N)))) =
          1 - Q.real (Set.Iic (uhat i (obsIdx (⟨j, hj⟩ : Fin N)))) := by
        rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
      rw [h3]
      have h4 : ((N - (j + 1) : ℕ) : ℝ) = (N : ℝ) - ((j : ℝ) + 1) := by
        rw [Nat.cast_sub hm]; push_cast; ring
      have h5 : ((N : ℝ) - ((j : ℝ) + 1)) / N = 1 - ((j : ℝ) + 1) / N := by
        field_simp
      rw [h4, h5]
      have h6 : ((j : ℝ) + 1) / N - Γ ≤ Q.real (Set.Iic (uhat i (obsIdx (⟨j, hj⟩ : Fin N)))) := by
        have := le_max_left (((j : ℝ) + 1) / N - Γ) 0
        simp only [measureReal_def]
        simp only at h2
        linarith
      linarith
  · exact measureReal_le_one

lemma sum_fin_qL {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d) (g : ℝ → ℝ) :
    ∑ j : Fin (N + 2), qL N Γ j * g (uhat i j) =
      ∑ j ∈ Finset.range (N + 2), qLn N Γ j * g (uSeq uhat i j) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => qLn N Γ j * g (uSeq uhat i j)) (N + 2)]
  apply Finset.sum_congr rfl
  intro j _
  rw [uSeq_of_lt uhat i j.isLt]
  rfl

lemma sum_fin_qR {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d) (g : ℝ → ℝ) :
    ∑ j : Fin (N + 2), qR N Γ j * g (uhat i j) =
      ∑ j ∈ Finset.range (N + 2), qLn N Γ j * g (uSeq uhat i (N + 1 - j)) := by
  have h1 : ∑ j : Fin (N + 2), qR N Γ j * g (uhat i j) =
      ∑ j : Fin (N + 2), qL N Γ j * g (uhat i (Fin.rev j)) := by
    rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N + 2)))
      (fun j => qL N Γ j * g (uhat i (Fin.rev j)))]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.revPerm_apply, Fin.rev_rev, qR]
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun j => qLn N Γ j * g (uSeq uhat i (N + 1 - j))) (N + 2)]
  apply Finset.sum_congr rfl
  intro j _
  have hlt : N + 1 - (j : ℕ) < N + 2 := by omega
  rw [uSeq_of_lt uhat i hlt]
  have : (Fin.rev j) = (⟨N + 1 - (j : ℕ), hlt⟩ : Fin (N + 2)) := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [this]
  rfl

theorem ec2_anti {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i)) (i : Fin d)
    (Q : Measure ℝ) (hQ : Q ∈ ksRegion uhat Γ i) (g : ℝ → ℝ) (hg : Antitone g) :
    ∫ x, g x ∂Q ≤ ∑ j, qL N Γ j * g (uhat i j) := by
  obtain ⟨hprob, hsupp, hcons⟩ := hQ
  haveI := hprob
  set u := uSeq uhat i with hu_def
  have hu : Monotone u := uSeq_mono uhat hmono i
  have e0 : u 0 = uhat i 0 := by rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have eN : u (N + 1) = uhat i (Fin.last (N + 1)) := by
    rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have hsupp' : Q (Set.Icc (u 0) (u (N + 1)))ᶜ = 0 := by rw [e0, eN]; exact hsupp
  have hbd : ∀ x ∈ Set.Icc (u 0) (u (N + 1)), |g x| ≤ |g (u 0)| + |g (u (N + 1))| := by
    intro x hx
    have h1 := hg hx.1
    have h2 := hg hx.2
    have := le_abs_self (g (u 0)); have := neg_abs_le (g (u 0))
    have := le_abs_self (g (u (N + 1))); have := neg_abs_le (g (u (N + 1)))
    have := abs_nonneg (g (u 0)); have := abs_nonneg (g (u (N + 1)))
    rw [abs_le]; constructor <;> linarith
  have step1 := int_le_step (Q := Q) g hg.measurable (u 0) (u (N + 1)) _ hsupp' hbd
    (g (u (N + 1))) (fun k => Set.Iio (u (k + 1))) (fun k => measurableSet_Iio)
    (fun k => g (u k) - g (u (k + 1))) (N + 1) (by
      intro x hx
      have := pw_anti u hu g hg (N + 1) x hx.1 hx.2
      simpa only [ind_Iio] using this)
  have hcons2 : ∀ j : Fin N, Q (Set.Iio (uhat i (obsIdx j))) ≤ ENNReal.ofReal ((j : ℝ) / N + Γ) :=
    fun j => (hcons j).2
  have step2 : ∑ k ∈ Finset.range (N + 1), (g (u k) - g (u (k + 1))) * Q.real (Set.Iio (u (k + 1)))
      ≤ ∑ k ∈ Finset.range (N + 1), (g (u k) - g (u (k + 1))) * min (Γ + (k : ℝ) / N) 1 := by
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left
    · exact real_Iio_le uhat Γ i Q hcons2 k (by simpa [Nat.lt_succ_iff] using hk) hN hΓ0
    · exact sub_nonneg.2 (hg (hu (Nat.le_succ k)))
  have step3 := abel_qL N hN Γ hΓ0 hΓ1 (fun j => g (u j))
  rw [sum_fin_qL uhat Γ i g]
  linarith

theorem ec2_mono {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i)) (i : Fin d)
    (Q : Measure ℝ) (hQ : Q ∈ ksRegion uhat Γ i) (g : ℝ → ℝ) (hg : Monotone g) :
    ∫ x, g x ∂Q ≤ ∑ j, qR N Γ j * g (uhat i j) := by
  obtain ⟨hprob, hsupp, hcons⟩ := hQ
  haveI := hprob
  set u := uSeq uhat i with hu_def
  have hu : Monotone u := uSeq_mono uhat hmono i
  have e0 : u 0 = uhat i 0 := by rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have eN : u (N + 1) = uhat i (Fin.last (N + 1)) := by
    rw [hu_def, uSeq_of_lt uhat i (by omega)]; rfl
  have hsupp' : Q (Set.Icc (u 0) (u (N + 1)))ᶜ = 0 := by rw [e0, eN]; exact hsupp
  have hbd : ∀ x ∈ Set.Icc (u 0) (u (N + 1)), |g x| ≤ |g (u 0)| + |g (u (N + 1))| := by
    intro x hx
    have h1 := hg hx.1
    have h2 := hg hx.2
    have := le_abs_self (g (u 0)); have := neg_abs_le (g (u 0))
    have := le_abs_self (g (u (N + 1))); have := neg_abs_le (g (u (N + 1)))
    have := abs_nonneg (g (u 0)); have := abs_nonneg (g (u (N + 1)))
    rw [abs_le]; constructor <;> linarith
  have step1 := int_le_step (Q := Q) g hg.measurable (u 0) (u (N + 1)) _ hsupp' hbd
    (g (u 0)) (fun k => Set.Ioi (u k)) (fun k => measurableSet_Ioi)
    (fun k => g (u (k + 1)) - g (u k)) (N + 1) (by
      intro x hx
      have := pw_mono u hu g hg (N + 1) x hx.1 hx.2
      simpa only [ind_Ioi] using this)
  have hcons1 : ∀ j : Fin N, ENNReal.ofReal (((j : ℝ) + 1) / N - Γ) ≤ Q (Set.Iic (uhat i (obsIdx j))) :=
    fun j => (hcons j).1
  have step2 : ∑ k ∈ Finset.range (N + 1), (g (u (k + 1)) - g (u k)) * Q.real (Set.Ioi (u k))
      ≤ ∑ k ∈ Finset.range (N + 1), (g (u (k + 1)) - g (u k)) *
          min (Γ + ((N - k : ℕ) : ℝ) / N) 1 := by
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left
    · exact real_Ioi_le uhat Γ i Q hcons1 k (by simpa [Nat.lt_succ_iff] using hk) hN hΓ0
    · exact sub_nonneg.2 (hg (hu (Nat.le_succ k)))
  have step3 := abel_qL N hN Γ hΓ0 hΓ1 (fun j => g (u (N + 1 - j)))
  simp only [Nat.sub_self] at step3
  have step4 : ∑ k ∈ Finset.range (N + 1), (g (u (N + 1 - k)) - g (u (N + 1 - (k + 1)))) *
        min (Γ + (k : ℝ) / N) 1
      = ∑ k ∈ Finset.range (N + 1), (g (u (k + 1)) - g (u k)) *
          min (Γ + ((N - k : ℕ) : ℝ) / N) 1 := by
    rw [← Finset.sum_range_reflect (fun k => (g (u (k + 1)) - g (u k)) *
          min (Γ + ((N - k : ℕ) : ℝ) / N) 1) (N + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ N := by simpa [Nat.lt_succ_iff] using hk
    have a1 : N + 1 - k = N + 1 - 1 - k + 1 := by omega
    have a2 : N + 1 - (k + 1) = N + 1 - 1 - k := by omega
    have a3 : N - (N + 1 - 1 - k) = k := by omega
    rw [a1, a2, a3]
  rw [sum_fin_qR uhat Γ i g]
  linarith

end

section
set_option autoImplicit false
open MeasureTheory

lemma integrable_exp_lin (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hsupp : ∃ a b : ℝ, Q (Set.Icc a b)ᶜ = 0) (c : ℝ) :
    Integrable (fun x => Real.exp (c * x)) Q := by
  obtain ⟨a, b, h⟩ := hsupp
  have hae : ∀ᵐ x ∂Q, x ∈ Set.Icc a b := mem_ae_iff.mpr h
  refine Integrable.of_bound (by fun_prop) (Real.exp (|c| * (|a| + |b|))) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hx' : |x| ≤ |a| + |b| := by
    rw [abs_le]; constructor
    · have := hx.1; have := neg_abs_le a; have := abs_nonneg b; linarith
    · have := hx.2; have := le_abs_self b; have := abs_nonneg a; linarith
  calc c * x ≤ |c * x| := le_abs_self _
    _ = |c| * |x| := abs_mul _ _
    _ ≤ |c| * (|a| + |b|) := mul_le_mul_of_nonneg_left hx' (abs_nonneg _)

theorem ns_bound {d : ℕ} (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)]
    (hsupp : ∀ i, ∃ a b : ℝ, Q i (Set.Icc a b)ᶜ = 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    DataDrivenRO.KS.VaR (Measure.pi Q) ε v ≤
      lam * Real.log (1 / ε) + lam * ∑ i, Real.log (∫ x, Real.exp (v i * x / lam) ∂(Q i)) := by
  set P := Measure.pi Q with hP
  set f : (Fin d → ℝ) → ℝ := fun u => u ⬝ᵥ v with hf
  set M : Fin d → ℝ := fun i => ∫ x, Real.exp (v i * x / lam) ∂(Q i) with hM
  have hint : ∀ i, Integrable (fun x => Real.exp (v i * x / lam)) (Q i) := by
    intro i
    have := integrable_exp_lin (Q i) (hsupp i) (v i / lam)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  have hMpos : ∀ i, 0 < M i := fun i => integral_exp_pos (hint i)
  set T := lam * Real.log (1 / ε) + lam * ∑ i, Real.log (M i) with hT
  have hfm : Measurable f := by
    simp only [hf]; fun_prop
  -- exp (f u / lam) = ∏ exp (v i * u i / lam)
  have hexp : ∀ u : Fin d → ℝ, Real.exp (f u / lam) = ∏ i, Real.exp (v i * u i / lam) := by
    intro u
    rw [← Real.exp_sum]
    congr 1
    simp only [hf, dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hEint : Integrable (fun u => Real.exp (f u / lam)) P := by
    have := Integrable.fintype_prod (μ := Q) (f := fun i x => Real.exp (v i * x / lam)) hint
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hexp]
  have hE : ∫ u, Real.exp (f u / lam) ∂P = ∏ i, M i := by
    simp_rw [hexp]
    exact integral_fintype_prod_eq_prod (fun i x => Real.exp (v i * x / lam))
  have hprodpos : 0 < ∏ i, M i := Finset.prod_pos fun i _ => hMpos i
  have hexpT : Real.exp (T / lam) = (1 / ε) * ∏ i, M i := by
    have : T / lam = Real.log (1 / ε) + ∑ i, Real.log (M i) := by
      rw [hT]; field_simp
    rw [this, Real.exp_add, Real.exp_log (by positivity), Real.exp_sum]
    congr 1
    exact Finset.prod_congr rfl fun i _ => Real.exp_log (hMpos i)
  -- Markov
  set S := {u | Real.exp (T / lam) ≤ Real.exp (f u / lam)} with hS
  have hmarkov : Real.exp (T / lam) * P.real S ≤ ∫ u, Real.exp (f u / lam) ∂P :=
    mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun u => (Real.exp_pos (f u / lam)).le) hEint (Real.exp (T / lam))
  rw [hE] at hmarkov
  have hbad : P.real S ≤ ε := by
    have h1 : (1 / ε) * ((∏ i, M i) * P.real S) ≤ ∏ i, M i := by
      rw [← mul_assoc, ← hexpT]; exact hmarkov
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hε0] at h1
    have h2 : (∏ i, M i) * (P.real S - ε) ≤ 0 := by nlinarith
    have := nonpos_of_mul_nonpos_right h2 hprodpos
    linarith
  have hsub : {u | T < f u} ⊆ S := by
    intro u hu
    simp only [hS, Set.mem_setOf_eq] at hu ⊢
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hu.le hlam.le)
  have hgt : P.real {u | T < f u} ≤ ε := (measureReal_mono hsub).trans hbad
  have hmem : ENNReal.ofReal (1 - ε) ≤ P {u | f u ≤ T} := by
    have hc : {u | f u ≤ T} = {u | T < f u}ᶜ := by
      ext u; simp
    have hms : MeasurableSet {u | T < f u} := measurableSet_lt measurable_const hfm
    have hr : P.real {u | f u ≤ T} = 1 - P.real {u | T < f u} := by
      rw [hc, probReal_compl_eq_one_sub hms]
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    change 1 - ε ≤ P.real {u | f u ≤ T}
    rw [hr]; linarith
  -- bounded below
  have hbdd : BddBelow {y : ℝ | ENNReal.ofReal (1 - ε) ≤ P {u | f u ≤ y}} := by
    have hten := tendsto_measure_iInter_atTop (μ := P) (s := fun n : ℕ => {u | f u ≤ -(n : ℝ)})
      (fun n => (measurableSet_le hfm measurable_const).nullMeasurableSet)
      (by
        intro m n hmn u hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith)
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {u : Fin d → ℝ | f u ≤ -(n : ℝ)}) = ∅ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-f u)
      exact ⟨n, by linarith⟩
    rw [hempty, measure_empty] at hten
    have hpos : (0 : ENNReal) < ENNReal.ofReal (1 - ε) := ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨n, hn⟩ := (hten.eventually (gt_mem_nhds hpos)).exists
    refine ⟨-(n : ℝ), fun y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    simp only [Set.mem_setOf_eq] at hy
    have : P {u | f u ≤ y} ≤ P {u | f u ≤ -(n : ℝ)} := by
      apply measure_mono
      intro u hu
      simp only [Set.mem_setOf_eq] at hu ⊢
      linarith
    exact absurd (hy.trans this) (not_le.mpr hn)
  have hVaR : DataDrivenRO.KS.VaR P ε v ≤ T := by
    unfold DataDrivenRO.KS.VaR MultistageStochastic.valueAtRisk
    exact csInf_le hbdd hmem
  exact hVaR

end

section
set_option autoImplicit false
open MeasureTheory
open DataDrivenRO
open DataDrivenRO.KS

theorem solution {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ productRegion uhat Γ) (v : Fin d → ℝ)
    (lam : ℝ) (hlam : 0 < lam) :
    VaR P ε v ≤ boundKS uhat Γ ε v lam := by
  obtain ⟨Q, hprob, hQ, rfl⟩ := hP
  haveI : ∀ i, IsProbabilityMeasure (Q i) := hprob
  have hsupp : ∀ i, ∃ a b : ℝ, Q i (Set.Icc a b)ᶜ = 0 := fun i => ⟨_, _, (hQ i).2.1⟩
  have h1 := ns_bound Q hsupp ε hε0 hε1 v lam hlam
  have hint : ∀ i, Integrable (fun x => Real.exp (v i * x / lam)) (Q i) := by
    intro i
    have := integrable_exp_lin (Q i) (hsupp i) (v i / lam)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  have hEC : ∀ i, ∫ x, Real.exp (v i * x / lam) ∂(Q i) ≤ max
      (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
      (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam)) := by
    intro i
    rcases le_total 0 (v i) with h | h
    · have hg : Monotone (fun x : ℝ => Real.exp (v i * x / lam)) := fun a b hab =>
        Real.exp_le_exp.2 (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab h) hlam.le)
      exact (ec2_mono uhat Γ hN hΓ0 hΓ1 hmono i (Q i) (hQ i) _ hg).trans (le_max_right _ _)
    · have hg : Antitone (fun x : ℝ => Real.exp (v i * x / lam)) := fun a b hab =>
        Real.exp_le_exp.2 (div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hab h) hlam.le)
      exact (ec2_anti uhat Γ hN hΓ0 hΓ1 hmono i (Q i) (hQ i) _ hg).trans (le_max_left _ _)
  have hpos : ∀ i, 0 < ∫ x, Real.exp (v i * x / lam) ∂(Q i) := fun i => integral_exp_pos (hint i)
  have h2 : ∑ i, Real.log (∫ x, Real.exp (v i * x / lam) ∂(Q i)) ≤ ∑ i, Real.log (max
      (∑ j, qL N Γ j * Real.exp (v i * uhat i j / lam))
      (∑ j, qR N Γ j * Real.exp (v i * uhat i j / lam))) :=
    Finset.sum_le_sum (fun i _ => Real.log_le_log (hpos i) (hEC i))
  have h3 := mul_le_mul_of_nonneg_left h2 hlam.le
  unfold boundKS
  linarith

end
