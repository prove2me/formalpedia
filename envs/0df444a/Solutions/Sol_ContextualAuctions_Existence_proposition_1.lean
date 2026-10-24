-- Prove2me | solution 1 for ContextualAuctions.Existence.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T07:12:07.30827+00:00
-- url     : https://prove2.me/submissions/43e2dc73-b703-443a-a9f7-8ca717ad6ed0

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Theorems.Thm_ContextualAuctions_Existence_lemma_1

open MeasureTheory

namespace L1Aux

variable (k : ℕ) (r : ℝ) (Fr : ℝ → ℝ)

noncomputable def Hk (x : ℝ) : ℝ := Fr x ^ k
noncomputable def Ik (x : ℝ) : ℝ := ∫ s in r..x, Hk k Fr s
noncomputable def sig (x : ℝ) : ℝ :=
  if x < r then x else if Hk k Fr x = 0 then 0 else x - Ik k r Fr x / Hk k Fr x

variable {r Fr}

lemma Hk_mono (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) : Monotone (Hk k Fr) :=
  fun _ _ hab => pow_le_pow_left₀ (hnn _) (hmono hab) k

lemma Hk_nn (hnn : ∀ x, 0 ≤ Fr x) (x : ℝ) : 0 ≤ Hk k Fr x := pow_nonneg (hnn x) k

lemma Hk_ii (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) (a b : ℝ) :
    IntervalIntegrable (Hk k Fr) volume a b :=
  (Hk_mono k hmono hnn).intervalIntegrable

/-- `∫_a^b H ≥ (b - a) H(a)` and `≤ (b - a) H(b)` for `a ≤ b`. -/
lemma int_bounds (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * Hk k Fr a ≤ ∫ s in a..b, Hk k Fr s ∧ ∫ s in a..b, Hk k Fr s ≤ (b - a) * Hk k Fr b := by
  constructor
  · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const (Hk_ii k hmono hnn a b)
      (fun s hs => Hk_mono k hmono hnn hs.1)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hab (Hk_ii k hmono hnn a b) intervalIntegrable_const
      (fun s hs => Hk_mono k hmono hnn hs.2)
    simpa [mul_comm] using this

lemma Ik_nn (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) {x : ℝ} (hx : r ≤ x) : 0 ≤ Ik k r Fr x :=
  le_trans (mul_nonneg (by linarith) (Hk_nn k hnn r)) (int_bounds k hmono hnn hx).1

lemma Ik_le (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) {x : ℝ} (hx : r ≤ x) :
    Ik k r Fr x ≤ (x - r) * Hk k Fr x := (int_bounds k hmono hnn hx).2

/-- key identity-inequality: `H(z) (v - σ(z)) ≤ I(v)` -/
lemma key_ineq (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) {z : ℝ} (hz : r ≤ z)
    (hHz : Hk k Fr z ≠ 0) (v : ℝ) :
    Hk k Fr z * (v - sig k r Fr z) ≤ Ik k r Fr v := by
  have hzs : sig k r Fr z = z - Ik k r Fr z / Hk k Fr z := by
    unfold sig; rw [if_neg (not_lt.mpr hz), if_neg hHz]
  rw [hzs]
  have e : Hk k Fr z * (v - (z - Ik k r Fr z / Hk k Fr z)) =
      Hk k Fr z * (v - z) + Ik k r Fr z := by
    field_simp
    ring
  rw [e]
  have hsplit : Ik k r Fr v = Ik k r Fr z + ∫ s in z..v, Hk k Fr s := by
    unfold Ik
    rw [intervalIntegral.integral_add_adjacent_intervals (Hk_ii k hmono hnn _ _)
      (Hk_ii k hmono hnn _ _)]
  rw [hsplit]
  rcases le_total z v with hzv | hvz
  · have := (int_bounds k hmono hnn hzv).1
    linarith
  · have := (int_bounds k hmono hnn hvz).2
    rw [intervalIntegral.integral_symm]
    nlinarith

lemma sig_ge_r (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) {x : ℝ} (hx : r ≤ x)
    (hH : Hk k Fr x ≠ 0) : r ≤ sig k r Fr x := by
  unfold sig
  rw [if_neg (not_lt.mpr hx), if_neg hH]
  have hpos : 0 < Hk k Fr x := lt_of_le_of_ne (Hk_nn k hnn x) (Ne.symm hH)
  have := Ik_le k hmono hnn hx
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hpos]
  linarith

lemma sig_le_self (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) {x : ℝ} (hx : r ≤ x)
    (hH : Hk k Fr x ≠ 0) : sig k r Fr x ≤ x := by
  unfold sig
  rw [if_neg (not_lt.mpr hx), if_neg hH]
  have hpos : 0 < Hk k Fr x := lt_of_le_of_ne (Hk_nn k hnn x) (Ne.symm hH)
  have := Ik_nn k hmono hnn hx
  have : 0 ≤ Ik k r Fr x / Hk k Fr x := div_nonneg this hpos.le
  linarith

lemma sig_nonneg (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) (hneg : ∀ x < 0, Fr x = 0)
    (hk : 1 ≤ k) {x : ℝ} (hx : r ≤ x) : 0 ≤ sig k r Fr x := by
  by_cases hH : Hk k Fr x = 0
  · unfold sig; rw [if_neg (not_lt.mpr hx), if_pos hH]
  have hpos : 0 < Hk k Fr x := lt_of_le_of_ne (Hk_nn k hnn x) (Ne.symm hH)
  have hx0 : 0 ≤ x := by
    by_contra h
    push Not at h
    apply hH
    unfold Hk
    rw [hneg x h]
    exact zero_pow (by omega)
  rcases le_or_gt 0 r with hr | hr
  · exact le_trans hr (sig_ge_r k hmono hnn hx hH)
  · -- r < 0: the integral over [r,0] vanishes
    have hz : ∫ s in r..0, Hk k Fr s = 0 := by
      apply intervalIntegral.integral_zero_ae
      have : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [this] with s hs hsI
      rw [Set.uIoc_of_le hr.le] at hsI
      have : s < 0 := lt_of_le_of_ne hsI.2 hs
      unfold Hk
      rw [hneg s this]
      exact zero_pow (by omega)
    have hsplit : Ik k r Fr x = ∫ s in (0 : ℝ)..x, Hk k Fr s := by
      unfold Ik
      rw [← intervalIntegral.integral_add_adjacent_intervals (Hk_ii k hmono hnn r 0)
        (Hk_ii k hmono hnn 0 x), hz, zero_add]
    have hb := (int_bounds k hmono hnn hx0).2
    unfold sig
    rw [if_neg (not_lt.mpr hx), if_neg hH, sub_nonneg, div_le_iff₀ hpos, hsplit]
    linarith

lemma sig_mono (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) (hneg : ∀ x < 0, Fr x = 0)
    (hk : 1 ≤ k) {x₁ x₂ : ℝ} (h1 : r ≤ x₁) (h12 : x₁ ≤ x₂) :
    sig k r Fr x₁ ≤ sig k r Fr x₂ := by
  have h2 : r ≤ x₂ := le_trans h1 h12
  by_cases hH1 : Hk k Fr x₁ = 0
  · have : sig k r Fr x₁ = 0 := by unfold sig; rw [if_neg (not_lt.mpr h1), if_pos hH1]
    rw [this]
    exact sig_nonneg k hmono hnn hneg hk h2
  have hp1 : 0 < Hk k Fr x₁ := lt_of_le_of_ne (Hk_nn k hnn _) (Ne.symm hH1)
  have hle : Hk k Fr x₁ ≤ Hk k Fr x₂ := Hk_mono k hmono hnn h12
  have hp2 : 0 < Hk k Fr x₂ := lt_of_lt_of_le hp1 hle
  have hH2 : Hk k Fr x₂ ≠ 0 := ne_of_gt hp2
  unfold sig
  rw [if_neg (not_lt.mpr h1), if_neg hH1, if_neg (not_lt.mpr h2), if_neg hH2]
  have hsplit : Ik k r Fr x₂ = Ik k r Fr x₁ + ∫ s in x₁..x₂, Hk k Fr s := by
    unfold Ik
    rw [intervalIntegral.integral_add_adjacent_intervals (Hk_ii k hmono hnn _ _)
      (Hk_ii k hmono hnn _ _)]
  have hb := (int_bounds k hmono hnn h12).2
  have hI1 := Ik_nn k hmono hnn h1
  -- I₂/H₂ ≤ I₁/H₂ + (x₂ - x₁) ≤ I₁/H₁ + (x₂ - x₁)
  have step1 : Ik k r Fr x₂ / Hk k Fr x₂ ≤ Ik k r Fr x₁ / Hk k Fr x₂ + (x₂ - x₁) := by
    rw [div_add' _ _ _ hH2, div_le_div_iff_of_pos_right hp2, hsplit]
    linarith
  have step2 : Ik k r Fr x₁ / Hk k Fr x₂ ≤ Ik k r Fr x₁ / Hk k Fr x₁ :=
    div_le_div_of_nonneg_left hI1 hp1 hle
  linarith

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Ω → ℝ)

/-- distribution function of `X` -/
noncomputable def Fd (x : ℝ) : ℝ := (ν {ω | X ω ≤ x}).toReal

variable {ν X}

lemma Fd_mono : Monotone (Fd ν X) := fun a b hab =>
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω (h : X ω ≤ a) => le_trans h hab)

lemma Fd_nn (x : ℝ) : 0 ≤ Fd ν X x := ENNReal.toReal_nonneg

lemma Fd_neg (hX0 : ν {ω | X ω < 0} = 0) : ∀ x < 0, Fd ν X x = 0 := by
  intro x hx
  unfold Fd
  have : ν {ω | X ω ≤ x} = 0 :=
    measure_mono_null (fun ω (h : X ω ≤ x) => (show X ω < 0 by linarith)) hX0
  simp [this]

lemma Fd_le_one (x : ℝ) : Fd ν X x ≤ 1 := by
  unfold Fd
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma M1 (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hX0 : ν {ω | X ω < 0} = 0) {z : ℝ} (hz : r ≤ z)
    (hH : Hk k (Fd ν X) z ≠ 0) :
    Fd ν X z ≤ (ν {ω | sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) z}).toReal := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω (hω : X ω ≤ z)
  show sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) z
  by_cases hlt : X ω < r
  · have : sig k r (Fd ν X) (X ω) = X ω := by unfold sig; rw [if_pos hlt]
    rw [this]
    exact le_trans hlt.le (sig_ge_r k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hz hH)
  · exact sig_mono k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) (Fd_neg (ν := ν) (X := X) hX0) hk (not_lt.mp hlt) hω

lemma tendsto_Fd_top :
    Filter.Tendsto (fun n : ℕ => Fd ν X n) Filter.atTop (nhds 1) := by
  have hmono : Monotone (fun n : ℕ => {ω | X ω ≤ (n : ℝ)}) := fun a b hab ω (h : X ω ≤ a) =>
    le_trans h (by exact_mod_cast hab)
  have hU : (⋃ n : ℕ, {ω | X ω ≤ (n : ℝ)}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (X ω)
    exact ⟨n, hn⟩
  have := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU, measure_univ] at this
  have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
  exact h2

lemma tendsto_Fd_left (s : ℝ) :
    Filter.Tendsto (fun n : ℕ => Fd ν X (s - 1 / ((n : ℝ) + 1))) Filter.atTop
      (nhds (ν {ω | X ω < s}).toReal) := by
  have hmono : Monotone (fun n : ℕ => {ω | X ω ≤ s - 1 / ((n : ℝ) + 1)}) := by
    intro a b hab ω (h : X ω ≤ s - 1 / ((a : ℝ) + 1))
    show X ω ≤ s - 1 / ((b : ℝ) + 1)
    have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hab 1
    linarith
  have hU : (⋃ n : ℕ, {ω | X ω ≤ s - 1 / ((n : ℝ) + 1)}) = {ω | X ω < s} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
  have := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU] at this
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this

lemma M2 (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hX0 : ν {ω | X ω < 0} = 0) (y κ : ℝ) (hκ : 0 ≤ κ)
    (hlt : κ < (ν {ω | sig k r (Fd ν X) (X ω) ≤ y}).toReal ^ k) :
    ∃ x, (x < r ∨ (r ≤ x ∧ sig k r (Fd ν X) x ≤ y)) ∧ κ < Fd ν X x ^ k := by
  set D := {x : ℝ | x < r ∨ (r ≤ x ∧ sig k r (Fd ν X) x ≤ y)} with hD_def
  have hdown : ∀ x ∈ D, ∀ x', x' ≤ x → x' ∈ D := by
    intro x hx x' hx'
    by_cases h' : x' < r
    · exact Or.inl h'
    · right
      refine ⟨not_lt.mp h', ?_⟩
      rcases hx with hx | ⟨hxr, hxy⟩
      · exact absurd (lt_of_le_of_lt hx' hx) h'
      · exact le_trans (sig_mono k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) (Fd_neg (ν := ν) (X := X) hX0) hk (not_lt.mp h') hx') hxy
  have hsub : {ω | sig k r (Fd ν X) (X ω) ≤ y} ⊆ X ⁻¹' D := by
    intro ω (h : sig k r (Fd ν X) (X ω) ≤ y)
    by_cases h' : X ω < r
    · exact Or.inl h'
    · exact Or.inr ⟨not_lt.mp h', h⟩
  set q := (ν {ω | sig k r (Fd ν X) (X ω) ≤ y}).toReal with hq
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ x ∈ D, Fd ν X x ^ k ≤ κ := fun x hx => hcon x hx
  -- find L ≥ q with L^k ≤ κ
  have hpowmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → a ^ k ≤ b ^ k := fun a b ha hab =>
    pow_le_pow_left₀ ha hab k
  by_cases hbdd : BddAbove D
  · by_cases hne : D.Nonempty
    · set s := sSup D
      by_cases hs : s ∈ D
      · have : q ≤ Fd ν X s := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          apply measure_mono
          intro ω hω
          exact le_csSup hbdd (hsub hω)
        linarith [hpowmono q _ hq0 this, hcon' s hs]
      · have hlim := tendsto_Fd_left (ν := ν) (X := X) s
        have hle : (ν {ω | X ω < s}).toReal ^ k ≤ κ := by
          have h2 := (hlim.pow k)
          apply le_of_tendsto' h2
          intro n
          apply hcon'
          have : s - 1 / ((n : ℝ) + 1) < s := by
            have : 0 < 1 / ((n : ℝ) + 1) := by positivity
            linarith
          obtain ⟨d, hd, hdlt⟩ := exists_lt_of_lt_csSup hne this
          exact hdown d hd _ hdlt.le
        have : q ≤ (ν {ω | X ω < s}).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          apply measure_mono
          intro ω hω
          have h1 := le_csSup hbdd (hsub hω)
          exact lt_of_le_of_ne h1 (fun heq => hs (by
            have h' : s = X ω := heq.symm
            rw [h']; exact hsub hω))
        linarith [hpowmono q _ hq0 this]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have : q = 0 := by
        rw [hq]
        have : ν {ω | sig k r (Fd ν X) (X ω) ≤ y} = 0 :=
          measure_mono_null (hsub.trans (by rw [hne]; simp)) measure_empty
        simp [this]
      rw [this, zero_pow (by omega)] at hlt
      linarith
  · have hall : ∀ x, x ∈ D := by
      intro x
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨d, hd, hxd⟩ := hbdd x
      exact hdown d hd x hxd.le
    have h1 : (1 : ℝ) ≤ κ := by
      have h2 := (tendsto_Fd_top (ν := ν) (X := X)).pow k
      rw [one_pow] at h2
      exact le_of_tendsto' h2 fun n => hcon' _ (hall _)
    have : q ≤ 1 := by
      rw [hq]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have := hpowmono q 1 hq0 this
    rw [one_pow] at this
    linarith

open Classical in
/-- pointwise optimality of the first-price bid -/
theorem pointwise (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hX0 : ν {ω | X ω < 0} = 0) {v : ℝ} (hv : 0 ≤ v)
    (y : ℝ) :
    (if r ≤ y then (v - y) * (ν {ω | sig k r (Fd ν X) (X ω) ≤ y}).toReal ^ k else 0) ≤
      (if r ≤ sig k r (Fd ν X) v then (v - sig k r (Fd ν X) v) *
        (ν {ω | sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) v}).toReal ^ k else 0) := by
  set σ := sig k r (Fd ν X)
  set qf : ℝ → ℝ := fun y => (ν {ω | σ (X ω) ≤ y}).toReal with hqf
  have hqf0 : ∀ y, 0 ≤ qf y := fun _ => ENNReal.toReal_nonneg
  set LB : ℝ := if v < r then 0 else Ik k r (Fd ν X) v with hLB
  have hLB0 : 0 ≤ LB := by
    rw [hLB]; split_ifs with h
    · exact le_refl 0
    · exact Ik_nn k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) (not_lt.mp h)
  -- lower bound for the σ bid
  have hlow : LB ≤ (if r ≤ σ v then (v - σ v) * qf (σ v) ^ k else 0) := by
    by_cases hvr : v < r
    · have : σ v = v := by simp only [σ]; unfold sig; rw [if_pos hvr]
      rw [hLB, if_pos hvr, this, if_neg (not_le.mpr hvr)]
    · have hvr' : r ≤ v := not_lt.mp hvr
      rw [hLB, if_neg hvr]
      by_cases hH : Hk k (Fd ν X) v = 0
      · have hI : Ik k r (Fd ν X) v = 0 := by
          have := Ik_le k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hvr'
          rw [hH, mul_zero] at this
          exact le_antisymm this (Ik_nn k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hvr')
        rw [hI]
        split_ifs
        · have : σ v = 0 := by simp only [σ]; unfold sig; rw [if_neg hvr, if_pos hH]
          rw [this, sub_zero]
          exact mul_nonneg hv (pow_nonneg (hqf0 _) k)
        · exact le_refl 0
      · have hge := sig_ge_r k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hvr' hH
        rw [if_pos hge]
        have hpos : 0 < Hk k (Fd ν X) v := lt_of_le_of_ne (Hk_nn k (Fd_nn (ν := ν) (X := X)) v) (Ne.symm hH)
        have hsv : σ v = v - Ik k r (Fd ν X) v / Hk k (Fd ν X) v := by
          simp only [σ]; unfold sig; rw [if_neg hvr, if_neg hH]
        have hm1 := M1 k hk r hX0 hvr' hH
        have hpow : Hk k (Fd ν X) v ≤ qf (σ v) ^ k := pow_le_pow_left₀ (Fd_nn v) hm1 k
        have hdiff : v - σ v = Ik k r (Fd ν X) v / Hk k (Fd ν X) v := by rw [hsv]; ring
        have hI0 := Ik_nn k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hvr'
        calc Ik k r (Fd ν X) v = (v - σ v) * Hk k (Fd ν X) v := by
              rw [hdiff]; field_simp
          _ ≤ (v - σ v) * qf (σ v) ^ k :=
              mul_le_mul_of_nonneg_left hpow (by rw [hdiff]; exact div_nonneg hI0 hpos.le)
  -- upper bound for any bid
  have hup : (if r ≤ y then (v - y) * qf y ^ k else 0) ≤ LB := by
    split_ifs with hry
    · by_cases hvy : v ≤ y
      · have : (v - y) * qf y ^ k ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg (hqf0 _) k)
        linarith
      · push Not at hvy
        have hvr : ¬ v < r := by linarith
        rw [hLB, if_neg hvr]
        by_contra hcon
        push Not at hcon
        have hvy' : 0 < v - y := by linarith
        set κ := Ik k r (Fd ν X) v / (v - y)
        have hκ0 : 0 ≤ κ := div_nonneg (Ik_nn k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) (by linarith)) hvy'.le
        have hκ : κ < qf y ^ k := by
          rw [div_lt_iff₀ hvy']; linarith
        obtain ⟨x, hxD, hx⟩ := M2 k hk r hX0 y κ hκ0 hκ
        have hx' : Ik k r (Fd ν X) v < (v - y) * Hk k (Fd ν X) x := by
          have := (div_lt_iff₀' hvy').mp hx
          simpa [Hk] using this
        rcases hxD with hxr | ⟨hxr, hσx⟩
        · -- below reserve
          have h1 : Hk k (Fd ν X) x ≤ Hk k (Fd ν X) r := Hk_mono k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hxr.le
          have h2 := (int_bounds k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) (show r ≤ v by linarith)).1
          have h3 : (v - y) * Hk k (Fd ν X) x ≤ (v - r) * Hk k (Fd ν X) r :=
            mul_le_mul (by linarith) h1 (Hk_nn k (Fd_nn (ν := ν) (X := X)) x) (by linarith)
          unfold Ik at hx'
          linarith
        · by_cases hHx : Hk k (Fd ν X) x = 0
          · rw [hHx, mul_zero] at hx'
            linarith [Ik_nn k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) (show r ≤ v by linarith)]
          · have hk' := key_ineq k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hxr hHx v
            have : (v - y) * Hk k (Fd ν X) x ≤ Hk k (Fd ν X) x * (v - σ x) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (by linarith) (Hk_nn k (Fd_nn (ν := ν) (X := X)) x)
            linarith
    · exact hLB0
  exact le_trans hup hlow

end Meas

end L1Aux


open MeasureTheory Filter Topology

namespace L1Aux

section Atomless

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν] {X : Ω → ℝ}

lemma Fd_eq_cdf (hX : Measurable X) :
    Fd ν X = fun x => ProbabilityTheory.cdf (ν.map X) x := by
  funext x
  have : IsProbabilityMeasure (ν.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, Measure.real, Measure.map_apply hX measurableSet_Iic]
  rfl

lemma Fd_continuous (hX : Measurable X) (hatom : ∀ c, ν {ω | X ω = c} = 0) :
    Continuous (Fd ν X) := by
  have : IsProbabilityMeasure (ν.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [Fd_eq_cdf hX]
  set f := ProbabilityTheory.cdf (ν.map X)
  rw [continuous_iff_continuousAt]
  intro a
  have hleft : Function.leftLim f a = f a := by
    have h1 := f.measure_singleton a
    rw [ProbabilityTheory.measure_cdf, Measure.map_apply hX (measurableSet_singleton a)] at h1
    have h2 : ν (X ⁻¹' {a}) = 0 := hatom a
    rw [h2, eq_comm, ENNReal.ofReal_eq_zero] at h1
    have h3 : Function.leftLim f a ≤ f a := f.mono.leftLim_le (le_refl a)
    linarith
  rw [f.mono.continuousAt_iff_leftLim_eq_rightLim, hleft, f.rightLim_eq]

variable (k : ℕ) (r : ℝ)

/-- under no atoms: the win probability at the bid `σ(x)` is `F(x)`. -/
lemma q_sig_eq (hk : 1 ≤ k) (hX : Measurable X) (hatom : ∀ c, ν {ω | X ω = c} = 0)
    (hX0 : ν {ω | X ω < 0} = 0) {x : ℝ} (hx : r < x) (hH : Hk k (Fd ν X) x ≠ 0) :
    (ν {ω | sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) x}).toReal = Fd ν X x := by
  have hFc := Fd_continuous hX hatom
  have hHc : Continuous (Hk k (Fd ν X)) := hFc.pow k
  apply le_antisymm _ (M1 k hk r hX0 hx.le hH)
  -- upper bound
  by_cases hF1 : Fd ν X x = 1
  · rw [hF1]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hFlt : Fd ν X x < 1 := lt_of_le_of_ne (Fd_le_one x) hF1
  -- the set of y > x with F y ≤ F x is bounded
  set E := {y : ℝ | Fd ν X y ≤ Fd ν X x} with hE
  have hEbdd : BddAbove E := by
    have := (tendsto_Fd_top (ν := ν) (X := X))
    have hev : ∀ᶠ n : ℕ in atTop, Fd ν X x < Fd ν X n := this.eventually (lt_mem_nhds hFlt)
    obtain ⟨n, hn⟩ := hev.exists
    refine ⟨n, fun y hy => ?_⟩
    by_contra h
    push Not at h
    have := Fd_mono (ν := ν) (X := X) h.le
    have hy' : Fd ν X y ≤ Fd ν X x := hy
    linarith
  have hxE : x ∈ E := show Fd ν X x ≤ Fd ν X x from le_refl _
  set z := sSup E
  have hxz : x ≤ z := le_csSup hEbdd hxE
  have hFz : Fd ν X z ≤ Fd ν X x := by
    have hcl : IsClosed E := isClosed_le hFc continuous_const
    exact hcl.csSup_mem ⟨x, hxE⟩ hEbdd
  -- key: points above x with the same bid have F = F x
  have hflat : ∀ y, x < y → sig k r (Fd ν X) y ≤ sig k r (Fd ν X) x → y ∈ E := by
    intro y hxy hsy
    have hry : r ≤ y := by linarith
    have hHle : Hk k (Fd ν X) x ≤ Hk k (Fd ν X) y := Hk_mono k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hxy.le
    have hpx : 0 < Hk k (Fd ν X) x := lt_of_le_of_ne (Hk_nn k (Fd_nn (ν := ν) (X := X)) x) (Ne.symm hH)
    have hpy : 0 < Hk k (Fd ν X) y := lt_of_lt_of_le hpx hHle
    have hHy : Hk k (Fd ν X) y ≠ 0 := ne_of_gt hpy
    -- H constant on [x, y]
    have hHeq : Hk k (Fd ν X) x = Hk k (Fd ν X) y := by
      by_contra hne
      have hlt : Hk k (Fd ν X) x < Hk k (Fd ν X) y := lt_of_le_of_ne hHle hne
      have hJ : ∫ s in x..y, Hk k (Fd ν X) s < ∫ s in x..y, Hk k (Fd ν X) y :=
        intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hxy
          hHc.continuousOn continuousOn_const
          (fun s hs => Hk_mono k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hs.2) ⟨x, ⟨le_refl x, hxy.le⟩, hlt⟩
      rw [intervalIntegral.integral_const, smul_eq_mul] at hJ
      have hsplit : Ik k r (Fd ν X) y = Ik k r (Fd ν X) x + ∫ s in x..y, Hk k (Fd ν X) s := by
        unfold Ik
        rw [intervalIntegral.integral_add_adjacent_intervals (Hk_ii k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) _ _)
          (Hk_ii k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) _ _)]
      have hsx : sig k r (Fd ν X) x = x - Ik k r (Fd ν X) x / Hk k (Fd ν X) x := by
        unfold sig; rw [if_neg (not_lt.mpr hx.le), if_neg hH]
      have hsy' : sig k r (Fd ν X) y = y - Ik k r (Fd ν X) y / Hk k (Fd ν X) y := by
        unfold sig; rw [if_neg (not_lt.mpr hry), if_neg hHy]
      rw [hsx, hsy', hsplit] at hsy
      have hI0 := Ik_nn k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hx.le
      -- derive contradiction
      have h1 : Ik k r (Fd ν X) x / Hk k (Fd ν X) y ≤ Ik k r (Fd ν X) x / Hk k (Fd ν X) x :=
        div_le_div_of_nonneg_left hI0 hpx hHle
      have h2 : (∫ s in x..y, Hk k (Fd ν X) s) / Hk k (Fd ν X) y < y - x := by
        rw [div_lt_iff₀ hpy]; linarith
      have h3 : (Ik k r (Fd ν X) x + ∫ s in x..y, Hk k (Fd ν X) s) / Hk k (Fd ν X) y =
          Ik k r (Fd ν X) x / Hk k (Fd ν X) y +
            (∫ s in x..y, Hk k (Fd ν X) s) / Hk k (Fd ν X) y := add_div _ _ _
      linarith
    -- F y = F x
    show Fd ν X y ≤ Fd ν X x
    have : Fd ν X x = Fd ν X y := by
      unfold Hk at hHeq
      exact (pow_left_inj₀ (Fd_nn x) (Fd_nn y) (by omega)).mp hHeq
    rw [this]
  -- measure bound
  have hsub : {ω | sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) x} ⊆ {ω | X ω ≤ z} := by
    intro ω (hω : sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) x)
    show X ω ≤ z
    by_cases h : X ω ≤ x
    · linarith
    · push Not at h
      exact le_csSup hEbdd (hflat _ h hω)
  have h1 : (ν {ω | sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) x}).toReal ≤ Fd ν X z :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  linarith

open Classical in
/-- the conditional payment of value `x` -/
noncomputable def psi (x : ℝ) : ℝ :=
  if r ≤ sig k r (Fd ν X) x then
    sig k r (Fd ν X) x * (ν {ω | sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) x}).toReal ^ k
  else 0

lemma psi_gt (hk : 1 ≤ k) (hX : Measurable X) (hatom : ∀ c, ν {ω | X ω = c} = 0)
    (hX0 : ν {ω | X ω < 0} = 0) {x : ℝ} (hx : r < x) :
    psi (ν := ν) (X := X) k r x = x * Hk k (Fd ν X) x - Ik k r (Fd ν X) x := by
  unfold psi
  by_cases hH : Hk k (Fd ν X) x = 0
  · have hs : sig k r (Fd ν X) x = 0 := by
      unfold sig; rw [if_neg (not_lt.mpr hx.le), if_pos hH]
    have hI : Ik k r (Fd ν X) x = 0 := by
      have h1 := Ik_le k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hx.le
      rw [hH, mul_zero] at h1
      exact le_antisymm h1 (Ik_nn k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hx.le)
    rw [hs, hH, hI]
    split_ifs <;> simp
  · have hge := sig_ge_r k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) hx.le hH
    rw [if_pos hge, q_sig_eq k r hk hX hatom hX0 hx hH]
    have hs : sig k r (Fd ν X) x = x - Ik k r (Fd ν X) x / Hk k (Fd ν X) x := by
      unfold sig; rw [if_neg (not_lt.mpr hx.le), if_neg hH]
    rw [hs]
    have : Fd ν X x ^ k = Hk k (Fd ν X) x := rfl
    rw [this]
    field_simp

lemma psi_lt {x : ℝ} (hx : x < r) : psi (ν := ν) (X := X) k r x = 0 := by
  unfold psi
  have hs : sig k r (Fd ν X) x = x := by unfold sig; rw [if_pos hx]
  rw [hs, if_neg (not_le.mpr hx)]

lemma psi_continuousAt (hk : 1 ≤ k) (hX : Measurable X) (hatom : ∀ c, ν {ω | X ω = c} = 0)
    (hX0 : ν {ω | X ω < 0} = 0) {x₀ : ℝ} (hx₀ : x₀ ≠ r) :
    ContinuousAt (psi (ν := ν) (X := X) k r) x₀ := by
  rcases lt_or_gt_of_ne hx₀ with h | h
  · have : psi (ν := ν) (X := X) k r =ᶠ[𝓝 x₀] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with x hx
      exact psi_lt k r hx
    exact continuousAt_const.congr this.symm
  · have hFc := Fd_continuous hX hatom
    have hHc : Continuous (Hk k (Fd ν X)) := hFc.pow k
    have hIc : Continuous (Ik k r (Fd ν X)) :=
      intervalIntegral.continuous_primitive
        (fun a b => Hk_ii k (Fd_mono (ν := ν) (X := X)) (Fd_nn (ν := ν) (X := X)) a b) r
    have : psi (ν := ν) (X := X) k r =ᶠ[𝓝 x₀]
        fun x => x * Hk k (Fd ν X) x - Ik k r (Fd ν X) x := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      exact psi_gt k r hk hX hatom hX0 hx
    exact ((continuous_id.mul hHc).sub hIc).continuousAt.congr this.symm

end Atomless

end L1Aux


open MeasureTheory ContextualAuctions.Existence

namespace CAC

lemma measurableSet_Theta (M : Model) : MeasurableSet (Theta M) := by
  simp only [Theta, Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
  · exact (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst)).inter
      (measurableSet_lt ((measurable_pi_apply i).comp measurable_fst) measurable_const)
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)

lemma measurable_val (d : ℕ) :
    Measurable (fun q : ((Fin d → ℝ) × ℝ) × (Fin d → ℝ) => val q.1 q.2) := by
  unfold val
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).mul
    ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_sigma (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) : Measurable (fun p : (Fin M.d → ℝ) × ℝ => sigma M μ p.1 p.2) := by
  classical
  have := hM.probG
  have hpaced : Measurable
      (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => paced μ q.1 q.2) := by
    unfold paced
    exact (measurable_val M.d).div (measurable_const.add (hμ.comp measurable_fst))
  have hS : MeasurableSet
      {p : ((Fin M.d → ℝ) × ℝ) × ((Fin M.d → ℝ) × ℝ) | paced μ p.2 p.1.1 ≤ p.1.2} := by
    apply measurableSet_le
    · exact hpaced.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    · exact measurable_snd.comp measurable_fst
  have hH : Measurable (fun p : (Fin M.d → ℝ) × ℝ => H M μ p.1 p.2) := by
    unfold H
    have := measurable_measure_prodMk_left (ν := M.G) hS
    exact (this.ennreal_toReal).pow_const _
  have hint1 : ∀ (a b : ((Fin M.d → ℝ) × ℝ) → ℝ), Measurable a → Measurable b →
      StronglyMeasurable (fun p : (Fin M.d → ℝ) × ℝ =>
        ∫ s in Set.Ioc (a p) (b p), H M μ p.1 s) := by
    intro a b ha hb
    have hg : Measurable (fun q : ((Fin M.d → ℝ) × ℝ) × ℝ =>
        Set.indicator {q : ((Fin M.d → ℝ) × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1}
          (fun q => H M μ q.1.1 q.2) q) := by
      apply Measurable.indicator
      · exact hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
          (measurableSet_le measurable_snd (hb.comp measurable_fst))
    have := (hg.stronglyMeasurable).integral_prod_right' (ν := (volume : Measure ℝ))
    convert this using 2 with p
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  have hI : Measurable (fun p : (Fin M.d → ℝ) × ℝ => ∫ s in (M.r p.1)..p.2, H M μ p.1 s) := by
    have h1 := (hint1 (fun p => M.r p.1) (fun p => p.2)
      (hM.measurable_r.comp measurable_fst) measurable_snd).measurable
    have h2 := (hint1 (fun p => p.2) (fun p => M.r p.1) measurable_snd
      (hM.measurable_r.comp measurable_fst)).measurable
    have := h1.sub h2
    convert this using 1
    funext p
    simp [intervalIntegral]
  unfold sigma
  refine Measurable.ite (measurableSet_lt measurable_snd
    (hM.measurable_r.comp measurable_fst)) measurable_snd ?_
  refine Measurable.ite (measurableSet_eq_fun hH measurable_const) measurable_const ?_
  exact measurable_snd.sub (hI.div hH)

lemma measurable_beta (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) : Measurable (Function.uncurry (beta M μ)) := by
  have hpaced : Measurable
      (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => paced μ q.1 q.2) := by
    unfold paced
    exact (measurable_val M.d).div (measurable_const.add (hμ.comp measurable_fst))
  have : Function.uncurry (beta M μ) =
      (fun p : (Fin M.d → ℝ) × ℝ => sigma M μ p.1 p.2) ∘
        (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => (q.2, paced μ q.1 q.2)) := by
    funext q; rfl
  rw [this]
  exact (measurable_sigma M hM μ hμ).comp (measurable_snd.prodMk hpaced)

/-- the paced bid of type `θ` with multiplier `t`. -/
noncomputable def bidT (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) :
    (Fin M.d → ℝ) → ℝ :=
  fun α => sigma M μ α (val θ α / (1 + t))

lemma bddAbove_omega (M : Model) (hM : M.Standing) :
    BddAbove {v | ∃ θ ∈ Theta M, ∃ α ∈ M.A, v = val θ α} := by
  obtain ⟨R, hR⟩ := hM.A_bounded.subset_closedBall 0
  refine ⟨∑ _i : Fin M.d, M.U * R, ?_⟩
  rintro v ⟨θ, hθ, α, hα, rfl⟩
  unfold val
  apply Finset.sum_le_sum
  intro i _
  have hαi : |α i| ≤ R := by
    have := hR hα
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact (norm_le_pi_norm α i).trans this
  have hpos := hM.A_pos hα i
  have hw := hθ.1 i
  calc θ.1 i * α i ≤ M.U * α i := mul_le_mul_of_nonneg_right hw.2.le hpos.le
    _ ≤ M.U * R := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hαi) hM.U_pos.le

lemma val_le_omega (M : Model) (hM : M.Standing) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M)
    {α : Fin M.d → ℝ} (hα : α ∈ M.A) : val θ α ≤ omega M :=
  le_csSup (bddAbove_omega M hM) ⟨θ, hθ, α, hα, rfl⟩

lemma theta_nonempty (M : Model) (hM : M.Standing) : (Theta M).Nonempty := by
  refine ⟨(fun _ => M.U / 2, (M.Bmin + M.U) / 2), fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · have := hM.U_pos; simp only; linarith
  · have := hM.U_pos; simp only; linarith
  · have := hM.Bmin_lt_U; simp only; linarith
  · have := hM.Bmin_lt_U; simp only; linarith

lemma omega_nonneg (M : Model) (hM : M.Standing) : 0 ≤ omega M := by
  obtain ⟨θ, hθ⟩ := theta_nonempty M hM
  obtain ⟨α, hα⟩ := hM.A_nonempty
  refine le_trans ?_ (val_le_omega M hM hθ hα)
  unfold val
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i).1.le (hM.A_pos hα i).le

lemma ae_A (M : Model) (hM : M.Standing) : ∀ᵐ ω ∂P M, ω.1 ∈ M.A := by
  have := hM.probG
  have := hM.probF
  have h1 : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.F_A
  exact (Measure.quasiMeasurePreserving_fst (μ := M.F)
    (ν := Measure.pi fun _ : Fin (M.n - 1) => M.G)).ae h1

open Classical in
lemma elem_le (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ 1 + t)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M μ) b) :
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M ≤ omega M := by
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hω0 := omega_nonneg M hM
  have hle : ∀ᵐ ω ∂P M,
      (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ≤ omega M := by
    filter_upwards [ae_A M hM] with ω hω
    split_ifs
    · have := hb.2.1 ω.1 hω
      have := val_le_omega M hM hθ hω
      nlinarith
    · exact hω0
  by_cases hint : Integrable (fun ω =>
      if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) (P M)
  · calc _ ≤ ∫ _ω, omega M ∂P M := integral_mono_ae hint (integrable_const _) hle
      _ = omega M := by simp
  · rw [integral_undef hint]; exact hω0

open Classical in
lemma zero_admissible (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) :
    Admissible M (beta M μ) (fun _ => 0) := by
  refine ⟨measurable_const, fun _ _ => le_refl 0, ?_⟩
  simp only [ite_self]
  exact integrable_zero _ _ _

open Classical in
/-- the set whose supremum defines `qDual` -/
def Sset (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) : Set ℝ :=
  {v | ∃ b, Admissible M (beta M μ) b ∧
    v = ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M}

lemma qDual_eq (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) :
    qDual M μ θ t = sSup (Sset M μ θ t) + t * θ.2 := rfl

lemma Sset_bdd (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ 1 + t) :
    BddAbove (Sset M μ θ t) ∧ (Sset M μ θ t).Nonempty ∧ sSup (Sset M μ θ t) ≤ omega M := by
  have hbdd : BddAbove (Sset M μ θ t) := by
    refine ⟨omega M, ?_⟩
    rintro v ⟨b, hb, rfl⟩
    exact elem_le M hM μ hθ ht b hb
  have hne : (Sset M μ θ t).Nonempty := ⟨_, ⟨fun _ => 0, zero_admissible M μ, rfl⟩⟩
  refine ⟨hbdd, hne, csSup_le hne ?_⟩
  rintro v ⟨b, hb, rfl⟩
  exact elem_le M hM μ hθ ht b hb

open Classical in
lemma Sset_zero_nonneg (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ 1 + t) :
    0 ≤ sSup (Sset M μ θ t) := by
  have hmem : (∫ ω, (if wins M (beta M μ) (fun _ => 0) ω then val θ ω.1 - (1 + t) * 0
      else 0) ∂P M) ∈ Sset M μ θ t := ⟨fun _ => 0, zero_admissible M μ, rfl⟩
  have hnn : 0 ≤ ∫ ω, (if wins M (beta M μ) (fun _ => 0) ω then val θ ω.1 - (1 + t) * 0
      else 0) ∂P M := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_A M hM] with ω hω
    split_ifs
    · simp only [mul_zero, sub_zero]
      unfold val
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (hθ.1 i).1.le (hM.A_pos hω i).le
    · exact le_refl 0
  exact hnn.trans (le_csSup (Sset_bdd M hM μ hθ ht).1 hmem)

open Classical in
lemma integral_scale (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    {t : ℝ} (ht : 0 < 1 + t) (b : (Fin M.d → ℝ) → ℝ) :
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M =
      (1 + t) * lagr M μ θ t b := by
  unfold lagr
  rw [← integral_const_mul]
  congr 1
  funext ω
  split_ifs
  · field_simp
  · simp

lemma measurableSet_wins (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) (b : (Fin M.d → ℝ) → ℝ) (hb : Measurable b) :
    MeasurableSet {ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) |
      wins M (beta M μ) b ω} := by
  unfold wins
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun i => ?_)
  · exact measurableSet_le (hM.measurable_r.comp measurable_fst) (hb.comp measurable_fst)
  · refine measurableSet_le ?_ (hb.comp measurable_fst)
    have hm : Measurable (fun q : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) =>
        (q.2 i, q.1)) := by fun_prop
    exact (measurable_beta M hM μ hμ).comp hm

open Classical in
lemma affine_elem (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M μ) b) :
    ∃ A Pb : ℝ, ∀ t : ℝ,
      ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M =
        A - (1 + t) * Pb := by
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hW := measurableSet_wins M hM μ hμ b hb.1
  have hv : Measurable (fun ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) =>
      val θ ω.1) :=
    (measurable_val M.d).comp (measurable_const.prodMk measurable_fst)
  have hint1 : Integrable (fun ω => if wins M (beta M μ) b ω then val θ ω.1 else 0) (P M) := by
    refine Integrable.mono' (integrable_const (omega M)) ?_ ?_
    · exact (Measurable.ite hW hv measurable_const).aestronglyMeasurable
    · filter_upwards [ae_A M hM] with ω hω
      split_ifs
      · have h0 : 0 ≤ val θ ω.1 := by
          unfold val
          exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i).1.le (hM.A_pos hω i).le
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact val_le_omega M hM hθ hω
      · simpa using omega_nonneg M hM
  refine ⟨∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 else 0) ∂P M,
    ∫ ω, (if wins M (beta M μ) b ω then b ω.1 else 0) ∂P M, fun t => ?_⟩
  rw [← integral_const_mul, ← integral_sub hint1 (hb.2.2.const_mul _)]
  congr 1
  funext ω
  split_ifs <;> ring

lemma G_ac_restrict (M : Model) (hM : M.Standing) : M.G ≪ volume.restrict (Theta M) := by
  intro s hs
  rw [Measure.restrict_apply_eq_zero' (measurableSet_Theta M)] at hs
  have h1 : M.G (s ∩ Theta M) = 0 := hM.G_ac hs
  apply measure_mono_null (t := (s ∩ Theta M) ∪ (Theta M)ᶜ)
  · intro x hx
    by_cases hxT : x ∈ Theta M
    · exact Or.inl ⟨hx, hxT⟩
    · exact Or.inr hxT
  · exact measure_union_null h1 hM.G_Theta

/-- `sigma` is the generic `sig` for the paced-value distribution. -/
lemma sigma_eq (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (α : Fin M.d → ℝ) :
    sigma M μ α = L1Aux.sig (M.n - 1) (M.r α) (L1Aux.Fd M.G (fun θ' => paced μ θ' α)) := rfl

lemma paced_nonneg_ae (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) {α : Fin M.d → ℝ} (hα : α ∈ M.A) :
    M.G {θ' | paced μ θ' α < 0} = 0 := by
  apply measure_mono_null _ hM.G_Theta
  intro θ' hθ' hmem
  have h1 : 0 ≤ val θ' α := by
    unfold val
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hmem.1 i).1.le (hM.A_pos hα i).le
  have h2 : 0 < 1 + μ θ' := by linarith [hμ.2 θ' hmem]
  exact absurd hθ' (not_lt.mpr (div_nonneg h1 h2.le))

lemma val_nonneg (M : Model) (hM : M.Standing) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M)
    {α : Fin M.d → ℝ} (hα : α ∈ M.A) : 0 ≤ val θ α := by
  unfold val
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i).1.le (hM.A_pos hα i).le

lemma sigma_bounds (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) {α : Fin M.d → ℝ} (hα : α ∈ M.A) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ sigma M μ α x ∧ sigma M μ α x ≤ x := by
  have := hM.probG
  have hk : 1 ≤ M.n - 1 := by have := hM.two_le_n; omega
  have hX0 := paced_nonneg_ae M hM μ hμ hα
  rw [sigma_eq]
  by_cases hlt : x < M.r α
  · unfold L1Aux.sig; rw [if_pos hlt]; exact ⟨hx, le_refl x⟩
  · have hr : M.r α ≤ x := not_lt.mp hlt
    refine ⟨L1Aux.sig_nonneg (M.n - 1) L1Aux.Fd_mono L1Aux.Fd_nn (L1Aux.Fd_neg hX0) hk hr, ?_⟩
    by_cases hH : L1Aux.Hk (M.n - 1) (L1Aux.Fd M.G (fun θ' => paced μ θ' α)) x = 0
    · unfold L1Aux.sig; rw [if_neg hlt, if_pos hH]; exact hx
    · exact L1Aux.sig_le_self (M.n - 1) L1Aux.Fd_mono L1Aux.Fd_nn hr hH

open Classical in
/-- the inner integral over the competitors, for a fixed context. -/
lemma inner_integral (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) (b : (Fin M.d → ℝ) → ℝ) (v : (Fin M.d → ℝ) → ℝ)
    (α : Fin M.d → ℝ) :
    ∫ θs, (if wins M (beta M μ) b (α, θs) then v α - b α else 0)
        ∂(Measure.pi fun _ : Fin (M.n - 1) => M.G) =
      (if M.r α ≤ b α then (v α - b α) *
        (M.G {θ' | beta M μ θ' α ≤ b α}).toReal ^ (M.n - 1) else 0) := by
  have := hM.probG
  set E := {θ' : (Fin M.d → ℝ) × ℝ | beta M μ θ' α ≤ b α} with hE
  have hEm : MeasurableSet E := by
    apply measurableSet_le _ measurable_const
    have hm : Measurable (fun θ' : (Fin M.d → ℝ) × ℝ => (θ', α)) := by fun_prop
    exact (measurable_beta M hM μ hμ.1).comp hm
  by_cases hr : M.r α ≤ b α
  · rw [if_pos hr]
    have hfun : (fun θs : Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ =>
        if wins M (beta M μ) b (α, θs) then v α - b α else 0) =
        (Set.pi Set.univ fun _ => E).indicator (fun _ => v α - b α) := by
      funext θs
      simp only [Set.indicator, Set.mem_pi, Set.mem_univ, true_implies]
      congr 1
      apply propext
      unfold wins
      simp only [hr, true_and]
      rfl
    rw [hfun, integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hEm)]
    rw [Measure.real, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
      smul_eq_mul]
    ring
  · rw [if_neg hr]
    have : (fun θs : Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ =>
        if wins M (beta M μ) b (α, θs) then v α - b α else 0) = fun _ => 0 := by
      funext θs
      rw [if_neg]
      intro hw
      exact hr hw.1
    rw [this, integral_zero]

open Classical in
lemma integrable_g (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ t)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M μ) b) :
    Integrable (fun ω => if wins M (beta M μ) b ω then val θ ω.1 / (1 + t) - b ω.1 else 0)
      (P M) := by
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hW := measurableSet_wins M hM μ hμ.1 b hb.1
  have hv : Measurable (fun ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) =>
      val θ ω.1 / (1 + t)) :=
    ((measurable_val M.d).comp (measurable_const.prodMk measurable_fst)).div_const _
  have hint1 : Integrable (fun ω => if wins M (beta M μ) b ω then val θ ω.1 / (1 + t) else 0)
      (P M) := by
    refine Integrable.mono' (integrable_const (omega M)) ?_ ?_
    · exact (Measurable.ite hW hv measurable_const).aestronglyMeasurable
    · filter_upwards [ae_A M hM] with ω hω
      split_ifs
      · have h0 := val_nonneg M hM hθ hω
        have h1 : val θ ω.1 / (1 + t) ≤ val θ ω.1 := div_le_self h0 (by linarith)
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (by linarith))]
        exact h1.trans (val_le_omega M hM hθ hω)
      · simpa using omega_nonneg M hM
  have := hint1.sub hb.2.2
  convert this using 1
  funext ω
  simp only [Pi.sub_apply]
  split_ifs <;> simp

end CAC


open MeasureTheory ContextualAuctions.Existence Filter Topology

namespace P1

/-- the kernel of a nonzero linear functional is Lebesgue-null -/
lemma volume_ker_null {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →ₗ[ℝ] ℝ) (hL : L ≠ 0) : μ {x | L x = 0} = 0 := by
  have : (LinearMap.ker L : Set E) = {x | L x = 0} := by ext; simp
  rw [← this]
  apply Measure.addHaar_submodule
  intro h
  apply hL
  ext x
  have : x ∈ LinearMap.ker L := by rw [h]; trivial
  simpa using this

/-- a line is null in dimension at least two -/
lemma span_ne_top {d : ℕ} (hd : 2 ≤ d) (β : Fin d → ℝ) :
    (Submodule.span ℝ {β} : Submodule ℝ (Fin d → ℝ)) ≠ ⊤ := by
  intro h
  have h1 : Module.finrank ℝ (Submodule.span ℝ {β}) ≤ 1 := by
    have := finrank_span_le_card (R := ℝ) ({β} : Set (Fin d → ℝ))
    simpa using this
  rw [h, finrank_top, Module.finrank_fin_fun] at h1
  omega

lemma linear_val (d : ℕ) (β : Fin d → ℝ) :
    ∃ L : ((Fin d → ℝ) × ℝ) →ₗ[ℝ] ℝ, ∀ θ, L θ = ∑ i, θ.1 i * β i := by
  refine ⟨∑ i, β i • ((LinearMap.proj i).comp (LinearMap.fst ℝ (Fin d → ℝ) ℝ)), fun θ => ?_⟩
  simp [LinearMap.sum_apply, mul_comm]

instance haar_prod (d : ℕ) : (volume : Measure ((Fin d → ℝ) × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

lemma atomless_ae (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) : ∀ᵐ α ∂M.F, ∀ c, M.G {θ | paced μ θ α = c} = 0 := by
  have := hM.probG
  set S : (Fin M.d → ℝ) → Set ((Fin M.d → ℝ) × ℝ) :=
    fun β => {θ | θ ∈ Theta M ∧ val θ β = 1 + μ θ} with hS
  have hSm : ∀ β, MeasurableSet (S β) := by
    intro β
    refine (CAC.measurableSet_Theta M).inter (measurableSet_eq_fun ?_ ?_)
    · exact (CAC.measurable_val M.d).comp (measurable_id.prodMk measurable_const)
    · exact measurable_const.add hμ.1
  have hdisj : Pairwise (Function.onFun (AEDisjoint M.G) S) := by
    intro β β' hne
    show M.G (S β ∩ S β') = 0
    obtain ⟨L, hL⟩ := linear_val M.d (β - β')
    have hL0 : L ≠ 0 := by
      intro h0
      apply hne
      funext i
      have := hL (Pi.single i 1, 0)
      rw [h0] at this
      simp [Pi.single_apply] at this
      linarith
    apply measure_mono_null _ (hM.G_ac (volume_ker_null volume L hL0))
    rintro θ ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    show L θ = 0
    rw [hL]
    have : val θ β - val θ β' = 0 := by rw [h1, h2]; ring
    unfold val at this
    rw [← Finset.sum_sub_distrib] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hC : Set.Countable {β | 0 < M.G (S β)} :=
    Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ M.G
      (fun β => (hSm β).nullMeasurableSet) hdisj (measure_ne_top _ _)
  have hFA : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.F_A
  have hlines : ∀ᵐ α ∂M.F, α ∉ ⋃ β ∈ {β | 0 < M.G (S β)},
      (Submodule.span ℝ {β} : Set (Fin M.d → ℝ)) := by
    rw [ae_iff]
    simp only [not_not]
    apply (measure_biUnion_null_iff hC).mpr
    intro β _
    apply hM.F_ac
    exact Measure.addHaar_submodule volume _ (span_ne_top hM.two_le_d β)
  filter_upwards [hFA, hlines] with α hα hl c
  by_contra hne
  apply hl
  have hpos : 0 < M.G {θ | paced μ θ α = c} := pos_iff_ne_zero.mpr hne
  -- on Θ the paced value is positive
  have hvalpos : ∀ θ ∈ Theta M, 0 < val θ α := by
    intro θ hθ
    unfold val
    have hd : 0 < M.d := by have := hM.two_le_d; omega
    exact Finset.sum_pos (fun i _ => mul_pos (hθ.1 i).1 (hM.A_pos hα i))
      ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hsub : {θ | paced μ θ α = c} ⊆ (Theta M)ᶜ ∪ (Theta M ∩ {θ | paced μ θ α = c}) := by
    intro θ hθ
    by_cases h : θ ∈ Theta M
    · exact Or.inr ⟨h, hθ⟩
    · exact Or.inl h
  have hle : M.G {θ | paced μ θ α = c} ≤ M.G (Theta M ∩ {θ | paced μ θ α = c}) := by
    calc _ ≤ M.G ((Theta M)ᶜ ∪ (Theta M ∩ {θ | paced μ θ α = c})) := measure_mono hsub
      _ ≤ M.G (Theta M)ᶜ + M.G (Theta M ∩ {θ | paced μ θ α = c}) := measure_union_le _ _
      _ = _ := by rw [hM.G_Theta, zero_add]
  have hne' : (Theta M ∩ {θ | paced μ θ α = c}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)
  obtain ⟨θ0, hθ0, hc0⟩ := hne'
  have hcpos : 0 < c := by
    have h1 := hvalpos θ0 hθ0
    have h2 : 0 < 1 + μ θ0 := by linarith [hμ.2 θ0 hθ0]
    rw [← show paced μ θ0 α = c from hc0]
    exact div_pos h1 h2
  have hEq : Theta M ∩ {θ | paced μ θ α = c} = S (c⁻¹ • α) := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hS]
    constructor
    · rintro ⟨hθ, hp⟩
      refine ⟨hθ, ?_⟩
      have h2 : 0 < 1 + μ θ := by linarith [hμ.2 θ hθ]
      unfold paced at hp
      have : val θ (c⁻¹ • α) = c⁻¹ * val θ α := by
        unfold val; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
        simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      field_simp at hp ⊢
      linarith
    · rintro ⟨hθ, hp⟩
      refine ⟨hθ, ?_⟩
      have h2 : 0 < 1 + μ θ := by linarith [hμ.2 θ hθ]
      unfold paced
      have : val θ (c⁻¹ • α) = c⁻¹ * val θ α := by
        unfold val; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
        simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [this] at hp
      field_simp at hp ⊢
      linarith
  rw [hEq] at hle
  refine Set.mem_biUnion (x := c⁻¹ • α) (lt_of_lt_of_le hpos hle) ?_
  have e : c • (c⁻¹ • α) = α := by rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
  have hmem : c • (c⁻¹ • α) ∈ (Submodule.span ℝ {c⁻¹ • α} : Submodule ℝ (Fin M.d → ℝ)) :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rw [e] at hmem
  exact hmem

/-- the contexts at which the scaled weight `u` exactly meets the reserve -/
def Rset (M : Model) (u : Fin M.d → ℝ) : Set (Fin M.d → ℝ) := {α | ∑ i, u i * α i = M.r α}

/-- the bad weights: countably many -/
def CU (M : Model) : Set (Fin M.d → ℝ) := {u | 0 < M.F (Rset M u)}

lemma CU_countable (M : Model) (hM : M.Standing) : (CU M).Countable := by
  have := hM.probF
  have hRm : ∀ u, MeasurableSet (Rset M u) := by
    intro u
    apply measurableSet_eq_fun _ hM.measurable_r
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hdisj : Pairwise (Function.onFun (AEDisjoint M.F) (Rset M)) := by
    intro u u' hne
    show M.F (Rset M u ∩ Rset M u') = 0
    let L : (Fin M.d → ℝ) →ₗ[ℝ] ℝ := ∑ i, (u - u') i • LinearMap.proj i
    have hL : ∀ α, L α = ∑ i, (u - u') i * α i := by
      intro α; simp [L, LinearMap.sum_apply]
    have hL0 : L ≠ 0 := by
      intro h0
      apply hne
      funext i
      have := hL (Pi.single i 1)
      rw [h0] at this
      simp [Pi.single_apply] at this
      linarith
    apply measure_mono_null _ (hM.F_ac (volume_ker_null volume L hL0))
    rintro α ⟨h1, h2⟩
    show L α = 0
    rw [hL]
    have h1' : ∑ i, u i * α i = M.r α := h1
    have h2' : ∑ i, u' i * α i = M.r α := h2
    have : ∑ i, u i * α i - ∑ i, u' i * α i = 0 := by rw [h1', h2']; ring
    rw [← Finset.sum_sub_distrib] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  exact Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ M.F
    (fun u => (hRm u).nullMeasurableSet) hdisj (measure_ne_top _ _)

/-- the full-measure set of types `Θ'` -/
def ThetaP (M : Model) : Set ((Fin M.d → ℝ) × ℝ) :=
  Theta M \ ⋃ u ∈ CU M, {θ | θ.1 ∈ (Submodule.span ℝ {u} : Submodule ℝ (Fin M.d → ℝ))}

lemma ThetaP_sub (M : Model) : ThetaP M ⊆ Theta M := Set.diff_subset

lemma ThetaP_meas (M : Model) (hM : M.Standing) : MeasurableSet (ThetaP M) := by
  apply (CAC.measurableSet_Theta M).diff
  apply MeasurableSet.biUnion (CU_countable M hM)
  intro u _
  have hcl : IsClosed ((Submodule.span ℝ {u} : Submodule ℝ (Fin M.d → ℝ)) : Set (Fin M.d → ℝ)) :=
    Submodule.closed_of_finiteDimensional _
  exact measurable_fst hcl.measurableSet

lemma ThetaP_full (M : Model) (hM : M.Standing) : M.G (ThetaP M) = 1 := by
  have := hM.probG
  have hnull : M.G (ThetaP M)ᶜ = 0 := by
    have hsub : (ThetaP M)ᶜ ⊆ (Theta M)ᶜ ∪
        ⋃ u ∈ CU M, {θ | θ.1 ∈ (Submodule.span ℝ {u} : Submodule ℝ (Fin M.d → ℝ))} := by
      intro θ hθ
      by_cases h : θ ∈ Theta M
      · right
        by_contra h'
        exact hθ ⟨h, h'⟩
      · exact Or.inl h
    apply measure_mono_null hsub
    apply measure_union_null hM.G_Theta
    apply (measure_biUnion_null_iff (CU_countable M hM)).mpr
    intro u _
    apply hM.G_ac
    have : {θ : (Fin M.d → ℝ) × ℝ | θ.1 ∈ (Submodule.span ℝ {u} : Submodule ℝ (Fin M.d → ℝ))} =
        ((Submodule.span ℝ {u}).prod (⊤ : Submodule ℝ ℝ) : Set ((Fin M.d → ℝ) × ℝ)) := by
      ext θ; simp
    rw [this]
    apply Measure.addHaar_submodule
    intro h
    apply span_ne_top hM.two_le_d u
    rw [eq_top_iff]
    intro x _
    have : (x, (0 : ℝ)) ∈ (Submodule.span ℝ {u}).prod (⊤ : Submodule ℝ ℝ) := by rw [h]; trivial
    exact this.1
  rw [measure_compl (ThetaP_meas M hM) (measure_ne_top _ _), measure_univ] at hnull
  have h1 : M.G (ThetaP M) ≤ 1 := prob_le_one
  have h2 : 1 ≤ M.G (ThetaP M) := by
    by_contra h
    push Not at h
    have : (0 : ENNReal) < 1 - M.G (ThetaP M) := tsub_pos_of_lt h
    rw [hnull] at this
    exact lt_irrefl 0 this
  exact le_antisymm h1 h2

lemma ThetaP_reserve (M : Model) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ ThetaP M) {t : ℝ}
    (ht : 0 ≤ t) : M.F {α | val θ α / (1 + t) = M.r α} = 0 := by
  set u : Fin M.d → ℝ := (1 + t)⁻¹ • θ.1
  have hset : {α | val θ α / (1 + t) = M.r α} = Rset M u := by
    ext α
    simp only [Set.mem_setOf_eq, Rset, u, Pi.smul_apply, smul_eq_mul]
    unfold val
    rw [Finset.sum_div]
    constructor <;> intro h <;> rw [← h] <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      field_simp
  rw [hset]
  by_contra hne
  have hu : u ∈ CU M := pos_iff_ne_zero.mpr hne
  apply hθ.2
  refine Set.mem_biUnion hu ?_
  show θ.1 ∈ (Submodule.span ℝ {u} : Submodule ℝ (Fin M.d → ℝ))
  have e : (1 + t) • u = θ.1 := by
    simp only [u, smul_smul]
    rw [mul_inv_cancel₀ (by linarith), one_smul]
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

open Classical in
lemma inner_integral_gen (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) (b c : (Fin M.d → ℝ) → ℝ) (α : Fin M.d → ℝ) :
    ∫ θs, (if wins M (beta M μ) b (α, θs) then c α else 0)
        ∂(Measure.pi fun _ : Fin (M.n - 1) => M.G) =
      (if M.r α ≤ b α then c α *
        (M.G {θ' | beta M μ θ' α ≤ b α}).toReal ^ (M.n - 1) else 0) := by
  have := hM.probG
  set E := {θ' : (Fin M.d → ℝ) × ℝ | beta M μ θ' α ≤ b α} with hE
  have hEm : MeasurableSet E := by
    apply measurableSet_le _ measurable_const
    have hm : Measurable (fun θ' : (Fin M.d → ℝ) × ℝ => (θ', α)) := by fun_prop
    exact (CAC.measurable_beta M hM μ hμ.1).comp hm
  by_cases hr : M.r α ≤ b α
  · rw [if_pos hr]
    have hfun : (fun θs : Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ =>
        if wins M (beta M μ) b (α, θs) then c α else 0) =
        (Set.pi Set.univ fun _ => E).indicator (fun _ => c α) := by
      funext θs
      simp only [Set.indicator, Set.mem_pi, Set.mem_univ, true_implies]
      congr 1
      apply propext
      unfold wins
      simp only [hr, true_and]
      rfl
    rw [hfun, integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hEm)]
    rw [Measure.real, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
      smul_eq_mul]
    ring
  · rw [if_neg hr]
    have : (fun θs : Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ =>
        if wins M (beta M μ) b (α, θs) then c α else 0) = fun _ => 0 := by
      funext θs
      rw [if_neg]
      intro hw
      exact hr hw.1
    rw [this, integral_zero]

open Classical in
/-- expected payment of the paced bid with multiplier `t` -/
noncomputable def pay (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) : ℝ :=
  ∫ ω, (if wins M (beta M μ) (CAC.bidT M μ θ t) ω then CAC.bidT M μ θ t ω.1 else 0) ∂P M

open Classical in
lemma pay_cont (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ ThetaP M) {ts : ℝ} (hts : 0 ≤ ts) :
    ContinuousWithinAt (pay M μ θ) (Set.Ici 0) ts := by
  have := hM.probG
  have := hM.probF
  have : SigmaFinite M.G := inferInstance
  have : SFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := inferInstance
  have hk : 1 ≤ M.n - 1 := by have := hM.two_le_n; omega
  have hθΘ : θ ∈ Theta M := ThetaP_sub M hθ
  have hP : P M = M.F.prod (Measure.pi fun _ : Fin (M.n - 1) => M.G) := rfl
  set Ψ : ℝ → (Fin M.d → ℝ) → ℝ := fun t α =>
    if M.r α ≤ CAC.bidT M μ θ t α then CAC.bidT M μ θ t α *
      (M.G {θ' | beta M μ θ' α ≤ CAC.bidT M μ θ t α}).toReal ^ (M.n - 1) else 0 with hΨ
  have hadm : ∀ t, 0 ≤ t → Admissible M (beta M μ) (CAC.bidT M μ θ t) :=
    fun t ht => (lemma_1 M hM μ hμ θ hθΘ t ht).1
  have hpayeq : ∀ t, 0 ≤ t → pay M μ θ t = ∫ α, Ψ t α ∂M.F := by
    intro t ht
    have hint := (hadm t ht).2.2
    unfold pay
    rw [hP] at hint ⊢
    rw [integral_prod _ hint]
    congr 1
    funext α
    exact inner_integral_gen M hM μ hμ _ _ α
  have hmeas : ∀ t, 0 ≤ t → AEStronglyMeasurable (Ψ t) M.F := by
    intro t ht
    have hint := (hadm t ht).2.2
    rw [hP] at hint
    refine hint.integral_prod_left.aestronglyMeasurable.congr
      (Eventually.of_forall fun α => ?_)
    exact inner_integral_gen M hM μ hμ _ _ α
  have hFA : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.F_A
  have hbound : ∀ t, 0 ≤ t → ∀ᵐ α ∂M.F, ‖Ψ t α‖ ≤ omega M := by
    intro t ht
    filter_upwards [hFA] with α hα
    have hv0 : 0 ≤ val θ α / (1 + t) := div_nonneg (CAC.val_nonneg M hM hθΘ hα) (by linarith)
    have hvle : val θ α / (1 + t) ≤ omega M :=
      (div_le_self (CAC.val_nonneg M hM hθΘ hα) (by linarith)).trans
        (CAC.val_le_omega M hM hθΘ hα)
    have hb : 0 ≤ CAC.bidT M μ θ t α ∧ CAC.bidT M μ θ t α ≤ val θ α / (1 + t) :=
      CAC.sigma_bounds M hM μ hμ hα hv0
    have hq0 : 0 ≤ (M.G {θ' | beta M μ θ' α ≤ CAC.bidT M μ θ t α}).toReal :=
      ENNReal.toReal_nonneg
    have hq1 : (M.G {θ' | beta M μ θ' α ≤ CAC.bidT M μ θ t α}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hqk : (M.G {θ' | beta M μ θ' α ≤ CAC.bidT M μ θ t α}).toReal ^ (M.n - 1) ≤ 1 :=
      pow_le_one₀ hq0 hq1
    have hqk0 := pow_nonneg hq0 (M.n - 1)
    simp only [hΨ]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 hqk0)]
      calc CAC.bidT M μ θ t α * _ ≤ CAC.bidT M μ θ t α * 1 :=
            mul_le_mul_of_nonneg_left hqk hb.1
        _ ≤ omega M := by rw [mul_one]; exact hb.2.trans hvle
    · simpa using CAC.omega_nonneg M hM
  have hres_ae : ∀ᵐ α ∂M.F, val θ α / (1 + ts) ≠ M.r α := by
    rw [ae_iff]; simpa using ThetaP_reserve M hθ hts
  have hcont : ∀ᵐ α ∂M.F, ContinuousWithinAt (fun t => Ψ t α) (Set.Ici 0) ts := by
    filter_upwards [hFA, atomless_ae M hM μ hμ, hres_ae] with α hα hatom hres
    have hX : Measurable (fun θ' : (Fin M.d → ℝ) × ℝ => paced μ θ' α) := by
      unfold paced
      exact ((CAC.measurable_val M.d).comp (measurable_id.prodMk measurable_const)).div
        (measurable_const.add hμ.1)
    have hX0 := CAC.paced_nonneg_ae M hM μ hμ hα
    have hpc := L1Aux.psi_continuousAt (ν := M.G) (X := fun θ' => paced μ θ' α) (M.n - 1)
      (M.r α) hk hX hatom hX0 hres
    have hvc : ContinuousAt (fun t : ℝ => val θ α / (1 + t)) ts :=
      continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith)
    have := (ContinuousAt.comp (f := fun t : ℝ => val θ α / (1 + t)) (x := ts) hpc hvc).continuousWithinAt
      (s := Set.Ici 0)
    exact this
  have hmain : ContinuousWithinAt (fun t => ∫ α, Ψ t α ∂M.F) (Set.Ici 0) ts :=
    continuousWithinAt_of_dominated
      (eventually_nhdsWithin_of_forall fun t ht => hmeas t ht)
      (eventually_nhdsWithin_of_forall fun t ht => hbound t ht)
      (integrable_const _) hcont
  exact hmain.congr (fun t ht => hpayeq t ht) (hpayeq ts hts)

open Classical in
lemma affine_explicit (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M μ) b) (s : ℝ) :
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + s) * b ω.1 else 0) ∂P M =
      (∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 else 0) ∂P M) -
        (1 + s) * ∫ ω, (if wins M (beta M μ) b ω then b ω.1 else 0) ∂P M := by
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hW := CAC.measurableSet_wins M hM μ hμ b hb.1
  have hv : Measurable (fun ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) =>
      val θ ω.1) :=
    (CAC.measurable_val M.d).comp (measurable_const.prodMk measurable_fst)
  have hint1 : Integrable (fun ω => if wins M (beta M μ) b ω then val θ ω.1 else 0) (P M) := by
    refine Integrable.mono' (integrable_const (omega M)) ?_ ?_
    · exact (Measurable.ite hW hv measurable_const).aestronglyMeasurable
    · filter_upwards [CAC.ae_A M hM] with ω hω
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (CAC.val_nonneg M hM hθ hω)]
        exact CAC.val_le_omega M hM hθ hω
      · simpa using CAC.omega_nonneg M hM
  rw [← integral_const_mul, ← integral_sub hint1 (hb.2.2.const_mul _)]
  congr 1
  funext ω
  split_ifs <;> ring

open Classical in
theorem main (M : Model) (hM : M.Standing) :
    ∃ Θ' ⊆ Theta M, MeasurableSet Θ' ∧ M.G Θ' = 1 ∧
      ∀ μ : (Fin M.d → ℝ) × ℝ → ℝ, IsPacing M μ → ∀ θ ∈ Θ', ∀ tstar : ℝ, 0 ≤ tstar →
        IsMinOn (qDual M μ θ) (Set.Ici 0) tstar →
          IsOptimal M (beta M μ) θ (fun α => sigma M μ α (val θ α / (1 + tstar))) := by
  refine ⟨ThetaP M, ThetaP_sub M, ThetaP_meas M hM, ThetaP_full M hM, ?_⟩
  intro μ hμ θ hθ ts hts hmin
  have hθΘ : θ ∈ Theta M := ThetaP_sub M hθ
  set B := θ.2
  -- notation
  let V : ℝ → ((Fin M.d → ℝ) → ℝ) → ℝ := fun s b =>
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + s) * b ω.1 else 0) ∂P M
  let Aof : ((Fin M.d → ℝ) → ℝ) → ℝ := fun b =>
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 else 0) ∂P M
  let Pof : ((Fin M.d → ℝ) → ℝ) → ℝ := fun b =>
    ∫ ω, (if wins M (beta M μ) b ω then b ω.1 else 0) ∂P M
  have hadm : ∀ t, 0 ≤ t → Admissible M (beta M μ) (CAC.bidT M μ θ t) :=
    fun t ht => (lemma_1 M hM μ hμ θ hθΘ t ht).1
  have haff : ∀ b, Admissible M (beta M μ) b → ∀ s, V s b = Aof b - (1 + s) * Pof b :=
    fun b hb s => affine_explicit M hM μ hμ.1 hθΘ b hb s
  -- value of the dual function
  have hq : ∀ t, 0 ≤ t → qDual M μ θ t = V t (CAC.bidT M μ θ t) + t * B := by
    intro t ht
    rw [CAC.qDual_eq]
    congr 1
    have ht1 : 0 < 1 + t := by linarith
    apply IsGreatest.csSup_eq
    refine ⟨⟨CAC.bidT M μ θ t, hadm t ht, rfl⟩, ?_⟩
    rintro v ⟨b, hb, rfl⟩
    show V t b ≤ V t (CAC.bidT M μ θ t)
    simp only [V]
    rw [CAC.integral_scale M μ θ ht1, CAC.integral_scale M μ θ ht1]
    exact mul_le_mul_of_nonneg_left ((lemma_1 M hM μ hμ θ hθΘ t ht).2 b hb) ht1.le
  have hqge : ∀ s, 0 ≤ s → ∀ b, Admissible M (beta M μ) b → V s b + s * B ≤ qDual M μ θ s := by
    intro s hs b hb
    rw [CAC.qDual_eq]
    have := le_csSup (CAC.Sset_bdd M hM μ hθΘ (show 0 ≤ 1 + s by linarith)).1
      (show V s b ∈ CAC.Sset M μ θ s from ⟨b, hb, rfl⟩)
    linarith
  have hpay : ∀ t, pay M μ θ t = Pof (CAC.bidT M μ θ t) := fun t => rfl
  set g : ℝ → ℝ := fun t => B - pay M μ θ t with hg
  -- subgradient inequality
  have hsub : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → qDual M μ θ t + (s - t) * g t ≤ qDual M μ θ s := by
    intro s hs t ht
    have h1 := hqge s hs _ (hadm t ht)
    rw [hq t ht, haff _ (hadm t ht) t]
    rw [haff _ (hadm t ht) s] at h1
    simp only [hg, hpay]
    nlinarith
  have hminv : ∀ s, 0 ≤ s → qDual M μ θ ts ≤ qDual M μ θ s := fun s hs => hmin hs
  have hright : ∀ s, ts < s → 0 ≤ g s := by
    intro s hs
    have h1 := hsub ts hts s (by linarith)
    have h2 := hminv s (by linarith)
    have : (ts - s) * g s ≤ 0 := by linarith
    nlinarith
  have hleft : ∀ s, 0 ≤ s → s < ts → g s ≤ 0 := by
    intro s hs0 hs
    have h1 := hsub ts hts s hs0
    have h2 := hminv s hs0
    have : (ts - s) * g s ≤ 0 := by linarith
    nlinarith
  have hgc : ContinuousWithinAt g (Set.Ici 0) ts :=
    continuousWithinAt_const.sub (pay_cont M hM μ hμ hθ hts)
  have hg0 : 0 ≤ g ts := by
    have hc : Tendsto g (𝓝[>] ts) (𝓝 (g ts)) :=
      hgc.mono_left (nhdsWithin_mono _ (fun x (hx : ts < x) => show (0 : ℝ) ≤ x by linarith))
    exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun s hs => hright s hs)
  have hcs : ts * g ts = 0 := by
    rcases eq_or_lt_of_le hts with h | h
    · rw [← h, zero_mul]
    · have hc : Tendsto g (𝓝[Set.Ioo 0 ts] ts) (𝓝 (g ts)) :=
        hgc.mono_left (nhdsWithin_mono _ (fun x hx => show (0 : ℝ) ≤ x from hx.1.le))
      haveI : (𝓝[Set.Ioo 0 ts] ts).NeBot := by
        rw [nhdsWithin_Ioo_eq_nhdsLT h]; infer_instance
      have hle : g ts ≤ 0 :=
        le_of_tendsto hc (eventually_nhdsWithin_of_forall fun s hs => hleft s hs.1.le hs.2)
      have : g ts = 0 := le_antisymm hle hg0
      rw [this, mul_zero]
  -- assemble
  have hσ : (fun α => sigma M μ α (val θ α / (1 + ts))) = CAC.bidT M μ θ ts := rfl
  rw [hσ]
  have hutil : ∀ b, utility M (beta M μ) θ b = V 0 b := by
    intro b
    simp only [V, utility]
    congr 1
    funext ω
    split_ifs <;> ring
  refine ⟨hadm ts hts, ?_, ?_⟩
  · show Pof (CAC.bidT M μ θ ts) ≤ B
    have : g ts = B - Pof (CAC.bidT M μ θ ts) := rfl
    linarith
  · intro b hb hbB
    have hbB' : Pof b ≤ B := hbB
    rw [hutil, hutil, haff b hb 0, haff _ (hadm ts hts) 0]
    have hl := (lemma_1 M hM μ hμ θ hθΘ ts hts).2 b hb
    have ht1 : 0 < 1 + ts := by linarith
    have hV : V ts b ≤ V ts (CAC.bidT M μ θ ts) := by
      simp only [V]
      rw [CAC.integral_scale M μ θ ht1, CAC.integral_scale M μ θ ht1]
      exact mul_le_mul_of_nonneg_left hl ht1.le
    rw [haff b hb ts, haff _ (hadm ts hts) ts] at hV
    have hgdef : g ts = B - Pof (CAC.bidT M μ θ ts) := rfl
    have : ts * (B - Pof b) ≥ 0 := mul_nonneg hts (by linarith)
    nlinarith

end P1


theorem solution (M : Model) (hM : M.Standing) :
    ∃ Θ' ⊆ Theta M, MeasurableSet Θ' ∧ M.G Θ' = 1 ∧
      ∀ μ : (Fin M.d → ℝ) × ℝ → ℝ, IsPacing M μ → ∀ θ ∈ Θ', ∀ tstar : ℝ, 0 ≤ tstar →
        IsMinOn (qDual M μ θ) (Set.Ici 0) tstar →
          IsOptimal M (beta M μ) θ (fun α => sigma M μ α (val θ α / (1 + tstar))) :=
  P1.main M hM
