-- Prove2me | solution 1 for ContextualAuctions.Existence.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T07:21:23.566933+00:00
-- url     : https://prove2.me/submissions/1eee1134-9b8f-4538-9cf4-c67d506436bc

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint
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

open Classical in
theorem value_eq (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hX0 : ν {ω | X ω < 0} = 0) {v : ℝ} (hv : 0 ≤ v)
    :
      (if r ≤ sig k r (Fd ν X) v then (v - sig k r (Fd ν X) v) *
        (ν {ω | sig k r (Fd ν X) (X ω) ≤ sig k r (Fd ν X) v}).toReal ^ k else 0) =
      (if v < r then 0 else Ik k r (Fd ν X) v) := by
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
  have hup : ∀ y, (if r ≤ y then (v - y) * qf y ^ k else 0) ≤ LB := by
    intro y
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
  exact le_antisymm (hup _) hlow

end Meas

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


open MeasureTheory ContextualAuctions.Existence

namespace CAC

/-- Lemma 1 gives the closed form of the dual function. -/
lemma qDual_formula (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ t) :
    qDual M μ θ t = (1 + t) * lagr M μ θ t (bidT M μ θ t) + t * θ.2 := by
  obtain ⟨hadm, hmax⟩ := lemma_1 M hM μ hμ θ hθ t ht
  have ht1 : 0 < 1 + t := by linarith
  rw [qDual_eq]
  congr 1
  apply IsGreatest.csSup_eq
  refine ⟨⟨bidT M μ θ t, hadm, (integral_scale M μ θ ht1 _).symm⟩, ?_⟩
  rintro v ⟨b, hb, rfl⟩
  rw [integral_scale M μ θ ht1]
  exact mul_le_mul_of_nonneg_left (hmax b hb) ht1.le

lemma measurable_Lam (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) :
    Measurable (fun p : ((Fin M.d → ℝ) × ℝ) × ℝ => lagr M μ p.1 p.2 (bidT M μ p.1 p.2)) := by
  classical
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hb : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
      ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) =>
        bidT M μ q.1.1 q.1.2 q.2.1) := by
    unfold bidT
    have hv : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
        ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) => val q.1.1 q.2.1) :=
      (measurable_val M.d).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
    exact (measurable_sigma M hM μ hμ).comp ((measurable_fst.comp measurable_snd).prodMk
      (hv.div (measurable_const.add (measurable_snd.comp measurable_fst))))
  have hW : MeasurableSet {q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
      ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) |
        wins M (beta M μ) (bidT M μ q.1.1 q.1.2) q.2} := by
    unfold wins
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun i => ?_)
    · exact measurableSet_le (hM.measurable_r.comp (measurable_fst.comp measurable_snd)) hb
    · refine measurableSet_le ?_ hb
      have hm : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
          ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) => (q.2.2 i, q.2.1)) := by
        fun_prop
      exact (measurable_beta M hM μ hμ).comp hm
  have hg : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
      ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) =>
        if wins M (beta M μ) (bidT M μ q.1.1 q.1.2) q.2 then
          val q.1.1 q.2.1 / (1 + q.1.2) - bidT M μ q.1.1 q.1.2 q.2.1 else 0) := by
    refine Measurable.ite hW ?_ measurable_const
    refine Measurable.sub ?_ hb
    exact ((measurable_val M.d).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).div
      (measurable_const.add (measurable_snd.comp measurable_fst))
  have := (hg.stronglyMeasurable).integral_prod_right' (ν := P M)
  exact this.measurable

lemma convex_q (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) :
    ConvexOn ℝ (Set.Ioi (-1)) (qDual M μ θ) := by
  refine ⟨convex_Ioi _, fun x hx y hy a c ha hc hac => ?_⟩
  have hx' : 0 ≤ 1 + x := by have : (-1 : ℝ) < x := hx; linarith
  have hy' : 0 ≤ 1 + y := by have : (-1 : ℝ) < y := hy; linarith
  have hz' : 0 ≤ 1 + (a • x + c • y) := by
    simp only [smul_eq_mul]; nlinarith
  simp only [qDual_eq, smul_eq_mul]
  have key : sSup (Sset M μ θ (a * x + c * y)) ≤
      a * sSup (Sset M μ θ x) + c * sSup (Sset M μ θ y) := by
    apply csSup_le (Sset_bdd M hM μ hθ (by simpa using hz')).2.1
    rintro v ⟨b, hb, rfl⟩
    obtain ⟨A, Pb, h⟩ := affine_elem M hM μ hμ hθ b hb
    have h1 : A - (1 + x) * Pb ≤ sSup (Sset M μ θ x) :=
      le_csSup (Sset_bdd M hM μ hθ hx').1 ⟨b, hb, (h x).symm⟩
    have h2 : A - (1 + y) * Pb ≤ sSup (Sset M μ θ y) :=
      le_csSup (Sset_bdd M hM μ hθ hy').1 ⟨b, hb, (h y).symm⟩
    rw [h]
    have : A - (1 + (a * x + c * y)) * Pb = a * (A - (1 + x) * Pb) + c * (A - (1 + y) * Pb) := by
      have hc' : c = 1 - a := by linarith
      subst hc'; ring
    rw [this]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hc)
  nlinarith

lemma ell_spec (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) :
    ell M μ θ ∈ Set.Icc 0 (omega M / M.Bmin) ∧
      IsMinOn (qDual M μ θ) (Set.Icc 0 (omega M / M.Bmin)) (ell M μ θ) := by
  set c := omega M / M.Bmin with hc_def
  have hc : 0 ≤ c := div_nonneg (omega_nonneg M hM) hM.Bmin_pos.le
  have hcont : ContinuousOn (qDual M μ θ) (Set.Icc 0 c) :=
    ((convex_q M hM μ hμ hθ).continuousOn isOpen_Ioi).mono
      (fun s hs => show (-1 : ℝ) < s by linarith [hs.1])
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hc) hcont
  set A := {s ∈ Set.Icc 0 c | IsMinOn (qDual M μ θ) (Set.Icc 0 c) s} with hA_def
  have hA : A = Set.Icc 0 c ∩ qDual M μ θ ⁻¹' Set.Iic (qDual M μ θ s0) := by
    ext s
    constructor
    · rintro ⟨hs, hm⟩
      exact ⟨hs, hm hs0⟩
    · rintro ⟨hs, hle⟩
      exact ⟨hs, fun x hx => show qDual M μ θ s ≤ qDual M μ θ x from le_trans hle (hmin hx)⟩
  have hclosed : IsClosed A := by
    rw [hA]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hmem : sInf A ∈ A :=
    hclosed.csInf_mem ⟨s0, hs0, hmin⟩ ⟨0, fun s hs => hs.1.1⟩
  exact hmem

lemma integrable_q (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) (ν : (Fin M.d → ℝ) × ℝ → ℝ) (hν : Measurable ν)
    (hνr : ∀ θ ∈ Theta M, ν θ ∈ Set.Icc 0 (omega M / M.Bmin)) :
    Integrable (fun θ => qDual M μ θ (ν θ)) M.G := by
  have := hM.probG
  have hΘ : ∀ᵐ θ ∂M.G, θ ∈ Theta M := ae_iff.mpr hM.G_Theta
  set c := omega M / M.Bmin
  have hmeas : Measurable (fun θ : (Fin M.d → ℝ) × ℝ =>
      (1 + ν θ) * lagr M μ θ (ν θ) (bidT M μ θ (ν θ)) + ν θ * θ.2) := by
    have h1 := (measurable_Lam M hM μ hμ.1).comp (measurable_id.prodMk hν)
    exact ((measurable_const.add hν).mul h1).add (hν.mul measurable_snd)
  refine Integrable.mono' (integrable_const (omega M + c * M.U)) ?_ ?_
  · refine hmeas.aestronglyMeasurable.congr ?_
    filter_upwards [hΘ] with θ hθ
    exact (qDual_formula M hM μ hμ hθ (hνr θ hθ).1).symm
  · filter_upwards [hΘ] with θ hθ
    have ht := hνr θ hθ
    have ht1 : 0 ≤ 1 + ν θ := by linarith [ht.1]
    have h0 := Sset_zero_nonneg M hM μ hθ ht1
    have h1 := (Sset_bdd M hM μ hθ ht1).2.2
    have hB : 0 < θ.2 := lt_trans hM.Bmin_pos hθ.2.1
    have hBU : θ.2 ≤ M.U := hθ.2.2.le
    have hc : 0 ≤ c := div_nonneg (omega_nonneg M hM) hM.Bmin_pos.le
    have e1 : 0 ≤ ν θ * θ.2 := mul_nonneg ht.1 hB.le
    have e2 : ν θ * θ.2 ≤ c * M.U :=
      mul_le_mul ht.2 hBU hB.le hc
    rw [qDual_eq, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

end CAC


open MeasureTheory ContextualAuctions.Existence

namespace L1Aux

variable {k : ℕ} {r : ℝ} {Fr : ℝ → ℝ}

/-- `H` truncated below the reserve -/
noncomputable def Ht (k : ℕ) (r : ℝ) (Fr : ℝ → ℝ) (s : ℝ) : ℝ := if s < r then 0 else Hk k Fr s

/-- the optimal Lagrangian value at paced value `v` -/
noncomputable def LBf (k : ℕ) (r : ℝ) (Fr : ℝ → ℝ) (v : ℝ) : ℝ := if v < r then 0 else Ik k r Fr v

lemma Ht_mono (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) : Monotone (Ht k r Fr) := by
  intro a b hab
  unfold Ht
  split_ifs with h1 h2 h2
  · exact le_refl 0
  · exact Hk_nn k hnn b
  · exact absurd (lt_of_le_of_lt hab h2) h1
  · exact Hk_mono k hmono hnn hab

lemma LBf_eq_int (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) (hneg : ∀ x < 0, Fr x = 0)
    (hk : 1 ≤ k) {v : ℝ} (hv : 0 ≤ v) : LBf k r Fr v = ∫ s in (0 : ℝ)..v, Ht k r Fr s := by
  have hHt0 : ∀ s, s < r → Ht k r Fr s = 0 := fun s hs => by unfold Ht; rw [if_pos hs]
  have hneg' : ∀ s, s < 0 → Hk k Fr s = 0 := fun s hs => by
    unfold Hk; rw [hneg s hs]; exact zero_pow (by omega)
  unfold LBf
  by_cases hvr : v < r
  · rw [if_pos hvr]
    symm
    apply intervalIntegral.integral_zero_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le hv] at hs
    exact hHt0 s (lt_of_le_of_lt hs.2 hvr)
  · rw [if_neg hvr]
    have hrv : r ≤ v := not_lt.mp hvr
    unfold Ik
    rcases le_or_gt 0 r with hr | hr
    · rw [← intervalIntegral.integral_add_adjacent_intervals
        ((Ht_mono hmono hnn).intervalIntegrable (a := 0) (b := r))
        ((Ht_mono hmono hnn).intervalIntegrable (a := r) (b := v))]
      have h1 : ∫ s in (0 : ℝ)..r, Ht k r Fr s = 0 := by
        apply intervalIntegral.integral_zero_ae
        have : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ r := by
          simp [ae_iff, measure_singleton]
        filter_upwards [this] with s hsr hs
        rw [Set.uIoc_of_le hr] at hs
        exact hHt0 s (lt_of_le_of_ne hs.2 hsr)
      rw [h1, zero_add]
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      rw [Set.uIoc_of_le hrv] at hs
      unfold Ht; rw [if_neg (not_lt.mpr hs.1.le)]
    · -- r < 0
      have h1 : ∫ s in r..(0 : ℝ), Hk k Fr s = 0 := by
        apply intervalIntegral.integral_zero_ae
        have : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
          simp [ae_iff, measure_singleton]
        filter_upwards [this] with s hs0 hs
        rw [Set.uIoc_of_le hr.le] at hs
        exact hneg' s (lt_of_le_of_ne hs.2 hs0)
      rw [← intervalIntegral.integral_add_adjacent_intervals (Hk_ii k hmono hnn r 0)
        (Hk_ii k hmono hnn 0 v), h1, zero_add]
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      rw [Set.uIoc_of_le hv] at hs
      unfold Ht; rw [if_neg (not_lt.mpr (le_trans hr.le hs.1.le))]

lemma kmono (hmono : Monotone Fr) (hnn : ∀ x, 0 ≤ Fr x) (hneg : ∀ x < 0, Fr x = 0)
    (hk : 1 ≤ k) {x x' : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x') {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁)
    (ht : t₁ ≤ t₂) :
    (1 + t₂) * (LBf k r Fr (x' / (1 + t₂)) - LBf k r Fr (x / (1 + t₂))) ≤
      (1 + t₁) * (LBf k r Fr (x' / (1 + t₁)) - LBf k r Fr (x / (1 + t₁))) := by
  have key : ∀ t, 0 ≤ t → (1 + t) * (LBf k r Fr (x' / (1 + t)) - LBf k r Fr (x / (1 + t))) =
      ∫ u in x..x', Ht k r Fr (u / (1 + t)) := by
    intro t ht0
    have hpos : 0 < 1 + t := by linarith
    rw [LBf_eq_int hmono hnn hneg hk (div_nonneg (by linarith) hpos.le),
      LBf_eq_int hmono hnn hneg hk (div_nonneg hx hpos.le)]
    rw [intervalIntegral.integral_comp_div (Ht k r Fr) hpos.ne', smul_eq_mul]
    have hii := fun a b => (Ht_mono (k := k) (r := r) hmono hnn).intervalIntegrable (μ := volume)
      (a := a) (b := b)
    rw [intervalIntegral.integral_interval_sub_left (hii 0 _) (hii 0 _)]
  rw [key t₂ (le_trans ht₁ ht), key t₁ ht₁]
  apply intervalIntegral.integral_mono_on hxx
  · exact (Monotone.comp (Ht_mono (k := k) (r := r) hmono hnn) (fun a b (hab : a ≤ b) =>
      div_le_div_of_nonneg_right hab (by linarith : (0:ℝ) ≤ 1 + t₂))).intervalIntegrable
  · exact (Monotone.comp (Ht_mono (k := k) (r := r) hmono hnn) (fun a b (hab : a ≤ b) =>
      div_le_div_of_nonneg_right hab (by linarith : (0:ℝ) ≤ 1 + t₁))).intervalIntegrable
  · intro u hu
    apply Ht_mono hmono hnn
    have hu0 : 0 ≤ u := le_trans hx hu.1
    exact div_le_div_of_nonneg_left hu0 (by linarith) (by linarith)

end L1Aux

namespace L2

open Classical in
lemma Phi_formula (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ t) :
    sSup (CAC.Sset M μ θ t) = (1 + t) * ∫ α, L1Aux.LBf (M.n - 1) (M.r α)
      (L1Aux.Fd M.G (fun θ' => paced μ θ' α)) (val θ α / (1 + t)) ∂M.F ∧
    Integrable (fun α => L1Aux.LBf (M.n - 1) (M.r α)
      (L1Aux.Fd M.G (fun θ' => paced μ θ' α)) (val θ α / (1 + t))) M.F := by
  have := hM.probG
  have := hM.probF
  have : SigmaFinite M.G := inferInstance
  have : SFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := inferInstance
  have hk : 1 ≤ M.n - 1 := by have := hM.two_le_n; omega
  have hq := CAC.qDual_formula M hM μ hμ hθ ht
  rw [CAC.qDual_eq] at hq
  have hS : sSup (CAC.Sset M μ θ t) = (1 + t) * lagr M μ θ t (CAC.bidT M μ θ t) := by linarith
  set v : (Fin M.d → ℝ) → ℝ := fun α => val θ α / (1 + t) with hv_def
  have hadm := (lemma_1 M hM μ hμ θ hθ t ht).1
  have hg : Integrable (fun ω => if wins M (beta M μ) (CAC.bidT M μ θ t) ω then
      val θ ω.1 / (1 + t) - CAC.bidT M μ θ t ω.1 else 0) (P M) :=
    CAC.integrable_g M hM μ hμ hθ ht _ hadm
  have hP : P M = M.F.prod (Measure.pi fun _ : Fin (M.n - 1) => M.G) := rfl
  have hFA : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.F_A
  have hpt : ∀ᵐ α ∂M.F, (if M.r α ≤ CAC.bidT M μ θ t α then (v α - CAC.bidT M μ θ t α) *
      (M.G {θ' | beta M μ θ' α ≤ CAC.bidT M μ θ t α}).toReal ^ (M.n - 1) else 0) =
      L1Aux.LBf (M.n - 1) (M.r α) (L1Aux.Fd M.G (fun θ' => paced μ θ' α)) (v α) := by
    filter_upwards [hFA] with α hα
    have hv0 : 0 ≤ v α := div_nonneg (CAC.val_nonneg M hM hθ hα) (by linarith)
    exact L1Aux.value_eq (ν := M.G) (X := fun θ' => paced μ θ' α) (M.n - 1) hk (M.r α)
      (CAC.paced_nonneg_ae M hM μ hμ hα) hv0
  have hlagr : lagr M μ θ t (CAC.bidT M μ θ t) = ∫ α, (if M.r α ≤ CAC.bidT M μ θ t α then
      (v α - CAC.bidT M μ θ t α) *
      (M.G {θ' | beta M μ θ' α ≤ CAC.bidT M μ θ t α}).toReal ^ (M.n - 1) else 0) ∂M.F := by
    unfold lagr
    rw [hP] at hg ⊢
    rw [integral_prod _ hg]
    congr 1
    funext α
    exact CAC.inner_integral M hM μ hμ _ v α
  have hint : Integrable (fun α => (if M.r α ≤ CAC.bidT M μ θ t α then
      (v α - CAC.bidT M μ θ t α) *
      (M.G {θ' | beta M μ θ' α ≤ CAC.bidT M μ θ t α}).toReal ^ (M.n - 1) else 0)) M.F := by
    rw [hP] at hg
    refine hg.integral_prod_left.congr (Filter.Eventually.of_forall fun α => ?_)
    exact CAC.inner_integral M hM μ hμ _ v α
  refine ⟨?_, hint.congr hpt⟩
  rw [hS, hlagr, integral_congr_ae hpt]

lemma D_anti (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) {θ θ' : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) (hθ' : θ' ∈ Theta M)
    (hle : ∀ α ∈ M.A, val θ α ≤ val θ' α) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) :
    sSup (CAC.Sset M μ θ' t₂) - sSup (CAC.Sset M μ θ t₂) ≤
      sSup (CAC.Sset M μ θ' t₁) - sSup (CAC.Sset M μ θ t₁) := by
  have := hM.probG
  have hk : 1 ≤ M.n - 1 := by have := hM.two_le_n; omega
  have ht₂ : 0 ≤ t₂ := le_trans ht₁ ht
  obtain ⟨e1, i1⟩ := Phi_formula M hM μ hμ hθ' ht₂
  obtain ⟨e2, i2⟩ := Phi_formula M hM μ hμ hθ ht₂
  obtain ⟨e3, i3⟩ := Phi_formula M hM μ hμ hθ' ht₁
  obtain ⟨e4, i4⟩ := Phi_formula M hM μ hμ hθ ht₁
  rw [e1, e2, e3, e4, ← mul_sub, ← mul_sub, ← integral_sub i1 i2, ← integral_sub i3 i4,
    ← integral_const_mul, ← integral_const_mul]
  apply integral_mono_ae ((i1.sub i2).const_mul _) ((i3.sub i4).const_mul _)
  have hFA : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.F_A
  filter_upwards [hFA] with α hα
  have hX0 := CAC.paced_nonneg_ae M hM μ hμ hα
  exact L1Aux.kmono (L1Aux.Fd_mono (ν := M.G) (X := fun θ' => paced μ θ' α))
    (L1Aux.Fd_nn (ν := M.G) (X := fun θ' => paced μ θ' α))
    (L1Aux.Fd_neg (ν := M.G) (X := fun θ' => paced μ θ' α) hX0) hk
    (CAC.val_nonneg M hM hθ hα) (hle α hα) ht₁ ht

lemma ell_le_of_min (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc 0 (omega M / M.Bmin))
    (hmin : IsMinOn (qDual M μ θ) (Set.Icc 0 (omega M / M.Bmin)) s) : ell M μ θ ≤ s :=
  csInf_le ⟨0, fun _ h => h.1.1⟩ ⟨hs, hmin⟩

end L2

open L2 in
theorem solution (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    (hμr : ∀ θ ∈ Theta M, μ θ ∈ Set.Icc 0 (omega M / M.Bmin)) :
    (∀ θ ∈ Theta M, ∀ θ' ∈ Theta M, ∀ i : Fin M.d, θ.2 = θ'.2 → (∀ j, j ≠ i → θ.1 j = θ'.1 j) →
        θ.1 i ≤ θ'.1 i → ell M μ θ ≤ ell M μ θ') ∧
      (∀ θ ∈ Theta M, ∀ θ' ∈ Theta M, θ.1 = θ'.1 → θ.2 ≤ θ'.2 → ell M μ θ' ≤ ell M μ θ) := by
  constructor
  · intro θ hθ θ' hθ' i hB hj hi
    have hle : ∀ α ∈ M.A, val θ α ≤ val θ' α := by
      intro α hα
      unfold val
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · subst hji
        exact mul_le_mul_of_nonneg_right hi (hM.A_pos hα j).le
      · rw [hj j hji]
    obtain ⟨hs, hmin⟩ := CAC.ell_spec M hM μ hμ.1 hθ
    obtain ⟨hs', hmin'⟩ := CAC.ell_spec M hM μ hμ.1 hθ'
    by_contra hcon
    push Not at hcon
    -- ℓ' < ℓ: show ℓ' minimizes for θ
    apply absurd (ell_le_of_min M μ θ hs' ?_) (not_le.mpr hcon)
    intro s hs_mem
    show qDual M μ θ (ell M μ θ') ≤ qDual M μ θ s
    have hD := D_anti M hM μ hμ hθ hθ' hle hs'.1 hcon.le
    have h1 : qDual M μ θ' (ell M μ θ') ≤ qDual M μ θ' (ell M μ θ) := hmin' hs
    have h2 : qDual M μ θ (ell M μ θ) ≤ qDual M μ θ s := hmin hs_mem
    simp only [CAC.qDual_eq] at h1 h2 ⊢
    rw [hB] at h2 ⊢
    linarith
  · intro θ hθ θ' hθ' h1 h2
    have hval : ∀ α, val θ' α = val θ α := by intro α; unfold val; rw [h1]
    have hS : ∀ t, CAC.Sset M μ θ' t = CAC.Sset M μ θ t := by
      intro t; unfold CAC.Sset; simp only [hval]
    obtain ⟨hs, hmin⟩ := CAC.ell_spec M hM μ hμ.1 hθ
    obtain ⟨hs', hmin'⟩ := CAC.ell_spec M hM μ hμ.1 hθ'
    by_contra hcon
    push Not at hcon
    apply absurd (ell_le_of_min M μ θ' hs ?_) (not_le.mpr hcon)
    intro s hs_mem
    show qDual M μ θ' (ell M μ θ) ≤ qDual M μ θ' s
    have e1 : qDual M μ θ (ell M μ θ) ≤ qDual M μ θ (ell M μ θ') := hmin hs'
    have e2 : qDual M μ θ' (ell M μ θ') ≤ qDual M μ θ' s := hmin' hs_mem
    simp only [CAC.qDual_eq] at e1 e2 ⊢
    rw [hS] at e2 ⊢
    have : ell M μ θ * (θ'.2 - θ.2) ≤ ell M μ θ' * (θ'.2 - θ.2) :=
      mul_le_mul_of_nonneg_right hcon.le (by linarith)
    nlinarith
