-- Prove2me | solution 1 for ContextualAuctions.Existence.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T07:42:11.722472+00:00
-- url     : https://prove2.me/submissions/ddbaa177-c03b-40b7-9aeb-4c4d55085ce1

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint
import Theorems.Thm_ContextualAuctions_Existence_lemma_1
import Theorems.Thm_ContextualAuctions_Existence_lemma_2

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


open MeasureTheory Filter Topology Set

namespace L3Aux

/-- Monotone case: `|∫_p^q u g'| ≤ c`. -/
lemma mono_case {a b c α β : ℝ} {u g : ℝ → ℝ} (hu : MonotoneOn u (Ioo a b))
    (huc : ∀ s ∈ Ioo a b, 0 ≤ u s ∧ u s ≤ c) (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ s, s ∉ Icc α β → g s = 0) (haα : a < α) (hαβ : α ≤ β) (hβb : β < b)
    (hg1 : ∀ s, |g s| ≤ 1) :
    |∫ s in (α - min (α - a) (b - β) / 2)..(β + min (α - a) (b - β) / 2), u s * deriv g s| ≤ c := by
  set δ := min (α - a) (b - β) / 2 with hδ
  have hδpos : 0 < δ := by
    have : 0 < min (α - a) (b - β) := lt_min (by linarith) (by linarith)
    linarith
  have hδ1 : 2 * δ ≤ α - a := by
    have := min_le_left (α - a) (b - β); linarith
  have hδ2 : 2 * δ ≤ b - β := by
    have := min_le_right (α - a) (b - β); linarith
  set p := α - δ
  set q := β + δ
  have hpq : p ≤ q := by linarith
  have hc0 : 0 ≤ c := by
    have := huc ((a + b) / 2) ⟨by linarith, by linarith⟩
    linarith [this.1, this.2]
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  -- integrability of `u` on subintervals of `(a, b)`
  have huii : ∀ x y, x ∈ Ioo a b → y ∈ Ioo a b → IntervalIntegrable u volume x y := by
    intro x y hx hy
    apply MonotoneOn.intervalIntegrable
    apply hu.mono
    intro z hz
    rw [Set.mem_uIcc] at hz
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 hy.2⟩
    · exact ⟨lt_of_lt_of_le hy.1 h1, lt_of_le_of_lt h2 hx.2⟩
  have hmem : ∀ h, 0 ≤ h → h < δ → ∀ t ∈ Icc (p - h) q, t ∈ Ioo a b := by
    intro h h0 hh t ht
    constructor <;> linarith [ht.1, ht.2]
  -- bound on the derivative
  obtain ⟨Md, hMd⟩ := (isCompact_Icc (a := p) (b := q + δ)).exists_bound_of_continuousOn
    hg'c.continuousOn
  have hMd0 : 0 ≤ Md := le_trans (norm_nonneg _) (hMd p ⟨le_refl p, by linarith⟩)
  -- difference quotients
  set D : ℝ → ℝ := fun h => ∫ t in p..q, u t * (h⁻¹ • (g (t + h) - g t)) with hD
  have hclaim1 : ∀ h, 0 < h → h < δ → |D h| ≤ c := by
    intro h h0 hh
    have hui : IntervalIntegrable u volume p q := huii p q (hmem h h0.le hh p ⟨by linarith, hpq⟩)
      (hmem h h0.le hh q ⟨by linarith, le_refl q⟩)
    have hush : IntervalIntegrable (fun t => u (t - h)) volume p q := by
      have := huii (p - h) (q - h) (hmem h h0.le hh (p - h) ⟨le_refl _, by linarith⟩)
        (hmem h h0.le hh (q - h) ⟨by linarith, by linarith⟩)
      have h2 := this.comp_sub_right h
      simpa using h2
    -- shift the first integral
    have hshift : ∫ t in p..q, u t * g (t + h) = ∫ t in p..q, u (t - h) * g t := by
      have e1 : ∫ t in p..q, u t * g (t + h) = ∫ t in p + h..q + h, u (t - h) * g t := by
        rw [← intervalIntegral.integral_comp_add_right (fun t => u (t - h) * g t) h]
        simp
      rw [e1]
      -- both sides: the integrand vanishes off `[α, β]`
      have hz1 : ∫ t in q..q + h, u (t - h) * g t = 0 := by
        apply intervalIntegral.integral_zero_ae
        filter_upwards with t ht
        rw [Set.uIoc_of_le (by linarith)] at ht
        rw [hsupp t (fun h' => by linarith [h'.2, ht.1]), mul_zero]
      have hz2 : ∫ t in p..p + h, u (t - h) * g t = 0 := by
        apply intervalIntegral.integral_zero_ae
        filter_upwards with t ht
        rw [Set.uIoc_of_le (by linarith)] at ht
        rw [hsupp t (fun h' => by linarith [h'.1, ht.2]), mul_zero]
      have hii : ∀ x y, x ∈ Icc p (q + h) → y ∈ Icc p (q + h) →
          IntervalIntegrable (fun t => u (t - h) * g t) volume x y := by
        intro x y hx hy
        have hu' : IntervalIntegrable (fun t => u (t - h)) volume x y := by
          have := huii (x - h) (y - h) ⟨by linarith [hx.1], by linarith [hx.2]⟩
            ⟨by linarith [hy.1], by linarith [hy.2]⟩
          simpa using this.comp_sub_right h
        exact hu'.mul_continuousOn hgc.continuousOn
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := q)
          (hii _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩)
          (hii _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, le_refl _⟩), hz1, add_zero]
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := p + h)
          (hii _ _ ⟨le_refl _, by linarith⟩ ⟨by linarith, by linarith⟩)
          (hii _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩), hz2, zero_add]
    have hgi : ∀ x y, IntervalIntegrable g volume x y := fun x y => hgc.intervalIntegrable x y
    have hDh : D h = h⁻¹ * ∫ t in p..q, (u (t - h) - u t) * g t := by
      simp only [hD, smul_eq_mul]
      have : ∀ t, u t * (h⁻¹ * (g (t + h) - g t)) = h⁻¹ * (u t * g (t + h) - u t * g t) := by
        intro t; ring
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hgsh : Continuous (fun t => g (t + h)) := hgc.comp (continuous_add_const h)
      rw [intervalIntegral.integral_sub (hui.mul_continuousOn hgsh.continuousOn)
        (hui.mul_continuousOn hgc.continuousOn),
        hshift, ← intervalIntegral.integral_sub (hush.mul_continuousOn hgc.continuousOn)
        (hui.mul_continuousOn hgc.continuousOn)]
      congr 1; funext t; ring
    -- bound the integral
    have hbound : |∫ t in p..q, (u (t - h) - u t) * g t| ≤ ∫ t in p..q, (u t - u (t - h)) := by
      calc |∫ t in p..q, (u (t - h) - u t) * g t|
          ≤ ∫ t in p..q, |(u (t - h) - u t) * g t| :=
            intervalIntegral.abs_integral_le_integral_abs hpq
        _ ≤ ∫ t in p..q, (u t - u (t - h)) := by
            apply intervalIntegral.integral_mono_on hpq
            · exact ((hush.sub hui).mul_continuousOn hgc.continuousOn).abs
            · exact hui.sub hush
            · intro t ht
              have h1 : u (t - h) ≤ u t := hu (hmem h h0.le hh (t - h) ⟨by linarith [ht.1],
                by linarith [ht.2]⟩) (hmem h h0.le hh t ⟨by linarith [ht.1], ht.2⟩)
                (by linarith)
              rw [abs_mul, abs_of_nonpos (by linarith : u (t - h) - u t ≤ 0)]
              have := hg1 t
              nlinarith [abs_nonneg (g t)]
    have htel : ∫ t in p..q, (u t - u (t - h)) ≤ h * c := by
      rw [intervalIntegral.integral_sub hui hush]
      have e2 : ∫ t in p..q, u (t - h) = ∫ t in p - h..q - h, u t := by
        rw [intervalIntegral.integral_comp_sub_right]
      rw [e2]
      have hA : ∫ t in p..q, u t = (∫ t in p..q - h, u t) + ∫ t in q - h..q, u t :=
        (intervalIntegral.integral_add_adjacent_intervals
          (huii _ _ (hmem h h0.le hh p ⟨by linarith, hpq⟩)
            (hmem h h0.le hh (q - h) ⟨by linarith, by linarith⟩))
          (huii _ _ (hmem h h0.le hh (q - h) ⟨by linarith, by linarith⟩)
            (hmem h h0.le hh q ⟨by linarith, le_refl _⟩))).symm
      have hB : ∫ t in p - h..q - h, u t = (∫ t in p - h..p, u t) + ∫ t in p..q - h, u t :=
        (intervalIntegral.integral_add_adjacent_intervals
          (huii _ _ (hmem h h0.le hh (p - h) ⟨le_refl _, by linarith⟩)
            (hmem h h0.le hh p ⟨by linarith, hpq⟩))
          (huii _ _ (hmem h h0.le hh p ⟨by linarith, hpq⟩)
            (hmem h h0.le hh (q - h) ⟨by linarith, by linarith⟩))).symm
      have hC : ∫ t in q - h..q, u t ≤ h * c := by
        have := intervalIntegral.integral_mono_on (by linarith : q - h ≤ q)
          (huii _ _ (hmem h h0.le hh (q - h) ⟨by linarith, by linarith⟩)
            (hmem h h0.le hh q ⟨by linarith, le_refl _⟩)) intervalIntegrable_const
          (fun t ht => (huc t (hmem h h0.le hh t ⟨by linarith [ht.1], ht.2⟩)).2)
        simpa using this
      have hE : 0 ≤ ∫ t in p - h..p, u t := by
        apply intervalIntegral.integral_nonneg (by linarith)
        intro t ht
        exact (huc t (hmem h h0.le hh t ⟨ht.1, by linarith [ht.2]⟩)).1
      linarith
    rw [hDh, abs_mul, abs_inv, abs_of_pos h0]
    rw [inv_mul_le_iff₀ h0]
    linarith
  -- convergence of the difference quotients
  have hclaim2 : Tendsto D (𝓝[>] 0) (𝓝 (∫ t in p..q, u t * deriv g t)) := by
    have hui : IntervalIntegrable u volume p q :=
      huii p q (hmem 0 le_rfl hδpos p ⟨by linarith, hpq⟩) (hmem 0 le_rfl hδpos q ⟨by linarith, le_refl q⟩)
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => c * Md)
    · filter_upwards with h
      have : Continuous (fun t => h⁻¹ • (g (t + h) - g t)) := by fun_prop
      exact (hui.mul_continuousOn this.continuousOn).def'.1
    · have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδpos
      filter_upwards [hev] with h hh
      filter_upwards with t ht
      rw [Set.uIoc_of_le hpq] at ht
      have htI : t ∈ Ioo a b := hmem 0 le_rfl hδpos t ⟨by linarith [ht.1], ht.2⟩
      have hu0 := huc t htI
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hu0.1]
      apply mul_le_mul hu0.2 _ (norm_nonneg _) hc0
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hh.1]
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Icc p (q + δ))
        (fun x _ => hgd x) (fun x hx => hMd x hx) (convex_Icc _ _)
        (show t ∈ Icc p (q + δ) from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (show t + h ∈ Icc p (q + δ) from ⟨by linarith [ht.1, hh.1], by linarith [ht.2, hh.2]⟩)
      rw [show t + h - t = h by ring, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hh.1] at hmv
      rw [inv_mul_le_iff₀ hh.1, Real.norm_eq_abs]
      linarith
    · exact intervalIntegrable_const
    · filter_upwards with t ht
      have := (hgd t).hasDerivAt.tendsto_slope_zero_right
      exact this.const_mul (u t)
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), |D h| ≤ c := by
    filter_upwards [Ioo_mem_nhdsGT hδpos] with h hh
    exact hclaim1 h hh.1 hh.2
  exact le_of_tendsto hclaim2.abs hev

lemma deriv_zero_off {g : ℝ → ℝ} {α β : ℝ} (hsupp : ∀ s, s ∉ Icc α β → g s = 0) {s : ℝ}
    (hs : s ∉ Icc α β) : deriv g s = 0 := by
  have hopen : IsOpen (Icc α β)ᶜ := isClosed_Icc.isOpen_compl
  have : g =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hs] with x hx
    exact hsupp x hx
  rw [this.deriv_eq]
  simp

/-- `∫ u g' ≤ c` for `u` monotone (either direction) with values in `[0, c]` and `g` a `C¹`
function with `|g| ≤ 1` supported in a compact subinterval. -/
lemma oneD_bound {a b c α β : ℝ} {u g : ℝ → ℝ}
    (hu : MonotoneOn u (Ioo a b) ∨ AntitoneOn u (Ioo a b))
    (huc : ∀ s ∈ Ioo a b, 0 ≤ u s ∧ u s ≤ c) (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ s, s ∉ Icc α β → g s = 0) (haα : a < α) (hαβ : α ≤ β) (hβb : β < b)
    (hg1 : ∀ s, |g s| ≤ 1) :
    ∫ s, u s * deriv g s ≤ c := by
  set δ := min (α - a) (b - β) / 2 with hδ
  have hδpos : 0 < δ := by
    have : 0 < min (α - a) (b - β) := lt_min (by linarith) (by linarith)
    linarith
  set p := α - δ
  set q := β + δ
  have hpq : p ≤ q := by linarith
  have hfull : ∫ s, u s * deriv g s = ∫ s in p..q, u s * deriv g s := by
    rw [intervalIntegral.integral_of_le hpq]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have : s ∉ Icc α β := by
      intro h
      apply hs
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [deriv_zero_off hsupp this, mul_zero]
  rw [hfull]
  rcases hu with hmono | hanti
  · exact le_trans (le_abs_self _) (mono_case hmono huc hg hsupp haα hαβ hβb hg1)
  · set v : ℝ → ℝ := fun s => c - u s
    have hv : MonotoneOn v (Ioo a b) := fun x hx y hy hxy => by
      simp only [v]; linarith [hanti hx hy hxy]
    have hvc : ∀ s ∈ Ioo a b, 0 ≤ v s ∧ v s ≤ c := fun s hs => by
      simp only [v]; constructor <;> linarith [(huc s hs).1, (huc s hs).2]
    have hm := mono_case hv hvc hg hsupp haα hαβ hβb hg1
    have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
    have hg'c : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
    have hFTC : ∫ s in p..q, deriv g s = g q - g p :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hgd x) (hg'c.intervalIntegrable _ _)
    have hgp : g p = 0 := hsupp p (fun h => by linarith [h.1])
    have hgq : g q = 0 := hsupp q (fun h => by linarith [h.2])
    have hδ1 : 2 * δ ≤ α - a := by
      have := min_le_left (α - a) (b - β); linarith
    have hδ2 : 2 * δ ≤ b - β := by
      have := min_le_right (α - a) (b - β); linarith
    have hui : IntervalIntegrable (fun s => u s * deriv g s) volume p q := by
      apply IntervalIntegrable.mul_continuousOn _ hg'c.continuousOn
      apply AntitoneOn.intervalIntegrable
      apply hanti.mono
      intro z hz
      rw [Set.uIcc_of_le hpq] at hz
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have e : ∫ s in p..q, u s * deriv g s = -∫ s in p..q, v s * deriv g s := by
      have : ∀ s, v s * deriv g s = c * deriv g s - u s * deriv g s := fun s => by
        simp only [v]; ring
      simp_rw [this]
      rw [intervalIntegral.integral_sub ((hg'c.intervalIntegrable _ _).const_mul c) hui,
        intervalIntegral.integral_const_mul, hFTC, hgp, hgq]
      ring
    rw [e]
    linarith [neg_abs_le (∫ s in p..q, v s * deriv g s)]

end L3Aux


open MeasureTheory Filter Topology Set

namespace L3Aux

variable {d : ℕ}

/-- the point with `k`-th coordinate `s` and the other coordinates `y` -/
noncomputable def ins (k : Fin (d + 1)) (s : ℝ) (y : Fin d → ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.insertNth k s y)

lemma ins_apply_self (k : Fin (d + 1)) (s : ℝ) (y : Fin d → ℝ) : ins k s y k = s := by
  simp [ins]

lemma ins_apply_succAbove (k : Fin (d + 1)) (s : ℝ) (y : Fin d → ℝ) (j : Fin d) :
    ins k s y (k.succAbove j) = y j := by
  simp [ins]

lemma ins_affine (k : Fin (d + 1)) (s : ℝ) (y : Fin d → ℝ) :
    ins k s y = ins k 0 y + s • EuclideanSpace.single k (1 : ℝ) := by
  ext i
  rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
  · simp [ins_apply_self]
  · simp [ins_apply_succAbove, PiLp.single_apply, Fin.succAbove_ne]

lemma hasDerivAt_slice (φ : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (hφ : Differentiable ℝ φ) (k : Fin (d + 1)) (y : Fin d → ℝ) (s : ℝ) :
    HasDerivAt (fun s => φ (ins k s y) k)
      (fderiv ℝ φ (ins k s y) (EuclideanSpace.single k 1) k) s := by
  have hL : HasDerivAt (fun s : ℝ => ins k s y) (EuclideanSpace.single k (1 : ℝ)) s := by
    have : (fun s : ℝ => ins k s y) = fun s => ins k 0 y + s • EuclideanSpace.single k (1 : ℝ) := by
      funext s; exact ins_affine k s y
    rw [this]
    simpa using ((hasDerivAt_id s).smul_const (EuclideanSpace.single k (1 : ℝ))).const_add
      (ins k 0 y)
  have h1 := (hφ (ins k s y)).hasFDerivAt.comp_hasDerivAt s hL
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp_hasDerivAt s h1
  exact h2

lemma measurePreserving_E (k : Fin (d + 1)) :
    MeasurePreserving
      ((MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) k))
      (volume : Measure (EuclideanSpace ℝ (Fin (d + 1))))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 1))
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (volume : Measure ℝ)) k
  exact h2.comp h1

lemma E_symm_apply (k : Fin (d + 1)) (z : ℝ × (Fin d → ℝ)) :
    ((MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) k)).symm z = ins k z.1 z.2 := by
  rfl

lemma tv_coord (lo hi : Fin (d + 1) → ℝ) (hlh : ∀ k, lo k < hi k)
    (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
    (hΩ : Ω = {x | ∀ k, x k ∈ Ioo (lo k) (hi k)})
    (u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (hum : AEStronglyMeasurable u (volume.restrict Ω))
    (c : ℝ) (hc : 0 ≤ c) (huc : ∀ x ∈ Ω, 0 ≤ u x ∧ u x ≤ c) (k : Fin (d + 1))
    (hmono : ∀ y : Fin d → ℝ, (∀ j, y j ∈ Ioo (lo (k.succAbove j)) (hi (k.succAbove j))) →
      MonotoneOn (fun s => u (ins k s y)) (Ioo (lo k) (hi k)) ∨
        AntitoneOn (fun s => u (ins k s y)) (Ioo (lo k) (hi k)))
    (φ : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (hφ1 : ∀ x, ‖φ x‖ ≤ 1) :
    ∫ x in Ω, u x * fderiv ℝ φ x (EuclideanSpace.single k 1) k ≤
      c * ∏ j, (hi (k.succAbove j) - lo (k.succAbove j)) := by
  set E := (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) k) with hE
  have hEmp := measurePreserving_E (d := d) k
  set D : EuclideanSpace ℝ (Fin (d + 1)) → ℝ := fun x => fderiv ℝ φ x (EuclideanSpace.single k 1) k
    with hD
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hDc : Continuous D := by
    have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
    have h2 : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)) :=
      h1.clm_apply continuous_const
    exact (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp h2
  have hDcs : HasCompactSupport D := by
    have h1 : HasCompactSupport (fderiv ℝ φ) := hφc.fderiv (𝕜 := ℝ)
    exact h1.comp_left (g := fun L => L (EuclideanSpace.single k 1) k) (by simp)
  obtain ⟨MD, hMD⟩ := hDc.bounded_above_of_compact_support hDcs
  -- the set Y of admissible other coordinates
  set Y : Set (Fin d → ℝ) := Set.pi univ fun j => Ioo (lo (k.succAbove j)) (hi (k.succAbove j))
    with hY
  have hins_mem : ∀ s y, ins k s y ∈ Ω ↔ s ∈ Ioo (lo k) (hi k) ∧ y ∈ Y := by
    intro s y
    rw [hΩ]
    simp only [Set.mem_setOf_eq, hY, Set.mem_pi, Set.mem_univ, true_implies]
    rw [Fin.forall_iff_succAbove k]
    simp [ins_apply_self, ins_apply_succAbove]
  have hΩE : Ω = E ⁻¹' (Ioo (lo k) (hi k) ×ˢ Y) := by
    ext x
    have : x = ins k (E x).1 (E x).2 := by
      have h1 : E.symm (E x) = x := E.symm_apply_apply x
      rw [E_symm_apply] at h1
      exact h1.symm
    constructor
    · intro hx
      rw [this, hins_mem] at hx
      exact hx
    · intro hx
      rw [this, hins_mem]
      exact hx
  have hYm : MeasurableSet Y := MeasurableSet.univ_pi fun j => measurableSet_Ioo
  have hΩm : MeasurableSet Ω := by
    rw [hΩE]; exact E.measurable (measurableSet_Ioo.prod hYm)
  have hΩfin : volume Ω ≠ ⊤ := by
    rw [hΩE, hEmp.measure_preimage_equiv, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp) (by
      rw [hY, Measure.pi_pi]
      exact ENNReal.prod_ne_top fun j _ => by simp)
  set F : EuclideanSpace ℝ (Fin (d + 1)) → ℝ := Ω.indicator (fun x => u x * D x) with hF
  have hFint : Integrable F volume := by
    rw [hF, integrable_indicator_iff hΩm]
    haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩfin
    refine Integrable.mono' (integrable_const (c * MD))
      (hum.mul hDc.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem hΩm] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (huc x hx).1]
    exact mul_le_mul (huc x hx).2 (hMD x) (norm_nonneg _) hc
  rw [← integral_indicator hΩm]
  show ∫ x, F x ≤ _
  -- change variables
  have hG : ∫ x, F x = ∫ z, F (E.symm z) ∂((volume : Measure ℝ).prod
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) := by
    rw [← hEmp.integral_comp' (fun z => F (E.symm z))]
    congr 1
    funext x
    exact congrArg F (E.symm_apply_apply x).symm
  have hGint : Integrable (fun z => F (E.symm z)) ((volume : Measure ℝ).prod
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) := by
    have := (hEmp.symm E).integrable_comp_emb E.symm.measurableEmbedding (g := F)
    exact this.mpr hFint
  rw [hG, integral_prod_symm _ hGint]
  -- inner bound
  have hinner : ∀ y, ∫ s, F (E.symm (s, y)) ≤ Y.indicator (fun _ => c) y := by
    intro y
    have hEs : ∀ z, E.symm z = ins k z.1 z.2 := fun z => E_symm_apply k z
    simp only [hEs]
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy]
      set g : ℝ → ℝ := fun s => φ (ins k s y) k with hg
      have hgd : ∀ s, HasDerivAt g (D (ins k s y)) s := fun s => hasDerivAt_slice φ hφd k y s
      have hderiv : ∀ s, deriv g s = D (ins k s y) := fun s => (hgd s).deriv
      have hgC : ContDiff ℝ 1 g := by
        have hL : ContDiff ℝ 1 (fun s : ℝ => ins k s y) := by
          have : (fun s : ℝ => ins k s y) =
              fun s => ins k 0 y + s • EuclideanSpace.single k (1 : ℝ) := by
            funext s; exact ins_affine k s y
          rw [this]
          exact contDiff_const.add (contDiff_id.smul contDiff_const)
        exact (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp (hφ.comp hL)
      have hg1 : ∀ s, |g s| ≤ 1 := fun s => by
        have := PiLp.norm_apply_le (φ (ins k s y)) k
        rw [Real.norm_eq_abs] at this
        exact this.trans (hφ1 _)
      set K : Set ℝ := {s | ins k s y ∈ tsupport φ} with hK
      have hKsub : K ⊆ Ioo (lo k) (hi k) := fun s hs => ((hins_mem s y).mp (hφs hs)).1
      have hgK : ∀ s, g s ≠ 0 → s ∈ K := by
        intro s hs
        apply subset_tsupport
        intro h0
        apply hs
        simp [hg, h0]
      by_cases hKe : K.Nonempty
      · have hKc : IsClosed K := by
          have hcont : Continuous (fun s : ℝ => ins k s y) := by
            have : (fun s : ℝ => ins k s y) =
                fun s => ins k 0 y + s • EuclideanSpace.single k (1 : ℝ) := by
              funext s; exact ins_affine k s y
            rw [this]; fun_prop
          exact (isClosed_tsupport φ).preimage hcont
        have hKb : BddBelow K := ⟨lo k, fun s hs => (hKsub hs).1.le⟩
        have hKa : BddAbove K := ⟨hi k, fun s hs => (hKsub hs).2.le⟩
        have hαK := hKc.csInf_mem hKe hKb
        have hβK := hKc.csSup_mem hKe hKa
        have hsupp : ∀ s, s ∉ Icc (sInf K) (sSup K) → g s = 0 := by
          intro s hs
          by_contra h
          exact hs ⟨csInf_le hKb (hgK s h), le_csSup hKa (hgK s h)⟩
        have hy' : ∀ j, y j ∈ Ioo (lo (k.succAbove j)) (hi (k.succAbove j)) := by
          simpa [hY] using hy
        have hb := oneD_bound (u := fun s => u (ins k s y)) (hmono y hy')
          (fun s hs => huc _ ((hins_mem s y).mpr ⟨hs, hy⟩)) hgC hsupp (hKsub hαK).1
          (csInf_le_csSup hKe hKb hKa) (hKsub hβK).2 hg1
        refine le_trans (le_of_eq ?_) hb
        apply integral_congr_ae
        filter_upwards with s
        simp only [hF, Set.indicator]
        split_ifs with hs
        · rw [hderiv]
        · have hs' : s ∉ Ioo (lo k) (hi k) := fun h => hs ((hins_mem s y).mpr ⟨h, hy⟩)
          have : s ∉ Icc (sInf K) (sSup K) := by
            intro h
            apply hs'
            exact ⟨lt_of_lt_of_le (hKsub hαK).1 h.1, lt_of_le_of_lt h.2 (hKsub hβK).2⟩
          rw [hderiv, ← (hgd s).deriv, deriv_zero_off hsupp this, mul_zero]
      · rw [Set.not_nonempty_iff_eq_empty] at hKe
        have hg0 : g = fun _ => 0 := by
          funext s
          by_contra h
          have := hgK s h
          rw [hKe] at this
          exact this
        have : ∀ s, F (ins k s y) = 0 := by
          intro s
          simp only [hF, Set.indicator]
          split_ifs
          · rw [← hderiv, hg0]; simp
          · rfl
        simp only [this, integral_zero]
        exact hc
    · rw [Set.indicator_of_notMem hy]
      have : ∀ s, F (ins k s y) = 0 := by
        intro s
        simp only [hF]
        apply Set.indicator_of_notMem
        intro h
        exact hy ((hins_mem s y).mp h).2
      simp [this]
  have hYfin : (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) Y ≠ ⊤ := by
    rw [hY, Measure.pi_pi]
    exact ENNReal.prod_ne_top fun j _ => by simp
  calc ∫ y, ∫ s, F (E.symm (s, y)) ∂volume ∂(Measure.pi fun _ : Fin d => (volume : Measure ℝ))
      ≤ ∫ y, Y.indicator (fun _ => c) y ∂(Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
        apply integral_mono hGint.integral_prod_right
        · exact (integrable_indicator_iff hYm).mpr (integrableOn_const hYfin)
        · exact hinner
    _ = c * ∏ j, (hi (k.succAbove j) - lo (k.succAbove j)) := by
        rw [integral_indicator_const _ hYm, smul_eq_mul, mul_comm, Measure.real, hY,
          Measure.pi_pi]
        simp only [Real.volume_Ioo, ENNReal.toReal_prod]
        congr 1
        apply Finset.prod_congr rfl
        intro j _
        rw [ENNReal.toReal_ofReal (by linarith [hlh (k.succAbove j)])]

lemma box_finite (lo hi : Fin (d + 1) → ℝ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
    (hΩ : Ω = {x | ∀ k, x k ∈ Ioo (lo k) (hi k)}) : MeasurableSet Ω ∧ volume Ω ≠ ⊤ := by
  have hsub : Ω = (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm ⁻¹'
      (Set.pi univ fun k => Ioo (lo k) (hi k)) := by
    rw [hΩ]; ext x; simp
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 1))
  refine ⟨?_, ?_⟩
  · rw [hsub]
    exact (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  · rw [hsub, hmp.measure_preimage_equiv, Real.volume_pi_Ioo]
    exact ENNReal.prod_ne_top fun j _ => ENNReal.ofReal_ne_top

theorem tv_bound (lo hi : Fin (d + 1) → ℝ) (hlh : ∀ k, lo k < hi k)
    (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
    (hΩ : Ω = {x | ∀ k, x k ∈ Ioo (lo k) (hi k)})
    (u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (hum : AEStronglyMeasurable u (volume.restrict Ω))
    (c : ℝ) (hc : 0 ≤ c) (huc : ∀ x ∈ Ω, 0 ≤ u x ∧ u x ≤ c)
    (hmono : ∀ k, ∀ y : Fin d → ℝ, (∀ j, y j ∈ Ioo (lo (k.succAbove j)) (hi (k.succAbove j))) →
      MonotoneOn (fun s => u (ins k s y)) (Ioo (lo k) (hi k)) ∨
        AntitoneOn (fun s => u (ins k s y)) (Ioo (lo k) (hi k)))
    (φ : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (hφ1 : ∀ x, ‖φ x‖ ≤ 1) :
    ∫ x in Ω, u x * TeschlODE.HigherDim.divergence φ x ≤
      c * ∑ k : Fin (d + 1), ∏ j, (hi (k.succAbove j) - lo (k.succAbove j)) := by
  obtain ⟨hΩm, hΩfin⟩ := box_finite lo hi Ω hΩ
  haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩfin
  have hint : ∀ k : Fin (d + 1), Integrable
      (fun x => u x * fderiv ℝ φ x (EuclideanSpace.single k 1) k) (volume.restrict Ω) := by
    intro k
    set D : EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
      fun x => fderiv ℝ φ x (EuclideanSpace.single k 1) k with hD
    have hDc : Continuous D := by
      have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
      have h2 : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)) :=
        h1.clm_apply continuous_const
      exact (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp h2
    have hDcs : HasCompactSupport D := by
      have h1 : HasCompactSupport (fderiv ℝ φ) := hφc.fderiv (𝕜 := ℝ)
      exact h1.comp_left (g := fun L => L (EuclideanSpace.single k 1) k) (by simp)
    obtain ⟨MD, hMD⟩ := hDc.bounded_above_of_compact_support hDcs
    refine Integrable.mono' (integrable_const (c * MD))
      (hum.mul hDc.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem hΩm] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (huc x hx).1]
    exact mul_le_mul (huc x hx).2 (hMD x) (norm_nonneg _) hc
  have hsplit : ∫ x in Ω, u x * TeschlODE.HigherDim.divergence φ x =
      ∑ k, ∫ x in Ω, u x * fderiv ℝ φ x (EuclideanSpace.single k 1) k := by
    rw [← integral_finset_sum _ (fun k _ => hint k)]
    congr 1
    funext x
    unfold TeschlODE.HigherDim.divergence
    rw [Finset.mul_sum]
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  exact tv_coord lo hi hlh Ω hΩ u hum c hc huc k (hmono k) φ hφ hφc hφs hφ1

end L3Aux


open MeasureTheory ContextualAuctions.Existence Set

namespace L3CA

/-- monotone in the product order on `Θ` (nondecreasing in `w`, nonincreasing in `B`) -/
lemma ell_mono (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    (hμr : ∀ θ ∈ Theta M, μ θ ∈ Icc 0 (omega M / M.Bmin))
    {w w' : Fin M.d → ℝ} {B B' : ℝ} (hθ : ((w, B) : (Fin M.d → ℝ) × ℝ) ∈ Theta M)
    (hθ' : ((w', B') : (Fin M.d → ℝ) × ℝ) ∈ Theta M) (hw : w ≤ w') (hB : B' ≤ B) :
    ell M μ (w, B) ≤ ell M μ (w', B') := by
  classical
  obtain ⟨hL1, hL2⟩ := lemma_2 M hM μ hμ hμr
  -- first lower the budget
  have hθ1 : ((w, B') : (Fin M.d → ℝ) × ℝ) ∈ Theta M := ⟨hθ.1, hθ'.2⟩
  have step1 : ell M μ (w, B) ≤ ell M μ (w, B') := hL2 _ hθ1 _ hθ rfl hB
  -- then raise the weights one coordinate at a time
  let z : Finset (Fin M.d) → (Fin M.d → ℝ) := fun S j => if j ∈ S then w' j else w j
  have hz : ∀ S, ((z S, B') : (Fin M.d → ℝ) × ℝ) ∈ Theta M := by
    intro S
    refine ⟨fun j => ?_, hθ'.2⟩
    simp only [z]
    split_ifs
    · exact hθ'.1 j
    · exact hθ.1 j
  have step2 : ∀ S : Finset (Fin M.d), ell M μ (w, B') ≤ ell M μ (z S, B') := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [z]
    | insert i S hi ih =>
      refine le_trans ih (hL1 _ (hz S) _ (hz (insert i S)) i rfl (fun j hj => ?_) ?_)
      · simp only [z, Finset.mem_insert, hj, false_or]
      · simp only [z, Finset.mem_insert, true_or, if_true, hi, if_false]
        exact hw i
  have hzu : z Finset.univ = w' := by funext j; simp [z]
  have := step2 Finset.univ
  rw [hzu] at this
  exact le_trans step1 this

/-- coordinates of the box `Θ` in `ℝ^{d+1}` -/
noncomputable def lo (M : Model) (k : Fin (M.d + 1)) : ℝ := if k = Fin.last M.d then M.Bmin else 0

lemma Omega_eq (M : Model) :
    toType ⁻¹' Theta M = {x : EuclideanSpace ℝ (Fin (M.d + 1)) |
      ∀ k, x k ∈ Ioo (lo M k) M.U} := by
  ext x
  simp only [mem_preimage, Theta, toType, mem_setOf_eq, mem_Ioo, lo]
  rw [Fin.forall_fin_succ']
  simp [Fin.castSucc_ne_last]

/-- the flipped box in `Fin (d+1) → ℝ` -/
def Omega' (M : Model) : Set (Fin (M.d + 1) → ℝ) :=
  {z | (∀ i : Fin M.d, z i.castSucc ∈ Ioo 0 M.U) ∧ z (Fin.last M.d) ∈ Ioo (-M.U) (-M.Bmin)}

/-- `ℓ` read in flipped coordinates -/
noncomputable def fflip (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (z : Fin (M.d + 1) → ℝ) : ℝ :=
  ell M μ (fun i => z i.castSucc, -z (Fin.last M.d))

lemma fflip_mono (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    (hμr : ∀ θ ∈ Theta M, μ θ ∈ Icc 0 (omega M / M.Bmin)) {z z' : Fin (M.d + 1) → ℝ}
    (hz : z ∈ Omega' M) (hz' : z' ∈ Omega' M) (hle : z ≤ z') :
    fflip M μ z ≤ fflip M μ z' := by
  unfold fflip
  apply ell_mono M hM μ hμ hμr
  · exact ⟨fun i => hz.1 i, by linarith [hz.2.2], by linarith [hz.2.1]⟩
  · exact ⟨fun i => hz'.1 i, by linarith [hz'.2.2], by linarith [hz'.2.1]⟩
  · exact fun i => hle i.castSucc
  · linarith [hle (Fin.last M.d)]

lemma fflip_aemeasurable (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) (hμr : ∀ θ ∈ Theta M, μ θ ∈ Icc 0 (omega M / M.Bmin)) :
    AEMeasurable (fflip M μ) (volume.restrict (Omega' M)) := by
  apply MeasureTheory.NullMeasurable.aemeasurable
  have hΩ'm : MeasurableSet (Omega' M) := by
    unfold Omega'
    simp only [ofPred_and, ofPred_forall]
    exact (MeasurableSet.iInter fun i => measurableSet_Ioo.preimage (measurable_pi_apply _)).inter
      (measurableSet_Ioo.preimage (measurable_pi_apply _))
  refine (measurable_of_Iic (δ := NullMeasurableSpace (Fin (M.d + 1) → ℝ)
    (volume.restrict (Omega' M))) (f := fflip M μ) (fun s => ?_) : _)
  show NullMeasurableSet (fflip M μ ⁻¹' Iic s) (volume.restrict (Omega' M))
  set L := Omega' M ∩ {z | fflip M μ z ≤ s} with hL
  have hord : L.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    have hzΩ : z ∈ Omega' M := by
      refine ⟨fun i => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact lt_of_lt_of_le (hx.1.1 i).1 (hz.1 i.castSucc)
      · exact lt_of_le_of_lt (hz.2 i.castSucc) (hy.1.1 i).2
      · exact lt_of_lt_of_le hx.1.2.1 (hz.1 _)
      · exact lt_of_le_of_lt (hz.2 _) hy.1.2.2
    exact ⟨hzΩ, le_trans (fflip_mono M hM μ hμ hμr hzΩ hy.1 hz.2) hy.2⟩
  have hLn : NullMeasurableSet L (volume.restrict (Omega' M)) :=
    hord.nullMeasurableSet.mono_ac Measure.restrict_le_self.absolutelyContinuous
  refine hLn.congr ?_
  filter_upwards [ae_restrict_mem hΩ'm] with z hz
  simp only [hL, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_Iic, eq_iff_iff]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-- the flip map -/
noncomputable def Mmap (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) : Fin (d + 1) → ℝ :=
  Function.update (WithLp.ofLp x) (Fin.last d) (-x (Fin.last d))

lemma Mmap_mp (d : ℕ) : MeasurePreserving (Mmap d) volume volume := by
  set P := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)
  have h1 := PiLp.volume_preserving_ofLp (ι := Fin (d + 1))
  have hP := measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (volume : Measure ℝ))
    (Fin.last d)
  have hN : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : (Fin d → ℝ) → (Fin d → ℝ)))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin d => (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  have h := ((hP.symm P).comp hN).comp (hP.comp h1)
  have heq : (P.symm ∘ Prod.map (Neg.neg : ℝ → ℝ) id) ∘ (P ∘ WithLp.ofLp) = Mmap d := by
    funext x
    funext k
    simp only [Function.comp_apply, Mmap, P, MeasurableEquiv.piFinSuccAbove_apply,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Prod.map_apply, id]
    rcases Fin.eq_self_or_eq_succAbove (Fin.last d) k with rfl | ⟨j, rfl⟩
    · simp
    · simp [Function.update_of_ne (Fin.succAbove_ne _ _)]
      try rfl
  rw [heq] at h
  exact h

lemma toType_mp (d : ℕ) :
    MeasurePreserving (toType : EuclideanSpace ℝ (Fin (d + 1)) → (Fin d → ℝ) × ℝ) volume volume ∧
    MeasurableEmbedding (toType : EuclideanSpace ℝ (Fin (d + 1)) → (Fin d → ℝ) × ℝ) := by
  set T := (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)).trans
      MeasurableEquiv.prodComm)
  have hT : ⇑T = toType := by
    funext x
    simp only [T, MeasurableEquiv.coe_trans, Function.comp_apply, toType]
    simp [MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  have h1 := PiLp.volume_preserving_ofLp (ι := Fin (d + 1))
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (volume : Measure ℝ))
    (Fin.last d)
  have h3 := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := Measure.pi fun _ : Fin d => (volume : Measure ℝ))
  refine ⟨?_, ?_⟩
  · have h := (h3.comp h2).comp h1
    have heq : (Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ)
        (Fin.last d))) ∘ WithLp.ofLp = (toType : EuclideanSpace ℝ (Fin (d + 1)) → _) := by
      rw [← hT]; rfl
    rw [heq] at h
    exact h
  · rw [← hT]; exact T.measurableEmbedding

lemma ins_le {d : ℕ} (k : Fin (d + 1)) {s s' : ℝ} (hs : s ≤ s') (y : Fin d → ℝ) (k' : Fin (d + 1)) :
    L3Aux.ins k s y k' ≤ L3Aux.ins k s' y k' := by
  rcases Fin.eq_self_or_eq_succAbove k k' with rfl | ⟨j, rfl⟩
  · simp [L3Aux.ins_apply_self, hs]
  · simp [L3Aux.ins_apply_succAbove]

lemma ins_eq_of_ne {d : ℕ} (k : Fin (d + 1)) (s s' : ℝ) (y : Fin d → ℝ) {k' : Fin (d + 1)}
    (hk : k' ≠ k) : L3Aux.ins k s y k' = L3Aux.ins k s' y k' := by
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
  simp [L3Aux.ins_apply_succAbove]

end L3CA

open L3CA in
theorem solution (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    (hμr : ∀ θ ∈ Theta M, μ θ ∈ Set.Icc 0 (omega M / M.Bmin)) :
    IntegrableOn (ell M μ) (Theta M) ∧ Vtheta M (ell M μ) ≤ (V0 M : EReal) := by
  set c := omega M / M.Bmin with hc_def
  have hc : 0 ≤ c := div_nonneg (CAC.omega_nonneg M hM) hM.Bmin_pos.le
  set Ω := toType ⁻¹' Theta M with hΩ_def
  have hΩ := Omega_eq M
  set u : EuclideanSpace ℝ (Fin (M.d + 1)) → ℝ := fun x => ell M μ (toType x) with hu
  have huflip : u = fflip M μ ∘ Mmap M.d := by
    funext x
    simp only [hu, Function.comp_apply, fflip, Mmap, toType]
    congr 1
    ext i
    · simp [Function.update_of_ne (Fin.castSucc_ne_last i)]
    · simp
  have hΩ' : Ω = Mmap M.d ⁻¹' Omega' M := by
    rw [hΩ_def, hΩ]
    ext x
    simp only [mem_setOf_eq, mem_preimage, Omega', Mmap, lo]
    rw [Fin.forall_fin_succ']
    simp [Function.update_of_ne (Fin.castSucc_ne_last _), Fin.castSucc_ne_last]
    first
      | exact fun _ => and_comm
      | tauto
  have hΩ'm : MeasurableSet (Omega' M) := by
    unfold Omega'
    simp only [ofPred_and, ofPred_forall]
    exact (MeasurableSet.iInter fun i => measurableSet_Ioo.preimage (measurable_pi_apply _)).inter
      (measurableSet_Ioo.preimage (measurable_pi_apply _))
  have hum : AEMeasurable u (volume.restrict Ω) := by
    rw [huflip, hΩ']
    exact (fflip_aemeasurable M hM μ hμ hμr).comp_quasiMeasurePreserving
      ((Mmap_mp M.d).restrict_preimage hΩ'm).quasiMeasurePreserving
  have huc : ∀ x ∈ Ω, 0 ≤ u x ∧ u x ≤ c := fun x hx =>
    (CAC.ell_spec M hM μ hμ.1 hx).1
  obtain ⟨hΩm, hΩfin⟩ := L3Aux.box_finite (lo M) (fun _ => M.U) Ω hΩ
  have hlh : ∀ k, lo M k < M.U := by
    intro k; unfold lo; split_ifs
    · exact hM.Bmin_lt_U
    · exact hM.U_pos
  refine ⟨?_, ?_⟩
  · -- integrability
    haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩfin
    have hint : IntegrableOn u Ω := by
      refine Integrable.mono' (integrable_const c) hum.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem hΩm] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (huc x hx).1]
      exact (huc x hx).2
    obtain ⟨hTmp, hTemb⟩ := toType_mp M.d
    exact (hTmp.integrableOn_comp_preimage hTemb (f := ell M μ) (s := Theta M)).mp hint
  · -- total variation
    have hmono : ∀ k, ∀ y : Fin M.d → ℝ,
        (∀ j, y j ∈ Ioo (lo M (k.succAbove j)) M.U) →
        MonotoneOn (fun s => u (L3Aux.ins k s y)) (Ioo (lo M k) M.U) ∨
          AntitoneOn (fun s => u (L3Aux.ins k s y)) (Ioo (lo M k) M.U) := by
      intro k y hy
      have hmem : ∀ s ∈ Ioo (lo M k) M.U, toType (L3Aux.ins k s y) ∈ Theta M := by
        intro s hs
        show L3Aux.ins k s y ∈ toType ⁻¹' Theta M
        rw [hΩ]
        intro k'
        rcases Fin.eq_self_or_eq_succAbove k k' with rfl | ⟨j, rfl⟩
        · rw [L3Aux.ins_apply_self]; exact hs
        · rw [L3Aux.ins_apply_succAbove]; exact hy j
      by_cases hk : k = Fin.last M.d
      · right
        intro s hs s' hs' hss
        simp only [hu]
        have h1 := hmem s hs
        have h2 := hmem s' hs'
        have hw : (toType (L3Aux.ins k s' y)).1 = (toType (L3Aux.ins k s y)).1 := by
          funext i
          simp only [toType]
          exact ins_eq_of_ne k s' s y (by rw [hk]; exact Fin.castSucc_ne_last i)
        have hB : (toType (L3Aux.ins k s y)).2 ≤ (toType (L3Aux.ins k s' y)).2 := by
          simp only [toType]; rw [← hk]; exact ins_le k hss y k
        have := ell_mono M hM μ hμ hμr (w := (toType (L3Aux.ins k s' y)).1)
          (B := (toType (L3Aux.ins k s' y)).2) (w' := (toType (L3Aux.ins k s y)).1)
          (B' := (toType (L3Aux.ins k s y)).2) h2 h1 (by rw [hw]) hB
        simpa using this
      · left
        intro s hs s' hs' hss
        simp only [hu]
        have h1 := hmem s hs
        have h2 := hmem s' hs'
        have hw : (toType (L3Aux.ins k s y)).1 ≤ (toType (L3Aux.ins k s' y)).1 := by
          intro i; simp only [toType]; exact ins_le k hss y _
        have hB : (toType (L3Aux.ins k s' y)).2 = (toType (L3Aux.ins k s y)).2 := by
          simp only [toType]; exact ins_eq_of_ne k s' s y (Ne.symm hk)
        have := ell_mono M hM μ hμ hμr (w := (toType (L3Aux.ins k s y)).1)
          (B := (toType (L3Aux.ins k s y)).2) (w' := (toType (L3Aux.ins k s' y)).1)
          (B' := (toType (L3Aux.ins k s' y)).2) h1 h2 hw (by rw [hB])
        simpa using this
    unfold Vtheta totalVariation
    apply iSup₂_le
    intro φ hφ
    have hb := L3Aux.tv_bound (lo M) (fun _ => M.U) hlh Ω hΩ u hum.aestronglyMeasurable c hc huc
      hmono φ hφ.1 hφ.2.1 hφ.2.2.1 hφ.2.2.2
    have hprod : ∀ k : Fin (M.d + 1), ∏ j, (M.U - lo M (k.succAbove j)) ≤ M.U ^ M.d := by
      intro k
      calc ∏ j, (M.U - lo M (k.succAbove j)) ≤ ∏ _j : Fin M.d, M.U := by
            apply Finset.prod_le_prod
            · intro j _; linarith [hlh (k.succAbove j)]
            · intro j _
              unfold lo; split_ifs
              · linarith [hM.Bmin_pos]
              · linarith
        _ = M.U ^ M.d := by simp
    have hsum : ∑ k : Fin (M.d + 1), ∏ j, (M.U - lo M (k.succAbove j)) ≤ (M.d + 1) * M.U ^ M.d := by
      calc _ ≤ ∑ _k : Fin (M.d + 1), M.U ^ M.d := Finset.sum_le_sum fun k _ => hprod k
        _ = (M.d + 1) * M.U ^ M.d := by simp
    have hfin : c * ∑ k : Fin (M.d + 1), ∏ j, (M.U - lo M (k.succAbove j)) ≤ V0 M := by
      unfold V0
      have hmax : M.U ^ M.d ≤ max (M.U ^ M.d) (M.U ^ (M.d + 1)) := le_max_left _ _
      have h1 : c * ∑ k : Fin (M.d + 1), ∏ j, (M.U - lo M (k.succAbove j)) ≤
          c * ((M.d + 1) * M.U ^ M.d) := mul_le_mul_of_nonneg_left hsum hc
      have h2 : c * ((M.d + 1) * M.U ^ M.d) ≤ c * ((M.d + 1) * max (M.U ^ M.d) (M.U ^ (M.d + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax (by positivity)) hc
      have h3 : c * ((M.d + 1) * max (M.U ^ M.d) (M.U ^ (M.d + 1))) =
          (M.d + 1) * max (M.U ^ M.d) (M.U ^ (M.d + 1)) * omega M / M.Bmin := by
        rw [hc_def]; ring
      linarith
    exact EReal.coe_le_coe_iff.mpr (le_trans hb hfin)
