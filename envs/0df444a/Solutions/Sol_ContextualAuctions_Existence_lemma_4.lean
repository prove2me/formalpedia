-- Prove2me | solution 1 for ContextualAuctions.Existence.lemma_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T07:53:34.074719+00:00
-- url     : https://prove2.me/submissions/30d5a7bc-17dd-4b32-9bf5-d3d5f079fc4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint
import Theorems.Thm_ContextualAuctions_Existence_lemma_1
import Theorems.Thm_ContextualAuctions_Existence_lemma_4_compact
import Theorems.Thm_ContextualAuctions_Existence_lemma_4_continuous

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

namespace CAC

/-- `H` only depends on the `G`-a.e. class of `μ`. -/
lemma H_congr (M : Model) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ} (h : μ₁ =ᵐ[M.G] μ₂) :
    H M μ₁ = H M μ₂ := by
  funext α x
  unfold H
  congr 2
  apply measure_congr
  filter_upwards [h] with θ hθ
  change (paced μ₁ θ α ≤ x) = (paced μ₂ θ α ≤ x)
  simp only [paced, hθ]

lemma sigma_congr (M : Model) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ} (h : μ₁ =ᵐ[M.G] μ₂) :
    sigma M μ₁ = sigma M μ₂ := by
  funext α x
  unfold sigma
  rw [H_congr M h]

lemma ae_comp (M : Model) (hM : M.Standing) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : μ₁ =ᵐ[M.G] μ₂) : ∀ᵐ ω ∂P M, ∀ i, μ₁ (ω.2 i) = μ₂ (ω.2 i) := by
  have := hM.probG
  have := hM.probF
  rw [ae_all_iff]
  intro i
  have h1 : ∀ᵐ x ∂(Measure.pi fun _ : Fin (M.n - 1) => M.G), μ₁ (x i) = μ₂ (x i) :=
    (measurePreserving_eval (fun _ : Fin (M.n - 1) => M.G) i).quasiMeasurePreserving.ae h
  exact (Measure.quasiMeasurePreserving_snd (μ := M.F)
    (ν := Measure.pi fun _ : Fin (M.n - 1) => M.G)).ae h1

lemma wins_congr (M : Model) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ} (h : μ₁ =ᵐ[M.G] μ₂)
    (b : (Fin M.d → ℝ) → ℝ) (ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ))
    (hω : ∀ i, μ₁ (ω.2 i) = μ₂ (ω.2 i)) :
    wins M (beta M μ₁) b ω ↔ wins M (beta M μ₂) b ω := by
  unfold wins beta paced
  rw [sigma_congr M h]
  simp only [hω]

lemma qDual_congr (M : Model) (hM : M.Standing) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : μ₁ =ᵐ[M.G] μ₂) : qDual M μ₁ = qDual M μ₂ := by
  classical
  funext θ t
  have hP := ae_comp M hM h
  have hset : ∀ (f : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) → ℝ)
      (b : (Fin M.d → ℝ) → ℝ),
      (fun ω => if wins M (beta M μ₁) b ω then f ω else 0) =ᵐ[P M]
        (fun ω => if wins M (beta M μ₂) b ω then f ω else 0) := by
    intro f b
    filter_upwards [hP] with ω hω
    simp only [wins_congr M h b ω hω]
  have hadm : ∀ b, Admissible M (beta M μ₁) b ↔ Admissible M (beta M μ₂) b := by
    intro b
    unfold Admissible
    rw [integrable_congr (hset (fun ω => b ω.1) b)]
  unfold qDual
  congr 2
  ext v
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, (hadm b).1 hb, integral_congr_ae (hset _ b)⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, (hadm b).2 hb, (integral_congr_ae (hset _ b)).symm⟩

lemma fObj_congr (M : Model) (hM : M.Standing) {μ₁ μ₂ ν₁ ν₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : μ₁ =ᵐ[M.G] μ₂) (h' : ν₁ =ᵐ[M.G] ν₂) : fObj M μ₁ ν₁ = fObj M μ₂ ν₂ := by
  unfold fObj
  rw [qDual_congr M hM h]
  apply integral_congr_ae
  filter_upwards [h'] with θ hθ
  rw [hθ]

lemma ae_G_of_ae_vol (M : Model) (hM : M.Standing) {f₁ f₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : f₁ =ᵐ[volume.restrict (Theta M)] f₂) : f₁ =ᵐ[M.G] f₂ :=
  (G_ac_restrict M hM).ae_le h

end CAC


open MeasureTheory ContextualAuctions.Existence Set Filter Topology

namespace L4

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

/-- every element of `X₀` has total-variation integrals bounded by `V₀` -/
lemma tv_int_le (M : Model) {μ : (Fin M.d → ℝ) × ℝ → ℝ} (hμ : μ ∈ X0 M)
    {φ : EuclideanSpace ℝ (Fin (M.d + 1)) → EuclideanSpace ℝ (Fin (M.d + 1))}
    (hφ : IsTestField (toType ⁻¹' Theta M) φ) :
    ∫ x in toType ⁻¹' Theta M, μ (toType x) * TeschlODE.HigherDim.divergence φ x ≤ V0 M := by
  have h := hμ.2
  unfold Vtheta totalVariation at h
  have := le_trans (le_iSup₂ (f := fun φ (_ : IsTestField (toType ⁻¹' Theta M) φ) =>
    ((∫ x in toType ⁻¹' Theta M, μ (toType x) * TeschlODE.HigherDim.divergence φ x : ℝ) : EReal))
    φ hφ) h
  exact EReal.coe_le_coe_iff.mp this

lemma div_bounded {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    {φ : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hφ : IsTestField Ω φ) :
    Continuous (TeschlODE.HigherDim.divergence φ) ∧
      ∃ C, ∀ x, ‖TeschlODE.HigherDim.divergence φ x‖ ≤ C := by
  have hc : Continuous (TeschlODE.HigherDim.divergence φ) := by
    unfold TeschlODE.HigherDim.divergence
    apply continuous_finset_sum
    intro k _
    have h1 : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by norm_num)
    exact (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp (h1.clm_apply continuous_const)
  refine ⟨hc, ?_⟩
  apply hc.bounded_above_of_compact_support
  apply HasCompactSupport.intro hφ.2.1
  intro x hx
  have h0 : fderiv ℝ φ x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset ℝ h)
  unfold TeschlODE.HigherDim.divergence
  simp [h0]

lemma X0_convex (M : Model) (hM : M.Standing) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h₁ : μ₁ ∈ X0 M) (h₂ : μ₂ ∈ X0 M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (fun θ => a * μ₁ θ + b * μ₂ θ) ∈ X0 M := by
  refine ⟨⟨⟨(measurable_const.mul h₁.1.1.1).add (measurable_const.mul h₂.1.1.1),
    fun θ hθ => add_nonneg (mul_nonneg ha (h₁.1.1.2 θ hθ)) (mul_nonneg hb (h₂.1.1.2 θ hθ))⟩,
    (h₁.1.2.1.const_mul a).add (h₂.1.2.1.const_mul b), fun θ hθ => ⟨?_, ?_⟩⟩, ?_⟩
  · exact add_nonneg (mul_nonneg ha (h₁.1.2.2 θ hθ).1) (mul_nonneg hb (h₂.1.2.2 θ hθ).1)
  · have e1 := mul_le_mul_of_nonneg_left (h₁.1.2.2 θ hθ).2 ha
    have e2 := mul_le_mul_of_nonneg_left (h₂.1.2.2 θ hθ).2 hb
    have : a * (omega M / M.Bmin) + b * (omega M / M.Bmin) = omega M / M.Bmin := by
      rw [← add_mul, hab, one_mul]
    linarith
  · unfold Vtheta totalVariation
    apply iSup₂_le
    intro φ hφ
    apply EReal.coe_le_coe_iff.mpr
    obtain ⟨hTmp, hTemb⟩ := toType_mp M.d
    have hi : ∀ μ : (Fin M.d → ℝ) × ℝ → ℝ, μ ∈ X0 M →
        IntegrableOn (fun x => μ (toType x) * TeschlODE.HigherDim.divergence φ x)
          (toType ⁻¹' Theta M) := by
      intro μ hμ
      have hint : IntegrableOn (μ ∘ toType) (toType ⁻¹' Theta M) :=
        (hTmp.integrableOn_comp_preimage hTemb (f := μ) (s := Theta M)).mpr hμ.1.2.1
      obtain ⟨hdc, C, hC⟩ := div_bounded hφ
      exact hint.mul_bdd hdc.aestronglyMeasurable (Eventually.of_forall hC)
    have e : ∫ x in toType ⁻¹' Theta M,
        (fun θ => a * μ₁ θ + b * μ₂ θ) (toType x) * TeschlODE.HigherDim.divergence φ x =
        a * (∫ x in toType ⁻¹' Theta M, μ₁ (toType x) * TeschlODE.HigherDim.divergence φ x) +
        b * (∫ x in toType ⁻¹' Theta M, μ₂ (toType x) * TeschlODE.HigherDim.divergence φ x) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi μ₁ h₁).const_mul a)
        ((hi μ₂ h₂).const_mul b)]
      congr 1; funext x; ring
    rw [e]
    have t1 := tv_int_le M h₁ hφ
    have t2 := tv_int_le M h₂ hφ
    have : a * (∫ x in toType ⁻¹' Theta M, μ₁ (toType x) * TeschlODE.HigherDim.divergence φ x) +
        b * (∫ x in toType ⁻¹' Theta M, μ₂ (toType x) * TeschlODE.HigherDim.divergence φ x) ≤
        a * V0 M + b * V0 M :=
      add_le_add (mul_le_mul_of_nonneg_left t1 ha) (mul_le_mul_of_nonneg_left t2 hb)
    calc _ ≤ a * V0 M + b * V0 M := this
      _ = V0 M := by rw [← add_mul, hab, one_mul]

lemma X0L_nonempty (M : Model) (hM : M.Standing) : (X0L M).Nonempty := by
  have hc : 0 ≤ omega M / M.Bmin := div_nonneg (CAC.omega_nonneg M hM) hM.Bmin_pos.le
  have hV0 : 0 ≤ V0 M := by
    unfold V0
    have := CAC.omega_nonneg M hM
    have := hM.Bmin_pos
    have : 0 ≤ max (M.U ^ M.d) (M.U ^ (M.d + 1)) := le_max_of_le_left (pow_nonneg hM.U_pos.le _)
    positivity
  refine ⟨0, fun _ => 0, ⟨⟨⟨measurable_const, fun _ _ => le_refl 0⟩, integrableOn_zero,
    fun _ _ => ⟨le_refl 0, hc⟩⟩, ?_⟩, Lp.coeFn_zero _ _ _⟩
  unfold Vtheta totalVariation
  apply iSup₂_le
  intro φ _
  simp only [zero_mul, integral_zero]
  exact EReal.coe_le_coe_iff.mpr hV0

lemma coe_comb (M : Model) (g₁ g₂ : L1Theta M) (a b : ℝ) :
    ((a • g₁ + b • g₂ : L1Theta M) : (Fin M.d → ℝ) × ℝ → ℝ) =ᵐ[volume.restrict (Theta M)]
      fun θ => a * g₁ θ + b * g₂ θ := by
  filter_upwards [Lp.coeFn_add (a • g₁) (b • g₂), Lp.coeFn_smul a g₁, Lp.coeFn_smul b g₂]
    with θ h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  rfl

lemma X0L_convex (M : Model) (hM : M.Standing) : Convex ℝ (X0L M) := by
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  obtain ⟨μ₁, h₁, e₁⟩ := hg₁
  obtain ⟨μ₂, h₂, e₂⟩ := hg₂
  refine ⟨fun θ => a * μ₁ θ + b * μ₂ θ, X0_convex M hM h₁ h₂ ha hb hab, ?_⟩
  filter_upwards [coe_comb M g₁ g₂ a b, e₁, e₂] with θ h h1 h2
  rw [h, h1, h2]

/-- convexity of `f(g, ·)` along `X₀` -/
lemma fL_convex (M : Model) (hM : M.Standing) {g h₁ h₂ : L1Theta M} (hg : g ∈ X0L M)
    (hh₁ : h₁ ∈ X0L M) (hh₂ : h₂ ∈ X0L M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    fL M g (a • h₁ + b • h₂) ≤ a * fL M g h₁ + b * fL M g h₂ := by
  have := hM.probG
  obtain ⟨μg, hμg, eg⟩ := hg
  obtain ⟨μ₁, h₁X, e₁⟩ := hh₁
  obtain ⟨μ₂, h₂X, e₂⟩ := hh₂
  have hcomb := X0_convex M hM h₁X h₂X ha hb hab
  have ek : ((a • h₁ + b • h₂ : L1Theta M) : (Fin M.d → ℝ) × ℝ → ℝ) =ᵐ[volume.restrict (Theta M)]
      fun θ => a * μ₁ θ + b * μ₂ θ := by
    filter_upwards [coe_comb M h₁ h₂ a b, e₁, e₂] with θ h h1 h2
    rw [h, h1, h2]
  unfold fL
  rw [CAC.fObj_congr M hM (CAC.ae_G_of_ae_vol M hM eg) (CAC.ae_G_of_ae_vol M hM ek),
    CAC.fObj_congr M hM (CAC.ae_G_of_ae_vol M hM eg) (CAC.ae_G_of_ae_vol M hM e₁),
    CAC.fObj_congr M hM (CAC.ae_G_of_ae_vol M hM eg) (CAC.ae_G_of_ae_vol M hM e₂)]
  unfold fObj
  have i0 := CAC.integrable_q M hM μg hμg.1.1 _ hcomb.1.1.1 hcomb.1.2.2
  have i1 := CAC.integrable_q M hM μg hμg.1.1 _ h₁X.1.1.1 h₁X.1.2.2
  have i2 := CAC.integrable_q M hM μg hμg.1.1 _ h₂X.1.1.1 h₂X.1.2.2
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul a)
    (i2.const_mul b)]
  apply integral_mono_ae i0 ((i1.const_mul a).add (i2.const_mul b))
  have hΘ : ∀ᵐ θ ∂M.G, θ ∈ Theta M := ae_iff.mpr hM.G_Theta
  filter_upwards [hΘ] with θ hθ
  have hcv := (CAC.convex_q M hM μg hμg.1.1.1 hθ).2
    (show μ₁ θ ∈ Set.Ioi (-1) from by have := (h₁X.1.2.2 θ hθ).1; simp only [mem_Ioi]; linarith)
    (show μ₂ θ ∈ Set.Ioi (-1) from by have := (h₂X.1.2.2 θ hθ).1; simp only [mem_Ioi]; linarith)
    ha hb hab
  simpa [smul_eq_mul] using hcv

theorem lemma4_main (M : Model) (hM : M.Standing) :
    ((X0L M).Nonempty ∧ IsCompact (X0L M) ∧ Convex ℝ (X0L M)) ∧
      ContinuousOn (fun p : L1Theta M × L1Theta M => fL M p.1 p.2) (X0L M ×ˢ X0L M) ∧
      (UpperHemicontinuousOn (C0starL M) (X0L M) ∧
        ∀ g ∈ X0L M, (C0starL M g).Nonempty ∧ Convex ℝ (C0starL M g) ∧
          IsCompact (C0starL M g)) := by
  have hcpt := lemma_4_compact M hM
  have hcont := lemma_4_continuous M hM
  have hcl : IsClosed (X0L M) := hcpt.isClosed
  have hne := X0L_nonempty M hM
  have hcv := X0L_convex M hM
  -- continuity in the second argument
  have hcont2 : ∀ g ∈ X0L M, ContinuousOn (fun h => fL M g h) (X0L M) := by
    intro g hg
    have : ContinuousOn (fun h : L1Theta M => ((g, h) : L1Theta M × L1Theta M)) (X0L M) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h1 : ContinuousOn ((fun p : L1Theta M × L1Theta M => fL M p.1 p.2) ∘
        (fun h : L1Theta M => ((g, h) : L1Theta M × L1Theta M))) (X0L M) :=
      hcont.comp this (fun h hh => Set.mk_mem_prod hg hh)
    exact h1
  -- values
  have hvals : ∀ g ∈ X0L M, (C0starL M g).Nonempty ∧ Convex ℝ (C0starL M g) ∧
      IsCompact (C0starL M g) := by
    intro g hg
    obtain ⟨h₀, hh₀, hmin⟩ := hcpt.exists_isMinOn hne (hcont2 g hg)
    have hC : C0starL M g = X0L M ∩ (fun h => fL M g h) ⁻¹' Set.Iic (fL M g h₀) := by
      ext h
      constructor
      · rintro ⟨hh, hle⟩
        exact ⟨hh, hle h₀ hh₀⟩
      · rintro ⟨hh, hle⟩
        exact ⟨hh, fun k hk => le_trans hle (hmin hk)⟩
    refine ⟨⟨h₀, hh₀, fun k hk => hmin hk⟩, ?_, ?_⟩
    · intro h₁ hh₁ h₂ hh₂ a b ha hb hab
      refine ⟨hcv hh₁.1 hh₂.1 ha hb hab, fun k hk => ?_⟩
      have e := fL_convex M hM hg hh₁.1 hh₂.1 ha hb hab
      have e1 := hh₁.2 k hk
      have e2 := hh₂.2 k hk
      have : a * fL M g h₁ + b * fL M g h₂ ≤ a * fL M g k + b * fL M g k :=
        add_le_add (mul_le_mul_of_nonneg_left e1 ha) (mul_le_mul_of_nonneg_left e2 hb)
      have h3 : a * fL M g k + b * fL M g k = fL M g k := by rw [← add_mul, hab, one_mul]
      linarith
    · rw [hC]
      exact hcpt.of_isClosed_subset
        ((hcont2 g hg).preimage_isClosed_of_isClosed hcl isClosed_Iic) inter_subset_left
  refine ⟨⟨hne, hcpt, hcv⟩, hcont, ?_, hvals⟩
  -- upper hemicontinuity (Berge)
  intro g₀ hg₀ t ht
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨x, hx, hfx⟩ := exists_seq_forall_of_frequently hcon
  have hxX : ∀ᶠ n in atTop, x n ∈ X0L M := (tendsto_nhdsWithin_iff.mp hx).2
  have hx' : Tendsto x atTop (𝓝 g₀) := tendsto_nhdsWithin_iff.mp hx |>.1
  -- pick bad points
  have hbad : ∀ n, ∃ y, y ∈ C0starL M (x n) ∧ y ∉ interior t := by
    intro n
    have : ¬ t ∈ 𝓝ˢ (C0starL M (x n)) := hfx n
    rw [← subset_interior_iff_mem_nhdsSet, Set.not_subset] at this
    exact this
  choose y hy hyt using hbad
  obtain ⟨N, hN⟩ := eventually_atTop.mp hxX
  have hyX : ∀ n, y (n + N) ∈ X0L M := fun n => (hy (n + N)).1
  obtain ⟨y₀, hy₀, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hyX
  have hxlim : Tendsto (fun n => x (φ n + N)) atTop (𝓝 g₀) :=
    hx'.comp (tendsto_atTop_mono (fun n => Nat.le_add_right (φ n) N) hφ.tendsto_atTop)
  -- the limit point is optimal for g₀
  have hopt : y₀ ∈ C0starL M g₀ := by
    refine ⟨hy₀, fun k hk => ?_⟩
    have hpair : Tendsto (fun n => ((x (φ n + N), y (φ n + N)) : L1Theta M × L1Theta M)) atTop
        (𝓝[X0L M ×ˢ X0L M] (g₀, y₀)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hxlim.prodMk_nhds hlim, Eventually.of_forall fun n => ⟨hN _ (by omega), hyX _⟩⟩
    have hpair2 : Tendsto (fun n => ((x (φ n + N), k) : L1Theta M × L1Theta M)) atTop
        (𝓝[X0L M ×ˢ X0L M] (g₀, k)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hxlim.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n => ⟨hN _ (by omega), hk⟩⟩
    have l1 := ((hcont (g₀, y₀) ⟨hg₀, hy₀⟩).tendsto).comp hpair
    have l2 := ((hcont (g₀, k) ⟨hg₀, hk⟩).tendsto).comp hpair2
    exact le_of_tendsto_of_tendsto' l1 l2 fun n => (hy (φ n + N)).2 k hk
  have hsub : C0starL M g₀ ⊆ interior t := subset_interior_iff_mem_nhdsSet.mpr ht
  have hclosed : IsClosed (interior t)ᶜ := isOpen_interior.isClosed_compl
  have : y₀ ∈ (interior t)ᶜ :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => hyt (φ n + N))
  exact this (hsub hopt)

end L4


theorem solution (M : Model) (hM : M.Standing) :
    ((X0L M).Nonempty ∧ IsCompact (X0L M) ∧ Convex ℝ (X0L M)) ∧
      ContinuousOn (fun p : L1Theta M × L1Theta M => fL M p.1 p.2) (X0L M ×ˢ X0L M) ∧
      (UpperHemicontinuousOn (C0starL M) (X0L M) ∧
        ∀ g ∈ X0L M, (C0starL M g).Nonempty ∧ Convex ℝ (C0starL M g) ∧
          IsCompact (C0starL M g)) :=
  L4.lemma4_main M hM
