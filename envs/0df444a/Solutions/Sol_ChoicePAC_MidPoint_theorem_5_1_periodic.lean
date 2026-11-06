-- Prove2me | solution 1 for ChoicePAC.MidPoint.theorem_5_1_periodic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:22:33.821203+00:00
-- url     : https://prove2.me/submissions/f15cd966-d705-48e2-904d-0fa873b249c5
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

namespace PerAux

open CorAux

lemma exp_neg_le' (x : ℝ) (hx : 0 < x) : Real.exp (-x) ≤ 24 / x ^ 4 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 4
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4] at h
  rw [Real.exp_neg, le_div_iff₀ (by positivity)]
  have hpos := Real.exp_pos x
  rw [inv_mul_eq_div, div_le_iff₀ hpos]
  linarith

lemma card_filter_lt (M b : ℕ) (hb : b ≤ M) :
    (Finset.univ.filter (fun l : Fin M => l.val < b)).card = b := by
  have : (Finset.univ.filter (fun l : Fin M => l.val < b)) =
      (Finset.range b).attachFin (fun i hi => by simp at hi; omega) := by
    ext l; simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- `G(k, t) ≤ 2h + 2(1 − t)` for the periodic schedule. -/
lemma periodic_G (h : ℝ) (hh : 0 < h) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (periodicSchedule h hh).G t ≤ 2 * h + 2 * (1 - t) := by
  classical
  set s := periodicSchedule h hh with hs
  have htime : ∀ j, j ≤ s.M → s.time j = (j : ℝ) * h := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp [Schedule.time]
    · rw [time_succ s j hpos hj]
      show (((j - 1 : ℕ) : ℝ) + 1) * h = _
      rw [Nat.cast_sub hpos]; push_cast; ring
  have hlt : ∀ j, 1 ≤ j → j ≤ s.M → (j : ℝ) * h < 1 := by
    intro j h1 hj; rw [← htime j hj]; exact time_lt_one s j hj
  unfold Schedule.G Schedule.idx
  set a := (Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t)).card with ha
  rw [Nat.add_sub_cancel]
  have haM : a ≤ s.M := by
    have := Finset.card_le_univ (Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t))
    simpa using this
  have hj : ∀ j, 1 ≤ j → j ≤ a → s.time j ≤ t := by
    intro j h1 hja
    rw [time_succ s j h1 (hja.trans haM)]
    by_contra hlt'
    push Not at hlt'
    have hsub : Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t) ⊆
        Finset.univ.filter (fun l : Fin s.M => l.val < j - 1) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      have : s.t l < s.t ⟨j - 1, by omega⟩ := lt_of_le_of_lt hl hlt'
      exact s.strictMono.lt_iff_lt.mp this
    have hc := Finset.card_le_card hsub
    rw [card_filter_lt _ _ (by omega), ← ha] at hc
    omega
  have hah : (a : ℝ) * h ≤ t := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0]; simp; exact ht0
    · rw [← htime a haM]; exact hj a hpos le_rfl
  -- the last partial window
  have hlast : t ≤ ((a : ℝ) + 1) * h := by
    rcases Nat.lt_or_ge a s.M with haM' | haM'
    · by_contra hcon
      push Not at hcon
      have hsub : Finset.univ.filter (fun l : Fin s.M => l.val < a + 1) ⊆
          Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t) := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
        show ((l.val : ℝ) + 1) * h ≤ t
        have : (l.val : ℝ) + 1 ≤ (a : ℝ) + 1 := by
          have : (l.val : ℝ) ≤ a := by exact_mod_cast (by omega : l.val ≤ a)
          linarith
        nlinarith
      have hc := Finset.card_le_card hsub
      rw [card_filter_lt _ _ (by omega), ← ha] at hc
      omega
    · have haeq : a = s.M := le_antisymm haM haM'
      rw [haeq]
      have hM : s.M = Nat.ceil (1 / h) - 1 := rfl
      have hceil : 1 ≤ Nat.ceil (1 / h) := Nat.one_le_iff_ne_zero.mpr (by
        intro h0; rw [Nat.ceil_eq_zero] at h0; have : 0 < 1 / h := by positivity
        linarith)
      have hc : ((s.M : ℕ) : ℝ) + 1 = (Nat.ceil (1 / h) : ℝ) := by
        rw [hM]; push_cast [Nat.cast_sub hceil]; ring
      rw [hc]
      have := Nat.le_ceil (1 / h)
      have h1 : 1 ≤ (Nat.ceil (1 / h) : ℝ) * h := by
        rw [div_le_iff₀ hh] at this; linarith
      linarith
  have hfirst : t - s.time a ≤ h := by
    rw [htime a haM]; nlinarith
  -- the sum
  have hsumeq : ∑ j ∈ Finset.Icc 1 a, (s.time j - s.time (j - 1)) * (1 - t) ^ 2 /
      (1 - s.time j) ^ 2 = ∑ j ∈ Finset.Icc 1 a, h * (1 - t) ^ 2 / (1 - (j : ℝ) * h) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hjm
    rw [Finset.mem_Icc] at hjm
    rw [htime j (hjm.2.trans haM), htime (j - 1) (by omega), Nat.cast_sub hjm.1]
    push_cast; ring_nf
  have hsum : ∑ j ∈ Finset.Icc 1 a, h * (1 - t) ^ 2 / (1 - (j : ℝ) * h) ^ 2 ≤
      h + 2 * (1 - t) := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0]; simp; linarith
    obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [hb] at haM hah ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    -- top term
    have hbh : ((b + 1 : ℕ) : ℝ) * h < 1 := hlt (b + 1) (by omega) haM
    have htop : h * (1 - t) ^ 2 / (1 - ((b + 1 : ℕ) : ℝ) * h) ^ 2 ≤ h := by
      have hz : 0 < 1 - ((b + 1 : ℕ) : ℝ) * h := by linarith
      rw [div_le_iff₀ (by positivity)]
      have : (1 - t) ^ 2 ≤ (1 - ((b + 1 : ℕ) : ℝ) * h) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith
    -- the other terms telescope
    have hrest : ∑ j ∈ Finset.Icc 1 b, h * (1 - t) ^ 2 / (1 - (j : ℝ) * h) ^ 2 ≤
        (1 - t) ^ 2 * (2 * ∑ j ∈ Finset.Icc 1 b,
          (1 / (1 - (j : ℝ) * h) - 1 / (1 - ((j - 1 : ℕ) : ℝ) * h))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hjm
      rw [Finset.mem_Icc] at hjm
      have hj1 : ((j + 1 : ℕ) : ℝ) * h < 1 := hlt (j + 1) (by omega) (by omega)
      push_cast at hj1
      set x := 1 - (j : ℝ) * h with hx
      have hxh : h < x := by rw [hx]; nlinarith
      have hy : 1 - ((j - 1 : ℕ) : ℝ) * h = x + h := by
        rw [Nat.cast_sub hjm.1, hx]; push_cast; ring
      rw [hy]
      have hxpos : 0 < x := by linarith
      rw [div_le_iff₀ (by positivity)]
      have key : 1 / x - 1 / (x + h) = h / (x * (x + h)) := by
        field_simp; ring
      rw [key]
      have h2 : h / (x * (x + h)) * x ^ 2 = h * x / (x + h) := by
        field_simp
      have h3 : 2 * (h * x / (x + h)) ≥ h := by
        rw [ge_iff_le, ← sub_nonneg]
        have : 2 * (h * x / (x + h)) - h = h * (x - h) / (x + h) := by field_simp; ring
        rw [this]; apply div_nonneg _ (by linarith); nlinarith
      have hsq : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
      calc h * (1 - t) ^ 2 = (1 - t) ^ 2 * h := by ring
        _ ≤ (1 - t) ^ 2 * (2 * (h * x / (x + h))) := mul_le_mul_of_nonneg_left h3 hsq
        _ = (1 - t) ^ 2 * (2 * (h / (x * (x + h)))) * x ^ 2 := by
            rw [show (1 - t) ^ 2 * (2 * (h / (x * (x + h)))) * x ^ 2 =
              (1 - t) ^ 2 * (2 * (h / (x * (x + h)) * x ^ 2)) by ring, h2]
    rw [telescope (fun j => 1 / (1 - (j : ℝ) * h))] at hrest
    simp only [Nat.cast_zero, zero_mul, sub_zero, div_one] at hrest
    have hbt : (b : ℝ) * h ≤ t := by
      have : (b : ℝ) * h ≤ ((b + 1 : ℕ) : ℝ) * h := by
        push_cast; nlinarith
      linarith
    have hz : 1 - t ≤ 1 - (b : ℝ) * h := by linarith
    have hzpos : 0 < 1 - (b : ℝ) * h := by
      have : ((b + 1 : ℕ) : ℝ) * h < 1 := hbh
      push_cast at this; nlinarith
    have hrest2 : (1 - t) ^ 2 * (2 * (1 / (1 - (b : ℝ) * h) - 1)) ≤ 2 * (1 - t) := by
      have h1 : (1 - t) ^ 2 * (1 / (1 - (b : ℝ) * h)) ≤ 1 - t := by
        rw [mul_one_div, div_le_iff₀ hzpos]
        have : 0 ≤ 1 - t := by linarith
        nlinarith
      nlinarith [sq_nonneg (1 - t)]
    linarith
  rw [hsumeq]
  linarith

end PerAux

namespace PerAux

lemma integrand_bound (k : ℕ) (hk : 1 ≤ k) (h : ℝ) (hh : 0 < h) (c0 ρ' D : ℝ) (hc0 : 0 < c0)
    (hρ' : 0 < ρ') (hD1 : 1 ≤ D) (hD : ρ' * Real.exp (4 * c0 ^ 2) * 24 / c0 ^ 4 ≤ D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min 1 (ρ' * (periodicSchedule h hh).F k
      (c0 / Real.sqrt (max 1 ((k : ℝ) * max (1 - t) h))) t) ≤
      2 * D / (1 + ((k : ℝ) - (k : ℝ) * t) ^ 2) +
        ρ' * Real.exp (4 * c0 ^ 2) *
          Real.exp (c0 * Real.sqrt k / Real.sqrt h * t + -(c0 * Real.sqrt k / Real.sqrt h)) := by
  set u : ℝ := (k : ℝ) * (1 - t) with hu
  have hu' : (k : ℝ) - (k : ℝ) * t = u := by rw [hu]; ring
  rw [hu']
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) (by linarith)
  set w := max (1 - t) h with hw
  have hwpos : 0 < w := lt_of_lt_of_le hh (le_max_right _ _)
  have hG := periodic_G h hh t ht0 ht1
  have hG4 : (periodicSchedule h hh).G t ≤ 4 * w := by
    have := le_max_left (1 - t) h; have := le_max_right (1 - t) h; linarith
  set A := ρ' * Real.exp (4 * c0 ^ 2) with hA
  set β := c0 * Real.sqrt k / Real.sqrt h with hβ
  have hh2 : 0 ≤ A * Real.exp (β * t + -β) := by positivity
  have hh1 : 0 ≤ 2 * D / (1 + u ^ 2) := by
    have : (0 : ℝ) ≤ D := by linarith
    positivity
  by_cases hU : 1 ≤ (k : ℝ) * w
  · rw [max_eq_right hU]
    set U := (k : ℝ) * w with hUdef
    set v := c0 / Real.sqrt U with hv
    have hsq : 0 < Real.sqrt U := Real.sqrt_pos.mpr (by linarith)
    have hsU : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt (by linarith)
    have hkv2 : (k : ℝ) * v ^ 2 * w = c0 ^ 2 := by
      rw [hv, div_pow, Real.sq_sqrt (by linarith)]
      field_simp
      rw [hUdef]
    have hA1 : (k : ℝ) * v ^ 2 * (periodicSchedule h hh).G t ≤ 4 * c0 ^ 2 := by
      calc (k : ℝ) * v ^ 2 * (periodicSchedule h hh).G t ≤ (k : ℝ) * v ^ 2 * (4 * w) :=
            mul_le_mul_of_nonneg_left hG4 (by positivity)
        _ = 4 * ((k : ℝ) * v ^ 2 * w) := by ring
        _ = 4 * c0 ^ 2 := by rw [hkv2]
    by_cases hth : h ≤ 1 - t
    · have hw' : w = 1 - t := max_eq_left hth
      have hUu : U = u := by rw [hUdef, hw', hu]
      have hu1 : 1 ≤ u := by rw [← hUu]; exact hU
      have hkv : (k : ℝ) * v * (1 - t) = c0 * Real.sqrt u := by
        rw [hv, hUu]
        have hsu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
        have hsupos : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
        field_simp
        nlinarith
      have hexp : (k : ℝ) * v ^ 2 * (periodicSchedule h hh).G t - (k : ℝ) * v * (1 - t) ≤
          4 * c0 ^ 2 + -(c0 * Real.sqrt u) := by rw [hkv]; linarith
      have hsu0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
      have hF : (periodicSchedule h hh).F k v t ≤
          Real.exp (4 * c0 ^ 2) * (24 / (c0 * Real.sqrt u) ^ 4) := by
        unfold Schedule.F
        calc Real.exp ((k : ℝ) * v ^ 2 * (periodicSchedule h hh).G t - (k : ℝ) * v * (1 - t))
            ≤ Real.exp (4 * c0 ^ 2 + -(c0 * Real.sqrt u)) := Real.exp_le_exp.mpr hexp
          _ = Real.exp (4 * c0 ^ 2) * Real.exp (-(c0 * Real.sqrt u)) := Real.exp_add _ _
          _ ≤ Real.exp (4 * c0 ^ 2) * (24 / (c0 * Real.sqrt u) ^ 4) :=
              mul_le_mul_of_nonneg_left (exp_neg_le' _ (by positivity)) (Real.exp_pos _).le
      have hpow : (c0 * Real.sqrt u) ^ 4 = c0 ^ 4 * u ^ 2 := by
        have : Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 := by ring
        rw [mul_pow, this, Real.sq_sqrt hu0]
      rw [hpow] at hF
      have h1 : ρ' * (periodicSchedule h hh).F k v t ≤ D / u ^ 2 := by
        calc ρ' * (periodicSchedule h hh).F k v t
            ≤ ρ' * (Real.exp (4 * c0 ^ 2) * (24 / (c0 ^ 4 * u ^ 2))) :=
              mul_le_mul_of_nonneg_left hF hρ'.le
          _ = (ρ' * Real.exp (4 * c0 ^ 2) * 24 / c0 ^ 4) / u ^ 2 := by field_simp
          _ ≤ D / u ^ 2 := div_le_div_of_nonneg_right hD (by positivity)
      have h2 : D / u ^ 2 ≤ 2 * D / (1 + u ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 1 + u ^ 2 ≤ 2 * u ^ 2 := by nlinarith
        nlinarith
      exact le_add_of_le_of_nonneg (le_trans (min_le_right _ _) (h1.trans h2)) hh2
    · push Not at hth
      have hw' : w = h := max_eq_right hth.le
      have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
      have hsU' : Real.sqrt U = Real.sqrt (k : ℝ) * Real.sqrt h := by
        rw [hUdef, hw', Real.sqrt_mul (by linarith)]
      have hkv : (k : ℝ) * v * (1 - t) = β * (1 - t) := by
        have hkk : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = k := Real.mul_self_sqrt (by linarith)
        have hq : (k : ℝ) / (Real.sqrt (k : ℝ) * Real.sqrt h) = Real.sqrt (k : ℝ) / Real.sqrt h := by
          calc (k : ℝ) / (Real.sqrt (k : ℝ) * Real.sqrt h)
              = (Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ)) / (Real.sqrt (k : ℝ) * Real.sqrt h) := by
                rw [hkk]
            _ = Real.sqrt (k : ℝ) / Real.sqrt h := mul_div_mul_left _ _ hsk.ne'
        rw [hv, hsU', hβ]
        calc (k : ℝ) * (c0 / (Real.sqrt (k : ℝ) * Real.sqrt h)) * (1 - t)
            = c0 * ((k : ℝ) / (Real.sqrt (k : ℝ) * Real.sqrt h)) * (1 - t) := by ring
          _ = c0 * Real.sqrt (k : ℝ) / Real.sqrt h * (1 - t) := by rw [hq]; ring
      have hexp : (k : ℝ) * v ^ 2 * (periodicSchedule h hh).G t - (k : ℝ) * v * (1 - t) ≤
          4 * c0 ^ 2 + (β * t + -β) := by rw [hkv]; linarith
      have hF : ρ' * (periodicSchedule h hh).F k v t ≤ A * Real.exp (β * t + -β) := by
        unfold Schedule.F
        calc ρ' * Real.exp ((k : ℝ) * v ^ 2 * (periodicSchedule h hh).G t - (k : ℝ) * v * (1 - t))
            ≤ ρ' * Real.exp (4 * c0 ^ 2 + (β * t + -β)) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hρ'.le
          _ = A * Real.exp (β * t + -β) := by rw [hA, Real.exp_add]; ring
      exact le_add_of_nonneg_of_le hh1 (le_trans (min_le_right _ _) hF)
  · have hU' : (k : ℝ) * w < 1 := lt_of_not_ge hU
    have hule : u ≤ 1 := by
      have : u ≤ (k : ℝ) * w :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
      linarith
    have hu2 : u ^ 2 ≤ 1 := by
      have := mul_le_mul hule hule hu0 zero_le_one
      rw [sq]; linarith
    have : 1 ≤ 2 * D / (1 + u ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact le_add_of_le_of_nonneg (le_trans (min_le_left _ _) this) hh2

end PerAux

theorem solution {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) :
    ∃ ρ ρhat : ℝ, 0 < ρ ∧ 0 < ρhat ∧
      ∀ h : ℝ, ∀ hh : 0 < h, ∀ k : ℕ, 1 ≤ k → ∀ sel, I.IsAdmissibleSelector sel →
        I.dlpValue ((k : ℝ) • I.C) ((k : ℝ) • I.lam) - I.pacValue sel k (periodicSchedule h hh) ≤
          ρ + ρhat * Real.sqrt (k * h) := by
  obtain ⟨ρ, ρhat, ρ', hρ, hρhat, hρ', h53⟩ := theorem_5_3_general_bound I hI h21 h22
  set c0 : ℝ := 1 / (1 + |I.ξmax|) with hc0
  have hc0pos : 0 < c0 := by positivity
  have hc0le : c0 ≤ 1 := by
    rw [hc0, div_le_one (by positivity)]; linarith [abs_nonneg I.ξmax]
  have hc0ξ : c0 * I.ξmax ≤ 1 := by
    rw [hc0, one_div_mul_eq_div, div_le_one (by positivity)]
    linarith [le_abs_self I.ξmax]
  set D : ℝ := max 1 (ρ' * Real.exp (4 * c0 ^ 2) * 24 / c0 ^ 4) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  set A : ℝ := ρ' * Real.exp (4 * c0 ^ 2) with hA
  have hApos : 0 < A := by positivity
  refine ⟨ρ + ρhat * (D * Real.pi), ρhat * A / c0, by positivity, by positivity, ?_⟩
  intro h hh k hk sel hsel
  set v : ℕ → ℝ → ℝ := fun k t => c0 / Real.sqrt (max 1 ((k : ℝ) * max (1 - t) h)) with hv
  have hvprop : ∀ k' : ℕ, 1 ≤ k' → ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 < v k' t ∧ v k' t ≤ 1 ∧ v k' t * I.ξmax ≤ 1 := by
    intro k' _ t _ _
    have hs : 1 ≤ Real.sqrt (max 1 ((k' : ℝ) * max (1 - t) h)) := by
      rw [Real.one_le_sqrt]; exact le_max_left _ _
    have hspos : 0 < Real.sqrt (max 1 ((k' : ℝ) * max (1 - t) h)) := by linarith
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
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      have : 1 ≤ Real.sqrt (max 1 ((k' : ℝ) * max (1 - t) h)) := by
        rw [Real.one_le_sqrt]; exact le_max_left _ _
      linarith
  have hmain := h53 k hk (periodicSchedule h hh) v hvprop hvint sel hsel
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  set β := c0 * Real.sqrt k / Real.sqrt h with hβ
  have hβpos : 0 < β := by positivity
  set f : ℝ → ℝ := fun t => min 1 (ρ' * (periodicSchedule h hh).F k (v k t) t) with hf
  set g1 : ℝ → ℝ := fun t => 2 * D / (1 + ((k : ℝ) - (k : ℝ) * t) ^ 2) with hg1
  set g2 : ℝ → ℝ := fun t => A * Real.exp (β * t + -β) with hg2
  have hg1int : IntervalIntegrable g1 volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by fun_prop)
    intro t; positivity
  have hg2int : IntervalIntegrable g2 volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hg1val : ∫ t in (0 : ℝ)..1, g1 t = 2 * D * (k : ℝ)⁻¹ * Real.arctan k := by
    have e := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
      (fun x : ℝ => 2 * D * (1 + x ^ 2)⁻¹) (ne_of_gt hk0) (k : ℝ)
    simp only [mul_one, mul_zero, sub_self, sub_zero] at e
    have hI0 : ∫ x in (0 : ℝ)..(k : ℝ), (1 + x ^ 2)⁻¹ = Real.arctan k := by
      simpa using (integral_inv_one_add_sq (a := (0 : ℝ)) (b := (k : ℝ)))
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI0,
      smul_eq_mul] at e
    have : (fun t : ℝ => g1 t) = fun x => 2 * D * (1 + ((k : ℝ) - (k : ℝ) * x) ^ 2)⁻¹ := by
      funext t; simp only [hg1, div_eq_mul_inv]
    rw [this, intervalIntegral.integral_const_mul, e]; ring
  have hg2val : ∫ t in (0 : ℝ)..1, g2 t = A * (β⁻¹ * (1 - Real.exp (-β))) := by
    simp only [hg2]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add (fun x => Real.exp x) hβpos.ne', integral_exp]
    simp
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ g1 t + g2 t := by
    intro t ht
    exact PerAux.integrand_bound k hk h hh c0 ρ' D hc0pos hρ' hD1 (le_max_right _ _) t ht.1 ht.2
  have hfg : ∫ t in (0 : ℝ)..1, f t ≤ ∫ t in (0 : ℝ)..1, (g1 t + g2 t) := by
    by_cases hfint : IntervalIntegrable f volume 0 1
    · exact intervalIntegral.integral_mono_on (by norm_num) hfint (hg1int.add hg2int) hpt
    · rw [intervalIntegral.integral_undef hfint, intervalIntegral.integral_add hg1int hg2int,
        hg1val, hg2val]
      have : 0 ≤ Real.arctan k := by
        rw [← Real.arctan_zero]; exact Real.arctan_mono hk0.le
      have : 0 ≤ 1 - Real.exp (-β) := by
        have : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      have : (0 : ℝ) ≤ D := by linarith
      positivity
  rw [intervalIntegral.integral_add hg1int hg2int, hg1val, hg2val] at hfg
  have hkβ : (k : ℝ) * β⁻¹ = Real.sqrt (k * h) / c0 := by
    rw [hβ, Real.sqrt_mul hk0.le]
    have : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    field_simp
    nlinarith
  have hkint : (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤ D * Real.pi + A / c0 * Real.sqrt (k * h) := by
    have h1 : (k : ℝ) * (2 * D * (k : ℝ)⁻¹ * Real.arctan k) ≤ D * Real.pi := by
      have : (k : ℝ) * (2 * D * (k : ℝ)⁻¹ * Real.arctan k) = 2 * D * Real.arctan k := by
        field_simp
      rw [this]
      have : (0 : ℝ) ≤ D := by linarith
      nlinarith [Real.arctan_lt_pi_div_two (k : ℝ)]
    have h2 : (k : ℝ) * (A * (β⁻¹ * (1 - Real.exp (-β)))) ≤ A / c0 * Real.sqrt (k * h) := by
      have : (k : ℝ) * (A * (β⁻¹ * (1 - Real.exp (-β)))) =
          A * ((k : ℝ) * β⁻¹) * (1 - Real.exp (-β)) := by ring
      rw [this, hkβ]
      have hp : 0 ≤ A * (Real.sqrt (k * h) / c0) := by positivity
      have := Real.exp_pos (-β)
      calc A * (Real.sqrt (k * h) / c0) * (1 - Real.exp (-β)) ≤ A * (Real.sqrt (k * h) / c0) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) hp
        _ = A / c0 * Real.sqrt (k * h) := by ring
    calc (k : ℝ) * ∫ t in (0 : ℝ)..1, f t
        ≤ (k : ℝ) * (2 * D * (k : ℝ)⁻¹ * Real.arctan k + A * (β⁻¹ * (1 - Real.exp (-β)))) :=
          mul_le_mul_of_nonneg_left hfg hk0.le
      _ ≤ D * Real.pi + A / c0 * Real.sqrt (k * h) := by rw [mul_add]; linarith
  have : ρhat * (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤
      ρhat * (D * Real.pi) + ρhat * A / c0 * Real.sqrt (k * h) := by
    rw [mul_assoc]
    calc ρhat * ((k : ℝ) * ∫ t in (0 : ℝ)..1, f t)
        ≤ ρhat * (D * Real.pi + A / c0 * Real.sqrt (k * h)) :=
          mul_le_mul_of_nonneg_left hkint hρhat.le
      _ = ρhat * (D * Real.pi) + ρhat * A / c0 * Real.sqrt (k * h) := by ring
  linarith
