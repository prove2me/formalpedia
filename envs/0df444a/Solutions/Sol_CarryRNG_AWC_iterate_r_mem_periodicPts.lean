-- Prove2me | solution 1 for CarryRNG.AWC.iterate_r_mem_periodicPts
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:18:52.53637+00:00
-- url     : https://prove2.me/submissions/fc92659a-ffa3-4352-b03b-24af752cd3b3

import Mathlib
import Definitions.Def_CarryRNG_AWC_step

set_option autoImplicit false

namespace CarryRNG.AWC

lemma state_eq {b r : ℕ} (z w : State b r) (hx : ∀ i, (z.x i).val = (w.x i).val)
    (hc : z.c.val = w.c.val) : z = w := by
  cases z with
  | mk zx zc =>
  cases w with
  | mk wx wc =>
    have h1 : zx = wx := funext (fun i => Fin.ext (hx i))
    have h2 : zc = wc := Fin.ext hc
    subst h1; subst h2; rfl

/-- the sum `t = x_{r-s} + x_1 + c` -/
def tsum (b : ℕ) (L : Lags) (z : State b L.r) : ℕ :=
  (z.x ⟨L.r - L.s, by have := L.hs; have := L.hsr; omega⟩).val
    + (z.x ⟨0, by have := L.hs; have := L.hsr; omega⟩).val + z.c.val

lemma step_x_lt (b : ℕ) (L : Lags) (z : State b L.r) (i : Fin L.r) (hi : i.val + 1 < L.r) :
    (step b L z).x i = z.x ⟨i.val + 1, hi⟩ := by
  unfold step
  simp only [hi, dif_pos]

lemma step_x_last (b : ℕ) (L : Lags) (z : State b L.r) (i : Fin L.r) (hi : ¬ i.val + 1 < L.r) :
    ((step b L z).x i).val = if tsum b L z < b then tsum b L z else tsum b L z - b := by
  unfold step tsum
  simp only [hi, dif_neg, not_false_eq_true]
  split_ifs <;> rfl

lemma step_c (b : ℕ) (L : Lags) (z : State b L.r) :
    (step b L z).c.val = if tsum b L z < b then 0 else 1 := by
  unfold step tsum
  simp only
  split_ifs <;> rfl

/-- digits as natural numbers, `0` out of range -/
def xv {b : ℕ} {L : Lags} (z : State b L.r) (i : ℕ) : ℕ :=
  if h : i < L.r then (z.x ⟨i, h⟩).val else 0

lemma xv_of_lt {b : ℕ} {L : Lags} (z : State b L.r) {i : ℕ} (h : i < L.r) :
    xv z i = (z.x ⟨i, h⟩).val := by simp [xv, h]

lemma xv_lt {b : ℕ} {L : Lags} (z : State b L.r) {i : ℕ} (h : i < L.r) : xv z i < b := by
  rw [xv_of_lt z h]; exact (z.x ⟨i, h⟩).isLt

lemma xv_step_lt (b : ℕ) (L : Lags) (z : State b L.r) {i : ℕ} (hi : i + 1 < L.r) :
    xv (step b L z) i = xv z (i + 1) := by
  rw [xv_of_lt _ (by omega), xv_of_lt z hi, step_x_lt b L z ⟨i, by omega⟩ hi]

lemma tsum_eq (b : ℕ) (L : Lags) (z : State b L.r) :
    tsum b L z = xv z (L.r - L.s) + xv z 0 + z.c.val := by
  have hs := L.hs
  have hsr := L.hsr
  unfold tsum
  rw [xv_of_lt z (by omega), xv_of_lt z (by omega)]

lemma xv_step_last (b : ℕ) (L : Lags) (z : State b L.r) :
    xv (step b L z) (L.r - 1) = if tsum b L z < b then tsum b L z else tsum b L z - b := by
  have hs := L.hs
  have hsr := L.hsr
  rw [xv_of_lt _ (by omega)]
  exact step_x_last b L z ⟨L.r - 1, by omega⟩ (by simp; omega)

def Asum {b : ℕ} {L : Lags} (z : State b L.r) : ℕ :=
  ∑ i ∈ Finset.range (L.r - L.s), xv z (L.s + i) * b ^ i

def Bsum {b : ℕ} {L : Lags} (z : State b L.r) : ℕ :=
  ∑ i ∈ Finset.range (L.r - L.s), xv z i * b ^ i

def Gp {b : ℕ} {L : Lags} (z : State b L.r) : Prop :=
  (z.c.val = 0 ∧ Bsum z ≤ Asum z) ∨ (z.c.val = 1 ∧ Asum z ≤ Bsum z)

lemma sum_digits_lt (b : ℕ) (d : ℕ → ℕ) (k : ℕ) (hd : ∀ i < k, d i < b) :
    ∑ i ∈ Finset.range k, d i * b ^ i < b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun i hi => hd i (by omega))
    have h2 := hd k (by omega)
    have h3 : (d k + 1) * b ^ k ≤ b * b ^ k := Nat.mul_le_mul_right _ (by omega)
    calc ∑ i ∈ Finset.range k, d i * b ^ i + d k * b ^ k < b ^ k + d k * b ^ k := by omega
      _ = (d k + 1) * b ^ k := by ring
      _ ≤ b * b ^ k := h3
      _ = b ^ (k + 1) := by ring


lemma digit_le (b x y u v : ℕ) (hx : x < b) (hy : y < b) (h : x + b * u ≤ y + b * v) : u ≤ v := by
  by_contra hlt
  have h1 : v + 1 ≤ u := by omega
  have h2 := Nat.mul_le_mul_left b h1
  rw [mul_add, mul_one] at h2
  omega

section decomp
variable {b : ℕ} {L : Lags}

lemma Bsum_decomp (z : State b L.r) (k : ℕ) (hk : L.r - L.s = k + 1) :
    Bsum z = xv z 0 + b * ∑ i ∈ Finset.range k, xv z (1 + i) * b ^ i := by
  unfold Bsum
  rw [hk, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm i 1]; ring

lemma Asum_decomp (z : State b L.r) (k : ℕ) (hk : L.r - L.s = k + 1) :
    Asum z = xv z L.s + b * ∑ i ∈ Finset.range k, xv z (L.s + 1 + i) * b ^ i := by
  unfold Asum
  rw [hk, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one, add_zero, pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show L.s + (i + 1) = L.s + 1 + i by omega]; ring

lemma Asum_step (z : State b L.r) (k : ℕ) (hk : L.r - L.s = k + 1) :
    Asum (step b L z) = (∑ i ∈ Finset.range k, xv z (L.s + 1 + i) * b ^ i)
      + xv (step b L z) (L.r - 1) * b ^ k := by
  have hs := L.hs
  have hsr := L.hsr
  unfold Asum
  rw [hk, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi := Finset.mem_range.1 hi
    rw [xv_step_lt b L z (by omega), show L.s + i + 1 = L.s + 1 + i by omega]
  · rw [show L.s + k = L.r - 1 by omega]

lemma Bsum_step (z : State b L.r) (k : ℕ) (hk : L.r - L.s = k + 1) :
    Bsum (step b L z) = (∑ i ∈ Finset.range k, xv z (1 + i) * b ^ i)
      + xv z (L.r - L.s) * b ^ k := by
  have hs := L.hs
  have hsr := L.hsr
  unfold Bsum
  rw [hk, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi := Finset.mem_range.1 hi
    rw [xv_step_lt b L z (by omega), add_comm i 1]
  · rw [xv_step_lt b L z (by omega)]

lemma Gp_step (z : State b L.r) (hz : Gp z) : Gp (step b L z) := by
  have hs := L.hs
  have hsr := L.hsr
  obtain ⟨k, hk⟩ : ∃ k, L.r - L.s = k + 1 := ⟨L.r - L.s - 1, by omega⟩
  have hA := Asum_decomp z k hk
  have hB := Bsum_decomp z k hk
  have hA' := Asum_step z k hk
  have hB' := Bsum_step z k hk
  set ã := ∑ i ∈ Finset.range k, xv z (L.s + 1 + i) * b ^ i with hã
  set β := ∑ i ∈ Finset.range k, xv z (1 + i) * b ^ i with hβ
  have hãP : ã < b ^ k := sum_digits_lt b _ k (fun i hi => xv_lt z (by omega))
  have hβP : β < b ^ k := sum_digits_lt b _ k (fun i hi => xv_lt z (by omega))
  set P := b ^ k with hP
  have hws : xv z L.s < b := xv_lt z (by omega)
  have hw0 : xv z 0 < b := xv_lt z (by omega)
  have hwm : xv z (L.r - L.s) < b := xv_lt z (by omega)
  have hc2 : z.c.val < 2 := z.c.isLt
  have hlast := xv_step_last b L z
  have hcs := step_c b L z
  rw [tsum_eq] at hlast hcs
  set ws := xv z L.s
  set w0 := xv z 0
  set wm := xv z (L.r - L.s)
  set wr := xv (step b L z) (L.r - 1)
  set c := z.c.val
  unfold Gp at hz ⊢
  rw [hA, hB] at hz
  rw [hA', hB', hcs]
  by_cases ht : wm + w0 + c < b
  · rw [if_pos ht] at hlast ⊢
    rcases hz with ⟨hc, hle⟩ | ⟨hc, hle⟩
    · left
      refine ⟨rfl, ?_⟩
      have h1 : β ≤ ã := digit_le b w0 ws β ã hw0 hws hle
      have h2 : wm * P ≤ wr * P := Nat.mul_le_mul_right _ (by omega)
      omega
    · left
      refine ⟨rfl, ?_⟩
      have h1 : ã ≤ β := digit_le b ws w0 ã β hws hw0 hle
      have h2 : wm * P + P ≤ wr * P := by
        have := Nat.mul_le_mul_right P (show wm + 1 ≤ wr by omega)
        rwa [add_mul, one_mul] at this
      omega
  · rw [if_neg ht] at hlast ⊢
    rcases hz with ⟨hc, hle⟩ | ⟨hc, hle⟩
    · right
      refine ⟨rfl, ?_⟩
      have h1 : β ≤ ã := digit_le b w0 ws β ã hw0 hws hle
      have h2 : wr * P + P ≤ wm * P := by
        have := Nat.mul_le_mul_right P (show wr + 1 ≤ wm by omega)
        rwa [add_mul, one_mul] at this
      omega
    · right
      refine ⟨rfl, ?_⟩
      have h1 : ã ≤ β := digit_le b ws w0 ã β hws hw0 hle
      have h2 : wr * P ≤ wm * P := Nat.mul_le_mul_right _ (by omega)
      omega


lemma tsum_eq_step (z : State b L.r) :
    tsum b L z = xv (step b L z) (L.r - 1) + b * (step b L z).c.val := by
  have hlast := xv_step_last b L z
  have hcs := step_c b L z
  rw [hlast, hcs]
  by_cases ht : tsum b L z < b
  · simp [ht]
  · simp only [ht, if_false]; omega

lemma Gp_inj (z1 z2 : State b L.r) (h1 : Gp z1) (h2 : Gp z2) (heq : step b L z1 = step b L z2) :
    z1 = z2 := by
  have hs := L.hs
  have hsr := L.hsr
  obtain ⟨k, hk⟩ : ∃ k, L.r - L.s = k + 1 := ⟨L.r - L.s - 1, by omega⟩
  have hx : ∀ i, 1 ≤ i → i < L.r → xv z1 i = xv z2 i := by
    intro i hi1 hi2
    have e1 := xv_step_lt b L z1 (i := i - 1) (by omega)
    have e2 := xv_step_lt b L z2 (i := i - 1) (by omega)
    rw [heq, show i - 1 + 1 = i by omega] at e1
    rw [show i - 1 + 1 = i by omega] at e2
    rw [← e1, e2]
  have ht : tsum b L z1 = tsum b L z2 := by
    rw [tsum_eq_step z1, tsum_eq_step z2, heq]
  rw [tsum_eq, tsum_eq, hx (L.r - L.s) (by omega) (by omega)] at ht
  have hA : Asum z1 = Asum z2 := by
    unfold Asum
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hx (L.s + i) (by omega) (by omega)]
  have hB1 := Bsum_decomp z1 k hk
  have hB2 := Bsum_decomp z2 k hk
  have hBs : ∑ i ∈ Finset.range k, xv z1 (1 + i) * b ^ i = ∑ i ∈ Finset.range k, xv z2 (1 + i) * b ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hx (1 + i) (by omega) (by omega)]
  rw [hBs] at hB1
  have hc1 : z1.c.val < 2 := z1.c.isLt
  have hc2 : z2.c.val < 2 := z2.c.isLt
  have hsame : z1.c.val = z2.c.val → z1 = z2 := by
    intro hc
    have hw0 : xv z1 0 = xv z2 0 := by omega
    apply state_eq
    · intro i
      by_cases hi : i.val = 0
      · have := hw0
        rw [xv_of_lt z1 (by omega), xv_of_lt z2 (by omega)] at this
        have e : i = ⟨0, by omega⟩ := Fin.ext hi
        rw [e]; exact this
      · have := hx i.val (by omega) i.isLt
        rw [xv_of_lt z1 i.isLt, xv_of_lt z2 i.isLt] at this
        exact this
    · exact hc
  by_cases hc : z1.c.val = z2.c.val
  · exact hsame hc
  · exfalso
    unfold Gp at h1 h2
    rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;> omega


/-- the digit sequence along the orbit of `w` -/
def Xs (w : State b L.r) (k : ℕ) : ℕ := xv ((step b L)^[k] w) 0

/-- the carry sequence along the orbit of `w` -/
def Cs (w : State b L.r) (k : ℕ) : ℕ := ((step b L)^[k] w).c.val

lemma xv_iter (w : State b L.r) (k i : ℕ) (hi : i < L.r) :
    xv ((step b L)^[k] w) i = Xs w (k + i) := by
  induction i generalizing k with
  | zero => simp [Xs]
  | succ i ih =>
    have h1 := xv_step_lt b L ((step b L)^[k] w) (i := i) hi
    rw [← Function.iterate_succ_apply' (step b L) k w] at h1
    rw [← h1, ih (k + 1) (by omega)]
    congr 1; omega

lemma Xs_lt (w : State b L.r) (k : ℕ) : Xs w k < b := by
  have := L.hs; have := L.hsr
  exact xv_lt _ (by omega)

lemma rec_Xs (w : State b L.r) (k : ℕ) :
    Xs w (k + L.r) + b * Cs w (k + 1) = Xs w (k + (L.r - L.s)) + Xs w k + Cs w k := by
  have hs := L.hs
  have hsr := L.hsr
  set u := (step b L)^[k] w with hu
  have hu' : (step b L)^[k + 1] w = step b L u := Function.iterate_succ_apply' _ _ _
  have hlast := xv_step_last b L u
  have hcs := step_c b L u
  rw [tsum_eq] at hlast hcs
  have e1 : xv (step b L u) (L.r - 1) = Xs w (k + L.r) := by
    rw [← hu', xv_iter w (k + 1) (L.r - 1) (by omega)]
    congr 1; omega
  have e2 : (step b L u).c.val = Cs w (k + 1) := by
    unfold Cs; rw [hu']
  have e3 : xv u (L.r - L.s) = Xs w (k + (L.r - L.s)) := xv_iter w k _ (by omega)
  have e4 : xv u 0 = Xs w k := rfl
  have e5 : u.c.val = Cs w k := rfl
  rw [e1, e3, e4, e5] at hlast
  rw [e2, e3, e4, e5] at hcs
  by_cases ht : Xs w (k + (L.r - L.s)) + Xs w k + Cs w k < b
  · rw [if_pos ht] at hlast hcs
    rw [hcs]
    omega
  · rw [if_neg ht] at hlast hcs
    rw [hcs]
    omega

lemma telescope (b : ℕ) (g : ℕ → ℕ) (m : ℕ) :
    ∑ i ∈ Finset.range m, b ^ i * g i + b ^ m * g m
      = g 0 + ∑ i ∈ Finset.range m, b ^ (i + 1) * g (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => b ^ (i + 1) * g (i + 1)) m]
    linarith [ih]

lemma Gp_iter_r (w : State b L.r) : Gp ((step b L)^[L.r] w) := by
  have hs := L.hs
  have hsr := L.hsr
  set u := (step b L)^[L.r] w with hu
  set m := L.r - L.s with hm
  have hAu : Asum u = ∑ i ∈ Finset.range m, Xs w (L.r + L.s + i) * b ^ i := by
    unfold Asum
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hu, xv_iter w L.r (L.s + i) (by omega), show L.r + (L.s + i) = L.r + L.s + i by omega]
  have hBu : Bsum u = ∑ i ∈ Finset.range m, Xs w (L.r + i) * b ^ i := by
    unfold Bsum
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hu, xv_iter w L.r i (by omega)]
  set O := ∑ i ∈ Finset.range m, Xs w (L.s + i) * b ^ i with hO
  have hOlt : O < b ^ m := sum_digits_lt b _ m (fun i _ => Xs_lt w _)
  have hkey : ∀ i ∈ Finset.range m,
      Xs w (L.r + L.s + i) * b ^ i + b ^ (i + 1) * Cs w (L.s + i + 1)
        = Xs w (L.r + i) * b ^ i + Xs w (L.s + i) * b ^ i + b ^ i * Cs w (L.s + i) := by
    intro i hi
    have := Finset.mem_range.1 hi
    have h := rec_Xs w (L.s + i)
    rw [show L.s + i + L.r = L.r + L.s + i by omega,
      show L.s + i + (L.r - L.s) = L.r + i by omega] at h
    have h2 : (Xs w (L.r + L.s + i) + b * Cs w (L.s + i + 1)) * b ^ i
        = (Xs w (L.r + i) + Xs w (L.s + i) + Cs w (L.s + i)) * b ^ i := by rw [h]
    zify at h2 ⊢
    linear_combination h2
  have hsum := Finset.sum_congr rfl hkey
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have htel := telescope b (fun i => Cs w (L.s + i)) m
  simp only [add_zero] at htel
  have hsm : L.s + m = L.r := by omega
  rw [hsm] at htel
  have hcu : u.c.val = Cs w L.r := rfl
  have hC1 : Cs w L.s < 2 := (((step b L)^[L.s] w).c).isLt
  have hCr : Cs w L.r < 2 := (((step b L)^[L.r] w).c).isLt
  unfold Gp
  rw [hcu]
  have hAB : Asum u + b ^ m * Cs w L.r = Bsum u + O + Cs w L.s := by
    rw [hAu, hBu]
    have e : ∀ i, L.s + (i + 1) = L.s + i + 1 := fun i => by omega
    simp only [e] at htel
    omega
  rcases Nat.lt_or_ge (Cs w L.r) 1 with h | h
  · left
    refine ⟨by omega, ?_⟩
    have : Cs w L.r = 0 := by omega
    rw [this] at hAB
    omega
  · right
    have : Cs w L.r = 1 := by omega
    refine ⟨by omega, ?_⟩
    rw [this] at hAB
    omega

end decomp


section final
variable {b : ℕ} {L : Lags}

lemma Gp_iter (z : State b L.r) (hz : Gp z) : ∀ n, Gp ((step b L)^[n] z) := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih => rw [Function.iterate_succ_apply']; exact Gp_step _ ih

lemma cancel_iter (d : ℕ) : ∀ (i : ℕ) (z : State b L.r), Gp z →
    (step b L)^[i] z = (step b L)^[i] ((step b L)^[d] z) → z = (step b L)^[d] z := by
  intro i
  induction i with
  | zero => intro z _ h; simpa using h
  | succ i ih =>
    intro z hz h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    have hcomm : step b L ((step b L)^[d] z) = (step b L)^[d] (step b L z) := by
      rw [← Function.iterate_succ_apply' (step b L) d z, Function.iterate_succ_apply]
    rw [hcomm] at h
    have := ih (step b L z) (Gp_step z hz) h
    rw [← hcomm] at this
    exact Gp_inj z _ hz (Gp_iter z hz d) this

lemma Gp_mem_periodicPts (z : State b L.r) (hz : Gp z) : z ∈ Function.periodicPts (step b L) := by
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (step b L)^[n] z)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨j - i, by omega, ?_⟩
    have : z = (step b L)^[j - i] z := by
      apply cancel_iter (j - i) i z hz
      rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
      exact hf
    exact this.symm
  · refine ⟨i - j, by omega, ?_⟩
    have : z = (step b L)^[i - j] z := by
      apply cancel_iter (i - j) j z hz
      rw [← Function.iterate_add_apply, show j + (i - j) = i by omega]
      exact hf.symm
    exact this.symm

lemma periodicPts_Gp (z : State b L.r) (hz : z ∈ Function.periodicPts (step b L)) : Gp z := by
  obtain ⟨n, hn, hper⟩ := hz
  have h1 : (step b L)^[n * L.r] z = z := hper.mul_const L.r
  have hr : 0 < L.r := by have := L.hs; have := L.hsr; omega
  have h2 : L.r ≤ n * L.r := Nat.le_mul_of_pos_left _ hn
  have h3 : (step b L)^[L.r] ((step b L)^[n * L.r - L.r] z) = z := by
    rw [← Function.iterate_add_apply, show L.r + (n * L.r - L.r) = n * L.r by omega]
    exact h1
  rw [← h3]
  exact Gp_iter_r _

end final

theorem iterate_r_mem_periodicPts' (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    (step b L)^[L.r] z ∈ Function.periodicPts (step b L) :=
  Gp_mem_periodicPts _ (Gp_iter_r z)

theorem periodic_seed_iff' (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    z ∈ Function.periodicPts (step b L) ↔
      let A : ℕ := ∑ i : Fin (L.r - L.s),
        (z.x ⟨L.s + i.val, by have := i.isLt; omega⟩).val * b ^ i.val
      let B : ℕ := ∑ i : Fin (L.r - L.s),
        (z.x ⟨i.val, by have := i.isLt; have := L.hs; omega⟩).val * b ^ i.val
      (z.c = 0 ∧ B ≤ A) ∨ (z.c = 1 ∧ A ≤ B) := by
  have hA : (∑ i : Fin (L.r - L.s),
        (z.x ⟨L.s + i.val, by have := i.isLt; omega⟩).val * b ^ i.val) = Asum z := by
    unfold Asum
    rw [← Fin.sum_univ_eq_sum_range (fun i => xv z (L.s + i) * b ^ i) (L.r - L.s)]
    apply Finset.sum_congr rfl
    intro i _
    rw [xv_of_lt z (by have := i.isLt; omega)]
  have hB : (∑ i : Fin (L.r - L.s),
        (z.x ⟨i.val, by have := i.isLt; have := L.hs; omega⟩).val * b ^ i.val) = Bsum z := by
    unfold Bsum
    rw [← Fin.sum_univ_eq_sum_range (fun i => xv z i * b ^ i) (L.r - L.s)]
    apply Finset.sum_congr rfl
    intro i _
    rw [xv_of_lt z (by have := i.isLt; have := L.hs; omega)]
  have hc0 : z.c = 0 ↔ z.c.val = 0 := ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
  have hc1 : z.c = 1 ↔ z.c.val = 1 := ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
  dsimp only
  rw [hA, hB, hc0, hc1]
  exact ⟨periodicPts_Gp z, Gp_mem_periodicPts z⟩

end CarryRNG.AWC

theorem solution (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    (CarryRNG.AWC.step b L)^[L.r] z ∈ Function.periodicPts (CarryRNG.AWC.step b L) :=
  CarryRNG.AWC.iterate_r_mem_periodicPts' b L hb z
