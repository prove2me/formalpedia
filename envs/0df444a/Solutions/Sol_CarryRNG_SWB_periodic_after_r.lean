-- Prove2me | solution 1 for CarryRNG.SWB.periodic_after_r
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:32:08.59275+00:00
-- url     : https://prove2.me/submissions/25d9eea6-223d-4ad1-b08a-5318a5fb10e2

import Mathlib
import Definitions.Def_CarryRNG_SWB_step
import Definitions.Def_CarryRNG_SWB_modulus
import Definitions.Def_CarryRNG_SWB_out
import Definitions.Def_CarryRNG_AWC_digit
import Definitions.Def_CarryRNG_SWB_highBlock
import Definitions.Def_CarryRNG_SWB_lowBlock
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed



namespace CarryRNG.SWB
open CarryRNG.AWC

/-- digit as a natural number, zero out of range -/
def dig {b : ℕ} {L : Lags} (z : State b L.r) (i : ℕ) : ℕ :=
  if h : i < L.r then (z.x ⟨i, h⟩).val else 0

theorem dig_lt {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (i : ℕ) : dig z i < b := by
  unfold dig; split_ifs with h
  · exact (z.x ⟨i, h⟩).isLt
  · omega

theorem dig_step_lt {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) {i : ℕ} (hi : i + 1 < L.r) :
    dig (step b L hb z) i = dig z (i+1) := by
  have h1 : i < L.r := by omega
  simp only [dig, h1, hi, dif_pos]
  simp [step, hi]

theorem step_c_val {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) :
    ((step b L hb z).c).val = if dig z (L.r - L.s) < dig z 0 + z.c.val then 1 else 0 := by
  have hs := L.hs; have hsr := L.hsr
  have h1 : L.r - L.s < L.r := by omega
  have h0 : 0 < L.r := by omega
  simp only [dig, h1, h0, dif_pos]
  simp [step]

theorem dig_step_last {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) :
    dig (step b L hb z) (L.r - 1) =
      if dig z (L.r - L.s) < dig z 0 + z.c.val then dig z (L.r - L.s) + b - (dig z 0 + z.c.val)
      else dig z (L.r - L.s) - (dig z 0 + z.c.val) := by
  have hs := L.hs; have hsr := L.hsr
  have h1 : L.r - L.s < L.r := by omega
  have h0 : 0 < L.r := by omega
  have h2 : L.r - 1 < L.r := by omega
  have h3 : ¬ (L.r - 1 + 1 < L.r) := by omega
  simp only [dig, h1, h0, h2, dif_pos]
  simp [step, dif_neg h3]


/-- weights -/
def alpha (b n i : ℕ) : ℕ := if i < n then b ^ i else (b ^ n - 1) * b ^ (i - n)

theorem alpha_pos {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : 0 < alpha b n i := by
  unfold alpha
  split_ifs
  · positivity
  · have : 2 ≤ b ^ n := by
      calc 2 ≤ b := hb
        _ = b ^ 1 := (pow_one b).symm
        _ ≤ b ^ n := Nat.pow_le_pow_right (by omega) hn
    have : 0 < b ^ n - 1 := by omega
    positivity

theorem alpha_succ {b : ℕ} (hb : 2 ≤ b) (n i : ℕ) :
    alpha b n (i + 1) + (if i + 1 = n then 1 else 0) = b * alpha b n i := by
  unfold alpha
  have hp : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by omega)
  by_cases h1 : i + 1 < n
  · have h2 : i < n := by omega
    have h3 : i + 1 ≠ n := by omega
    simp [h1, h2, h3, pow_succ']
  · by_cases h2 : i + 1 = n
    · have h3 : i < n := by omega
      subst h2
      simp [h3, pow_succ']
      have := (pow_succ' b i).symm; omega
    · have h3 : ¬ i < n := by omega
      have h4 : i + 1 - n = (i - n) + 1 := by omega
      simp [h1, h3, h2, h4, pow_succ']
      ring

theorem geom_nat (b : ℕ) (hb : 1 ≤ b) (n : ℕ) :
    (b - 1) * (∑ i ∈ Finset.range n, b ^ i) + 1 = b ^ n := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [pow_succ]
    nlinarith [ih]

theorem alpha_sum {b : ℕ} (hb : 2 ≤ b) (n s : ℕ) :
    (b - 1) * (∑ i ∈ Finset.range (n + s), alpha b n i) + b ^ s = b ^ (n + s) := by
  rw [Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range n, alpha b n i = ∑ i ∈ Finset.range n, b ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [alpha, Finset.mem_range.mp hi]
  have h2 : ∑ x ∈ Finset.range s, alpha b n (n + x) = (b ^ n - 1) * ∑ x ∈ Finset.range s, b ^ x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [alpha]
  rw [h1, h2]
  have g1 := geom_nat b (by omega) n
  have g2 := geom_nat b (by omega) s
  have hp : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by omega)
  obtain ⟨P, hP⟩ : ∃ P, b ^ n = P + 1 := ⟨b ^ n - 1, by omega⟩
  rw [hP] at g1 ⊢
  rw [pow_add, hP]
  simp only [Nat.add_sub_cancel]
  generalize (∑ i ∈ Finset.range n, b ^ i) = G1 at *
  generalize (∑ i ∈ Finset.range s, b ^ i) = G2 at *
  generalize b ^ s = Q at *
  nlinarith [g1, g2]


/-- the potential -/
def phi {b : ℕ} {L : Lags} (z : State b L.r) : ℕ :=
  ∑ i ∈ Finset.range L.r, dig z i * alpha b (L.r - L.s) i + z.c.val

theorem sum_r_succ' (L : Lags) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range L.r, f i = ∑ i ∈ Finset.range (L.r - 1), f (i + 1) + f 0 := by
  have := L.hsr; have := L.hs
  have h := Finset.sum_range_succ' f (L.r - 1)
  rwa [Nat.sub_add_cancel (by omega)] at h

theorem sum_r_succ (L : Lags) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range L.r, f i = ∑ i ∈ Finset.range (L.r - 1), f i + f (L.r - 1) := by
  have := L.hsr; have := L.hs
  have h := Finset.sum_range_succ f (L.r - 1)
  rwa [Nat.sub_add_cancel (by omega)] at h

theorem modulus_eq {b : ℕ} (hb : 2 ≤ b) (L : Lags) :
    modulus b L = b * ((b ^ (L.r - L.s) - 1) * b ^ (L.s - 1)) + 1 := by
  have hs := L.hs; have hsr := L.hsr
  unfold modulus
  have hp : 1 ≤ b ^ (L.r - L.s) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨P, hP⟩ : ∃ P, b ^ (L.r - L.s) = P + 1 := ⟨_, (Nat.sub_add_cancel hp).symm⟩
  have e1 : b ^ L.r = b ^ (L.r - L.s) * (b * b ^ (L.s - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have e2 : b ^ L.s = b * b ^ (L.s - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hP] at e1 ⊢
  rw [e2]
  simp only [Nat.add_sub_cancel]
  have : b ^ L.r = b * b ^ (L.s - 1) + b * (P * b ^ (L.s - 1)) := by rw [e1]; ring
  omega

theorem phi_step {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) :
    b * phi (step b L hb z) = phi z + modulus b L * dig (step b L hb z) (L.r - 1) := by
  have hs := L.hs; have hsr := L.hsr
  set n := L.r - L.s with hn
  have hn1 : 1 ≤ n := by omega
  set S := ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * alpha b n i with hS
  set A := (b ^ n - 1) * b ^ (L.s - 1) with hA
  have hα0 : alpha b n 0 = 1 := by simp [alpha]; omega
  have hαl : alpha b n (L.r - 1) = A := by
    have : ¬ (L.r - 1 < n) := by omega
    have h2 : L.r - 1 - n = L.s - 1 := by omega
    simp [alpha, this, h2, hA]
  -- H1
  have H1 : phi z + dig z n = dig z 0 + b * S + z.c.val := by
    unfold phi
    rw [← hn, sum_r_succ', hα0]
    have key : ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * (alpha b n (i + 1) + (if i + 1 = n then 1 else 0))
        = b * S := by
      rw [hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [alpha_succ hb n i]; ring
    simp only [mul_add, Finset.sum_add_distrib] at key
    have key2 : ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * (if i + 1 = n then 1 else 0) = dig z n := by
      rw [Finset.sum_eq_single_of_mem (n - 1)]
      · have : n - 1 + 1 = n := by omega
        simp [this]
      · rw [Finset.mem_range]; omega
      · intro i _ hi
        have : i + 1 ≠ n := by omega
        simp [this]
    rw [key2] at key
    omega
  -- H2
  have H2 : phi (step b L hb z) = S + dig (step b L hb z) (L.r - 1) * A + (step b L hb z).c.val := by
    unfold phi
    rw [← hn, sum_r_succ, hαl]
    congr 2
    rw [hS]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dig_step_lt hb z (by have := Finset.mem_range.mp hi; omega)]
  have hE : dig (step b L hb z) (L.r - 1) + dig z 0 + z.c.val
      = dig z n + b * (step b L hb z).c.val := by
    have hc := z.c.isLt
    have h1 := dig_lt hb z n
    have h2 := dig_lt hb z 0
    rw [dig_step_last hb z, step_c_val hb z, ← hn]
    split_ifs with h <;> omega
  have hm := modulus_eq hb L
  rw [← hn, ← hA] at hm
  rw [hm, H2]
  have : b * (S + dig (step b L hb z) (L.r - 1) * A + (step b L hb z).c.val) + dig z n =
      (phi z + dig z n) + (b * A + 1) * dig (step b L hb z) (L.r - 1) := by
    rw [H1]; nlinarith [hE]
  omega


theorem state_ext {b : ℕ} {L : Lags} (z w : State b L.r) (hx : ∀ i, i < L.r → dig z i = dig w i)
    (hc : z.c.val = w.c.val) : z = w := by
  obtain ⟨zx, zc⟩ := z
  obtain ⟨wx, wc⟩ := w
  have hc' : zc = wc := Fin.ext hc
  subst hc'
  have : zx = wx := by
    funext i
    have := hx i.val i.isLt
    simp only [dig, i.isLt, dif_pos] at this
    exact Fin.ext this
  subst this
  rfl

theorem dig_top {b : ℕ} {L : Lags} (hb : 2 ≤ b) {i : ℕ} (hi : i < L.r) :
    dig (topSeed b L.r hb) i = b - 1 := by
  simp [dig, topSeed, hi]

theorem dig_zero {b : ℕ} {L : Lags} (hb : 2 ≤ b) (i : ℕ) :
    dig (zeroSeed b L.r hb) i = 0 := by
  simp [dig, zeroSeed]

theorem eq_top_of_dig {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r)
    (hx : ∀ i, i < L.r → dig z i = b - 1) (hc : z.c.val = 1) : z = topSeed b L.r hb :=
  state_ext z _ (fun i hi => by rw [hx i hi, dig_top hb hi]) (by simpa [topSeed] using hc)

theorem eq_zero_of_dig {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r)
    (hx : ∀ i, i < L.r → dig z i = 0) (hc : z.c.val = 0) : z = zeroSeed b L.r hb :=
  state_ext z _ (fun i hi => by rw [hx i hi, dig_zero hb]) (by simpa [zeroSeed] using hc)

theorem step_top {b : ℕ} {L : Lags} (hb : 2 ≤ b) :
    step b L hb (topSeed b L.r hb) = topSeed b L.r hb := by
  have hs := L.hs; have hsr := L.hsr
  apply state_ext
  · intro i hi
    by_cases h : i + 1 < L.r
    · rw [dig_step_lt hb _ h, dig_top hb h, dig_top hb hi]
    · have : i = L.r - 1 := by omega
      subst this
      rw [dig_step_last hb, dig_top hb (by omega : L.r - L.s < L.r), dig_top hb (by omega : 0 < L.r),
        dig_top hb hi]
      simp [topSeed]
      omega
  · rw [step_c_val hb, dig_top hb (by omega : L.r - L.s < L.r), dig_top hb (by omega : 0 < L.r)]
    simp [topSeed]

theorem step_zero {b : ℕ} {L : Lags} (hb : 2 ≤ b) :
    step b L hb (zeroSeed b L.r hb) = zeroSeed b L.r hb := by
  have hs := L.hs; have hsr := L.hsr
  apply state_ext
  · intro i hi
    by_cases h : i + 1 < L.r
    · rw [dig_step_lt hb _ h, dig_zero hb, dig_zero hb]
    · have : i = L.r - 1 := by omega
      subst this
      rw [dig_step_last hb, dig_zero hb, dig_zero hb, dig_zero hb]
      simp [zeroSeed]
  · rw [step_c_val hb, dig_zero hb, dig_zero hb]
    simp [zeroSeed]

theorem sum_alpha {b : ℕ} (hb : 2 ≤ b) (L : Lags) :
    (b - 1) * (∑ i ∈ Finset.range L.r, alpha b (L.r - L.s) i) + b ^ L.s = b ^ L.r := by
  have h := alpha_sum hb (L.r - L.s) L.s
  rwa [Nat.sub_add_cancel L.hsr.le] at h

theorem sum_dig_le {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) :
    ∑ i ∈ Finset.range L.r, dig z i * alpha b (L.r - L.s) i ≤
      (b - 1) * ∑ i ∈ Finset.range L.r, alpha b (L.r - L.s) i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have := dig_lt hb z i
  exact Nat.mul_le_mul_right _ (by omega)

theorem phi_top {b : ℕ} {L : Lags} (hb : 2 ≤ b) : phi (topSeed b L.r hb) = modulus b L := by
  have hs := L.hs; have hsr := L.hsr
  have h := sum_alpha hb L
  have hle : b ^ L.s ≤ b ^ L.r := Nat.pow_le_pow_right (by omega) hsr.le
  have : ∑ i ∈ Finset.range L.r, dig (topSeed b L.r hb) i * alpha b (L.r - L.s) i =
      (b - 1) * ∑ i ∈ Finset.range L.r, alpha b (L.r - L.s) i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dig_top hb (Finset.mem_range.mp hi)]
  unfold phi modulus
  rw [this]
  simp [topSeed]
  omega

theorem eq_top_of_phi_ge {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r)
    (h : modulus b L ≤ phi z) : z = topSeed b L.r hb := by
  have hs := L.hs; have hsr := L.hsr
  have h1 := sum_alpha hb L
  have hle : b ^ L.s ≤ b ^ L.r := Nat.pow_le_pow_right (by omega) hsr.le
  have h2 := sum_dig_le hb z
  have hc := z.c.isLt
  unfold phi modulus at h
  have h3 : ∑ i ∈ Finset.range L.r, dig z i * alpha b (L.r - L.s) i =
      (b - 1) * ∑ i ∈ Finset.range L.r, alpha b (L.r - L.s) i := by omega
  have h4 : z.c.val = 1 := by omega
  have h5 := (Finset.sum_eq_sum_iff_of_le (s := Finset.range L.r)
    (f := fun i => dig z i * alpha b (L.r - L.s) i) (g := fun i => (b - 1) * alpha b (L.r - L.s) i)
    (fun i _ => by
      have := dig_lt hb z i
      exact Nat.mul_le_mul_right _ (by omega))).mp (by rw [← Finset.mul_sum]; exact h3)
  apply eq_top_of_dig hb z _ h4
  intro i hi
  have := h5 i (Finset.mem_range.mpr hi)
  have hpos := alpha_pos hb (n := L.r - L.s) (by omega) i
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem phi_lt_of_ne_top {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r)
    (h : z ≠ topSeed b L.r hb) : phi z < modulus b L := by
  by_contra h'
  exact h (eq_top_of_phi_ge hb z (not_lt.mp h'))

theorem phi_eq_zero_iff {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) :
    phi z = 0 ↔ z = zeroSeed b L.r hb := by
  have hs := L.hs; have hsr := L.hsr
  constructor
  · intro h
    unfold phi at h
    have h1 := Nat.add_eq_zero_iff.mp h
    apply eq_zero_of_dig hb z _ (by simpa using h1.2)
    intro i hi
    have := (Finset.sum_eq_zero_iff.mp h1.1) i (Finset.mem_range.mpr hi)
    have hpos := alpha_pos hb (n := L.r - L.s) (by omega) i
    rcases Nat.mul_eq_zero.mp this with h | h
    · exact h
    · omega
  · rintro rfl
    unfold phi
    simp only [dig_zero hb, zero_mul, Finset.sum_const_zero, zero_add]
    simp [zeroSeed]


theorem modulus_pos {b : ℕ} (hb : 2 ≤ b) (L : Lags) : 0 < modulus b L := by
  unfold modulus; omega

theorem phi_step_lt {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (h : phi z < modulus b L) :
    phi (step b L hb z) < modulus b L := by
  have h1 := phi_step hb z
  have h2 := dig_lt hb (step b L hb z) (L.r - 1)
  have hm := modulus_pos hb L
  by_contra hc
  push_neg at hc
  have : b * modulus b L ≤ b * phi (step b L hb z) := Nat.mul_le_mul_left _ hc
  have : modulus b L * dig (step b L hb z) (L.r - 1) ≤ modulus b L * (b - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  nlinarith

theorem phi_iter_lt {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (hz : z ≠ topSeed b L.r hb)
    (t : ℕ) : phi ((step b L hb)^[t] z) < modulus b L := by
  induction t with
  | zero => simpa using phi_lt_of_ne_top hb z hz
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact phi_step_lt hb _ ih

theorem phi_iter_mod {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (hz : z ≠ topSeed b L.r hb)
    (u d : ℕ) :
    b ^ d * phi ((step b L hb)^[u + d] z) % modulus b L = phi ((step b L hb)^[u] z) := by
  induction d with
  | zero => simpa using Nat.mod_eq_of_lt (phi_iter_lt hb z hz u)
  | succ d ih =>
    have h1 := phi_step hb ((step b L hb)^[u + d] z)
    rw [← Function.iterate_succ_apply' (step b L hb) (u + d) z] at h1
    have : b ^ (d + 1) * phi ((step b L hb)^[u + (d + 1)] z) =
        b ^ d * phi ((step b L hb)^[u + d] z) + modulus b L *
          (b ^ d * dig ((step b L hb)^[u + d + 1] z) (L.r - 1)) := by
      rw [← add_assoc, pow_succ]
      have : b ^ d * b * phi ((step b L hb)^[u + d + 1] z) =
          b ^ d * (b * phi ((step b L hb)^[u + d + 1] z)) := by ring
      rw [this, h1]; ring
    rw [this, Nat.add_mul_mod_self_left]
    exact ih

theorem phi_iter_dig {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (hz : z ≠ topSeed b L.r hb)
    (t : ℕ) :
    dig ((step b L hb)^[t + 1] z) (L.r - 1) =
      b * phi ((step b L hb)^[t + 1] z) / modulus b L := by
  have h1 : b * phi ((step b L hb)^[t + 1] z) = phi ((step b L hb)^[t] z) +
      modulus b L * dig ((step b L hb)^[t + 1] z) (L.r - 1) := by
    have := phi_step hb ((step b L hb)^[t] z)
    rwa [← Function.iterate_succ_apply' (step b L hb) t z] at this
  have h2 := phi_iter_lt hb z hz t
  have hm := modulus_pos hb L
  rw [h1, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt h2, zero_add]

theorem phi_iter_zero_iff {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (t : ℕ) :
    phi ((step b L hb)^[t] z) = 0 ↔ z = zeroSeed b L.r hb := by
  constructor
  · intro h
    rw [← phi_eq_zero_iff hb]
    induction t with
    | zero => simpa using h
    | succ t ih =>
      apply ih
      have h1 : b * phi ((step b L hb)^[t + 1] z) = phi ((step b L hb)^[t] z) +
          modulus b L * dig ((step b L hb)^[t + 1] z) (L.r - 1) := by
        have := phi_step hb ((step b L hb)^[t] z)
        rwa [← Function.iterate_succ_apply' (step b L hb) t z] at this
      rw [h, mul_zero] at h1
      exact (Nat.add_eq_zero_iff.mp h1.symm).1
  · rintro rfl
    rw [Function.iterate_fixed (step_zero hb)]
    exact (phi_eq_zero_iff hb _).mpr rfl

theorem output_eq_reversed_digits_core (b : ℕ) (L : Lags) (hb : 2 ≤ b)
    (z : State b L.r) (hz : z ≠ topSeed b L.r hb) (C : ℕ) (hC : L.r + 1 ≤ C) :
    ∃ k : ℕ, k < modulus b L ∧ (0 < k ↔ z ≠ zeroSeed b L.r hb) ∧
      ∀ n : ℕ, L.r + 1 ≤ n → n ≤ C →
        out b L hb z n = digit b (modulus b L) k (C + 1 - n) := by
  have hs := L.hs; have hsr := L.hsr
  refine ⟨phi ((step b L hb)^[C - L.r] z), phi_iter_lt hb z hz _, ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, phi_iter_zero_iff hb]
  · intro n hn1 hn2
    have hn : ¬ (1 ≤ n ∧ n ≤ L.r) := by omega
    obtain ⟨t, ht⟩ : ∃ t, n - L.r = t + 1 := ⟨n - L.r - 1, by omega⟩
    have e1 : out b L hb z n = dig ((step b L hb)^[t + 1] z) (L.r - 1) := by
      unfold out
      rw [dif_neg hn, ht]
      simp [dig, show L.r - 1 < L.r by omega]
    rw [e1, phi_iter_dig hb z hz]
    unfold digit
    have e2 := phi_iter_mod hb z hz (n - L.r) (C - n)
    have e3 : n - L.r + (C - n) = C - L.r := by omega
    rw [e3, ht] at e2
    have e4 : C + 1 - n - 1 = C - n := by omega
    rw [e4, e2]


theorem periodic_of_inj {α : Type*} [Finite α] (f : α → α) (P : α → Prop)
    (hP : ∀ x, P x → P (f x)) (hinj : ∀ x y, P x → P y → f x = f y → x = y) :
    ∀ x, P x → x ∈ Function.periodicPts f := by
  intro x hx
  have key : ∀ n a b, P a → P b → f^[n] a = f^[n] b → a = b := by
    intro n
    induction n with
    | zero => intro a b _ _ h; simpa using h
    | succ n ih =>
      intro a b ha hb h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      exact hinj a b ha hb (ih _ _ (hP a ha) (hP b hb) h)
  have hit : ∀ n a, P a → P (f^[n] a) := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; rw [Function.iterate_succ_apply]; exact ih _ (hP a ha)
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] x)
  have main : ∀ i j : ℕ, i < j → f^[i] x = f^[j] x → x ∈ Function.periodicPts f := by
    intro i j hlt h
    have h2 : f^[i] x = f^[i] (f^[j - i] x) := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt.le]; exact h
    have h3 := key i x _ hx (hit _ x hx) h2
    exact ⟨j - i, by omega, h3.symm⟩
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact main i j h1 h
  · exact main j i h1 h.symm

/-- the integer formed by the digits -/
def Dval {b : ℕ} {L : Lags} (z : State b L.r) : ℕ :=
  ∑ i ∈ Finset.range L.r, dig z i * b ^ i

theorem Dval_step {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) :
    b * Dval (step b L hb z) + dig z 0 = Dval z + b ^ L.r * dig (step b L hb z) (L.r - 1) := by
  have hs := L.hs; have hsr := L.hsr
  unfold Dval
  rw [sum_r_succ (f := fun i => dig (step b L hb z) i * b ^ i), sum_r_succ' (f := fun i => dig z i * b ^ i)]
  have h1 : ∑ i ∈ Finset.range (L.r - 1), dig (step b L hb z) i * b ^ i =
      ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [dig_step_lt hb z (by have := Finset.mem_range.mp hi; omega)]
  rw [h1]
  have h2 : b * ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ i =
      ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ (i + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]; ring
  have h3 : b ^ L.r = b * b ^ (L.r - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [mul_add, h2, h3]
  simp
  ring

/-- the periodicity condition -/
def Cond {b : ℕ} {L : Lags} (z : State b L.r) : Prop :=
  phi z < modulus b L ∧ modulus b L * Dval z ≤ b ^ L.r * phi z ∧
    b ^ L.r * phi z < modulus b L * (Dval z + 1)

theorem cond_step {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (h : Cond z) :
    Cond (step b L hb z) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨phi_step_lt hb z h0, ?_⟩
  have E1 := phi_step hb z
  have E2 := Dval_step hb z
  have hu := dig_lt hb z 0
  have hbpos : 0 < b := by omega
  set m := modulus b L with hm
  set e := dig (step b L hb z) (L.r - 1) with he
  set D' := Dval (step b L hb z)
  set Φ' := phi (step b L hb z)
  set u0 := dig z 0
  have F1 : m * (b * D' + u0) = m * (Dval z + b ^ L.r * e) := by rw [E2]
  have F2 : b ^ L.r * (b * Φ') = b ^ L.r * (phi z + m * e) := by rw [E1]
  have F3 : m * (u0 + 1) ≤ m * b := Nat.mul_le_mul_left _ (by omega)
  constructor
  · apply Nat.le_of_mul_le_mul_left _ hbpos
    nlinarith
  · apply Nat.lt_of_mul_lt_mul_left (a := b)
    nlinarith


/-- eventual set -/
def PSet {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) : Prop :=
  Cond z ∨ z = topSeed b L.r hb

theorem PSet_step {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (h : PSet hb z) :
    PSet hb (step b L hb z) := by
  rcases h with h | h
  · exact Or.inl (cond_step hb z h)
  · exact Or.inr (by rw [h, step_top])

theorem cond_inj {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z1 z2 : State b L.r) (c1 : Cond z1) (c2 : Cond z2)
    (h : step b L hb z1 = step b L hb z2) : z1 = z2 := by
  have hs := L.hs; have hsr := L.hsr
  have E1a := phi_step hb z1
  have E1b := phi_step hb z2
  have E2a := Dval_step hb z1
  have E2b := Dval_step hb z2
  have hphi : phi z1 = phi z2 := by
    have hp' : phi (step b L hb z1) = phi (step b L hb z2) := by rw [h]
    have he : dig (step b L hb z1) (L.r - 1) = dig (step b L hb z2) (L.r - 1) := by rw [h]
    have : phi z1 + modulus b L * dig (step b L hb z1) (L.r - 1) =
        phi z2 + modulus b L * dig (step b L hb z1) (L.r - 1) := by
      rw [← E1a, hp', E1b, he]
    exact Nat.add_right_cancel this
  have hm := modulus_pos hb L
  have hD : Dval z1 = Dval z2 := by
    obtain ⟨_, a1, a2⟩ := c1
    obtain ⟨_, b1, b2⟩ := c2
    rw [hphi] at a1 a2
    have x1 : Dval z1 < Dval z2 + 1 := Nat.lt_of_mul_lt_mul_left (a := modulus b L) (by omega)
    have x2 : Dval z2 < Dval z1 + 1 := Nat.lt_of_mul_lt_mul_left (a := modulus b L) (by omega)
    omega
  have hd0 : dig z1 0 = dig z2 0 := by
    have hDs : Dval (step b L hb z1) = Dval (step b L hb z2) := by rw [h]
    have he : dig (step b L hb z1) (L.r - 1) = dig (step b L hb z2) (L.r - 1) := by rw [h]
    have : b * Dval (step b L hb z1) + dig z1 0 = b * Dval (step b L hb z1) + dig z2 0 := by
      calc b * Dval (step b L hb z1) + dig z1 0
          = Dval z1 + b ^ L.r * dig (step b L hb z1) (L.r - 1) := E2a
        _ = Dval z2 + b ^ L.r * dig (step b L hb z2) (L.r - 1) := by rw [hD, he]
        _ = b * Dval (step b L hb z2) + dig z2 0 := E2b.symm
        _ = b * Dval (step b L hb z1) + dig z2 0 := by rw [hDs]
    exact Nat.add_left_cancel this
  have hdi : ∀ i, i < L.r → dig z1 i = dig z2 i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; exact hd0
    · have e1 := dig_step_lt hb z1 (i := i - 1) (by omega)
      have e2 := dig_step_lt hb z2 (i := i - 1) (by omega)
      rw [Nat.sub_add_cancel h0] at e1 e2
      rw [← e1, ← e2, h]
  apply state_ext z1 z2 hdi
  have : phi z1 = phi z2 := hphi
  unfold phi at this
  have hsum : ∑ i ∈ Finset.range L.r, dig z1 i * alpha b (L.r - L.s) i =
      ∑ i ∈ Finset.range L.r, dig z2 i * alpha b (L.r - L.s) i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdi i (Finset.mem_range.mp hi)]
  rw [hsum] at this
  exact Nat.add_left_cancel this

theorem PSet_inj {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z1 z2 : State b L.r) (h1 : PSet hb z1)
    (h2 : PSet hb z2) (h : step b L hb z1 = step b L hb z2) : z1 = z2 := by
  rcases h1 with c1 | t1
  · rcases h2 with c2 | t2
    · exact cond_inj hb z1 z2 c1 c2 h
    · exfalso
      subst t2
      rw [step_top] at h
      have := phi_step_lt hb z1 c1.1
      rw [h, phi_top] at this
      exact lt_irrefl _ this
  · rcases h2 with c2 | t2
    · exfalso
      subst t1
      rw [step_top] at h
      have := phi_step_lt hb z2 c2.1
      rw [← h, phi_top] at this
      exact lt_irrefl _ this
    · rw [t1, t2]

theorem PSet_periodic {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (h : PSet hb z) :
    z ∈ Function.periodicPts (step b L hb) :=
  periodic_of_inj (step b L hb) (PSet hb) (PSet_step hb) (PSet_inj hb) z h

theorem dig_iter_shift {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (t j : ℕ) :
    ∀ i, i + j < L.r → dig ((step b L hb)^[t + j] z) i = dig ((step b L hb)^[t] z) (i + j) := by
  induction j with
  | zero => intro i _; simp
  | succ j ih =>
    intro i hi
    rw [← add_assoc, Function.iterate_succ_apply', dig_step_lt hb _ (by omega), ih (i + 1) (by omega)]
    congr 1; omega

theorem phi_iter_eq {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (t : ℕ) :
    b ^ t * phi ((step b L hb)^[t] z) = phi z +
      modulus b L * ∑ i ∈ Finset.range t, dig ((step b L hb)^[i + 1] z) (L.r - 1) * b ^ i := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : b * phi ((step b L hb)^[t + 1] z) = phi ((step b L hb)^[t] z) +
        modulus b L * dig ((step b L hb)^[t + 1] z) (L.r - 1) := by
      have := phi_step hb ((step b L hb)^[t] z)
      rwa [← Function.iterate_succ_apply' (step b L hb) t z] at this
    have : b ^ (t + 1) * phi ((step b L hb)^[t + 1] z) = b ^ t * phi ((step b L hb)^[t] z) +
        modulus b L * (dig ((step b L hb)^[t + 1] z) (L.r - 1) * b ^ t) := by
      calc b ^ (t + 1) * phi ((step b L hb)^[t + 1] z)
          = b ^ t * (b * phi ((step b L hb)^[t + 1] z)) := by ring
        _ = b ^ t * (phi ((step b L hb)^[t] z) +
              modulus b L * dig ((step b L hb)^[t + 1] z) (L.r - 1)) := by rw [h1]
        _ = _ := by ring
    rw [this, ih, Finset.sum_range_succ]
    ring

theorem cond_iter {b : ℕ} {L : Lags} (hb : 2 ≤ b) (z : State b L.r) (hz : z ≠ topSeed b L.r hb) :
    Cond ((step b L hb)^[L.r] z) := by
  have hs := L.hs; have hsr := L.hsr
  have h1 := phi_iter_eq hb z L.r
  have hD : Dval ((step b L hb)^[L.r] z) =
      ∑ i ∈ Finset.range L.r, dig ((step b L hb)^[i + 1] z) (L.r - 1) * b ^ i := by
    unfold Dval
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have := dig_iter_shift hb z (i + 1) (L.r - 1 - i) i (by omega)
    rw [show i + 1 + (L.r - 1 - i) = L.r by omega, show i + (L.r - 1 - i) = L.r - 1 by omega] at this
    rw [this]
  rw [← hD] at h1
  have h2 := phi_iter_lt hb z hz L.r
  have h3 := phi_lt_of_ne_top hb z hz
  refine ⟨h2, ?_, ?_⟩
  · rw [h1]; exact Nat.le_add_left _ _
  · rw [h1]; nlinarith

theorem periodic_after_r_core (b : ℕ) (L : Lags) (hb : 2 ≤ b) (z : State b L.r) :
    (step b L hb)^[L.r] z ∈ Function.periodicPts (step b L hb) := by
  by_cases hz : z = topSeed b L.r hb
  · apply PSet_periodic hb
    right
    rw [hz, Function.iterate_fixed (step_top hb)]
  · exact PSet_periodic hb _ (Or.inl (cond_iter hb z hz))

end CarryRNG.SWB

open CarryRNG.SWB


theorem solution (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    (step b L hb)^[L.r] z ∈ Function.periodicPts (step b L hb) := by
  exact periodic_after_r_core b L hb z
