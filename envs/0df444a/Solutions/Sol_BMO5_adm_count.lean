-- Prove2me | solution 1 for BMO5.adm_count
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T17:40:12.827833+00:00
-- url     : https://prove2.me/submissions/231f716c-3c51-4600-b03f-b66b50ca60c1

import Mathlib
import Definitions.Def_BMO5Adm

set_option maxHeartbeats 1000000

namespace BMO5C

theorem four_pow : ∀ m : ℕ, (3:ℤ) ^ (m + 1) ∣ 4 ^ (3 ^ m) - 1
  | 0 => by norm_num
  | m + 1 => by
    have ih := four_pow m
    have h3 : (3:ℤ) ∣ 4 ^ (3 ^ m) - 1 := dvd_trans (dvd_pow_self 3 (Nat.succ_ne_zero m)) ih
    have e : (4:ℤ) ^ (3 ^ (m + 1)) - 1 =
        (4 ^ (3 ^ m) - 1) * ((4 ^ (3 ^ m) - 1) ^ 2 + 3 * 4 ^ (3 ^ m)) := by
      rw [pow_succ 3 m, pow_mul]; ring
    rw [e, pow_succ (3:ℤ) (m + 1)]
    exact mul_dvd_mul ih (dvd_add (dvd_pow h3 two_ne_zero) (dvd_mul_right 3 _))

theorem pw_shift (k t x : ℕ) : (2:ℤ) ^ (x + 2 * 3 ^ k * t) ≡ 2 ^ x [ZMOD 3 ^ (k + 1)] := by
  have h4 : (4:ℤ) ^ (3 ^ k) ≡ 1 [ZMOD 3 ^ (k + 1)] := (Int.modEq_iff_dvd.mpr (four_pow k)).symm
  have e : (2:ℤ) ^ (x + 2 * 3 ^ k * t) = 2 ^ x * ((4:ℤ) ^ 3 ^ k) ^ t := by
    rw [← pow_mul, show (4:ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [e]
  calc (2:ℤ) ^ x * ((4:ℤ) ^ 3 ^ k) ^ t ≡ 2 ^ x * 1 ^ t [ZMOD 3 ^ (k + 1)] := (h4.pow t).mul_left _
    _ = 2 ^ x := by ring

def NN (i : ℕ) : ℤ := 20 * 2 ^ i + (i : ℤ) + 1

theorem hpow (k t i e : ℕ) (he : e < i) :
    (2:ℤ) ^ (i + 2 * 3 ^ k * t - e - 1) ≡ 2 ^ (i - e - 1) [ZMOD 3 ^ (k + 1)] := by
  have h : i + 2 * 3 ^ k * t - e - 1 = (i - e - 1) + 2 * 3 ^ k * t := by
    generalize 2 * 3 ^ k * t = K
    omega
  rw [h]
  exact pw_shift k t _

theorem hN (k t i : ℕ) : NN (i + 2 * 3 ^ k * t) - NN i ≡ 2 * 3 ^ k * (t : ℤ) [ZMOD 3 ^ (k + 1)] := by
  have h0 := (pw_shift k t i).mul_left 20
  have e : NN (i + 2 * 3 ^ k * t) - NN i =
      ((20:ℤ) * 2 ^ (i + 2 * 3 ^ k * t) - 20 * 2 ^ i) + 2 * 3 ^ k * (t : ℤ) := by
    unfold NN; push_cast; ring
  rw [e]
  have hz : (20:ℤ) * 2 ^ (i + 2 * 3 ^ k * t) - 20 * 2 ^ i ≡ 0 [ZMOD 3 ^ (k + 1)] := by
    have := h0.sub_right (20 * 2 ^ i)
    rwa [sub_self] at this
  have := hz.add_right (2 * 3 ^ k * (t : ℤ))
  rwa [zero_add] at this

/-- block-word version of `BMO5Adm.okb` (false = T block, true = ST block) -/
def okw (i : ℕ) : List Bool → ℤ → ℕ → ℕ → Prop
  | [], _, _, _ => True
  | false :: w, F, m, d => (3:ℤ) ^ (m + 1) ∣ F ∧ okw i w F (m + 1) d
  | true :: w, F, m, d => (3:ℤ) ^ (m + 1) ∣ F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3) ∧
      okw i w (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) (m + 1) (d + 1)

def fin (i : ℕ) : List Bool → ℤ → ℕ → ℕ → ℤ × ℕ × ℕ
  | [], F, m, d => (F, m, d)
  | false :: w, F, m, d => fin i w F (m + 1) d
  | true :: w, F, m, d => fin i w (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) (m + 1) (d + 1)

def lastc (i : ℕ) (x : Bool) (s : ℤ × ℕ × ℕ) : Prop :=
  if x then (3:ℤ) ^ (s.2.1 + 1) ∣ s.1 + 3 ^ s.2.1 * (20 * 2 ^ (i - s.2.2 - 1) - 3)
  else (3:ℤ) ^ (s.2.1 + 1) ∣ s.1

theorem okw_append (i : ℕ) (x : Bool) : ∀ (w : List Bool) (F : ℤ) (m d : ℕ),
    okw i (w ++ [x]) F m d ↔ okw i w F m d ∧ lastc i x (fin i w F m d)
  | [], F, m, d => by cases x <;> simp [okw, fin, lastc]
  | false :: w, F, m, d => by
    simp only [List.cons_append, okw, fin, okw_append i x w, and_assoc]
  | true :: w, F, m, d => by
    simp only [List.cons_append, okw, fin, okw_append i x w, and_assoc]

theorem fin_m (i : ℕ) : ∀ (w : List Bool) (F : ℤ) (m d : ℕ), (fin i w F m d).2.1 = m + w.length
  | [], F, m, d => by simp [fin]
  | false :: w, F, m, d => by
    have := fin_m i w F (m + 1) d
    simp only [fin, List.length_cons] at this ⊢; omega
  | true :: w, F, m, d => by
    have := fin_m i w (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) (m + 1) (d + 1)
    simp only [fin, List.length_cons] at this ⊢; omega

theorem fin_d (i i' : ℕ) : ∀ (w : List Bool) (F F' : ℤ) (m d : ℕ),
    (fin i w F m d).2.2 = (fin i' w F' m d).2.2 ∧ (fin i w F m d).2.2 ≤ d + w.length
  | [], F, F', m, d => by simp [fin]
  | false :: w, F, F', m, d => by
    obtain ⟨h1, h2⟩ := fin_d i i' w F F' (m + 1) d
    simp only [fin, List.length_cons]
    exact ⟨h1, by omega⟩
  | true :: w, F, F', m, d => by
    obtain ⟨h1, h2⟩ := fin_d i i' w (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3))
      (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)) (m + 1) (d + 1)
    simp only [fin, List.length_cons]
    exact ⟨h1, by omega⟩

theorem fin_diff (i i' K : ℕ) : ∀ (w : List Bool) (F F' : ℤ) (m d : ℕ),
    (∀ e, d ≤ e → e < d + w.length → (2:ℤ) ^ (i' - e - 1) ≡ 2 ^ (i - e - 1) [ZMOD 3 ^ K]) →
    (fin i' w F' m d).1 - (fin i w F m d).1 ≡ F' - F [ZMOD 3 ^ K]
  | [], F, F', m, d, _ => Int.ModEq.refl _
  | false :: w, F, F', m, d, h =>
    fin_diff i i' K w F F' (m + 1) d
      (fun e h1 h2 => h e h1 (by simp only [List.length_cons]; omega))
  | true :: w, F, F', m, d, h => by
    have hd := h d le_rfl (by simp only [List.length_cons]; omega)
    have hT : (3:ℤ) ^ m * (20 * 2 ^ (i' - d - 1) - 3) - 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)
        ≡ 0 [ZMOD 3 ^ K] := by
      have := (((hd.mul_left 20).sub_right 3).mul_left ((3:ℤ) ^ m)).sub_right
        (3 ^ m * (20 * 2 ^ (i - d - 1) - 3))
      rwa [sub_self] at this
    have ih := fin_diff i i' K w (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3))
      (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)) (m + 1) (d + 1)
      (fun e h1 h2 => h e (by omega) (by simp only [List.length_cons]; omega))
    show (fin i' w (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)) (m + 1) (d + 1)).1 -
      (fin i w (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) (m + 1) (d + 1)).1 ≡ F' - F [ZMOD 3 ^ K]
    refine ih.trans ?_
    have e1 : (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)) - (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) =
        (F' - F) + ((3:ℤ) ^ m * (20 * 2 ^ (i' - d - 1) - 3) - 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) := by
      ring
    rw [e1]
    have := hT.add_left (F' - F)
    rwa [add_zero] at this

theorem okw_congr (i i' : ℕ) : ∀ (w : List Bool) (F F' : ℤ) (m d : ℕ),
    F ≡ F' [ZMOD 3 ^ (m + w.length)] →
    (∀ e, d ≤ e → e < d + w.length → (2:ℤ) ^ (i - e - 1) ≡ 2 ^ (i' - e - 1) [ZMOD 3 ^ w.length]) →
    (okw i w F m d ↔ okw i' w F' m d)
  | [], _, _, _, _, _, _ => by simp [okw]
  | false :: w, F, F', m, d, hF, h2 => by
    have hF1 : F % 3 ^ (m + 1) = F' % 3 ^ (m + 1) :=
      Int.ModEq.of_dvd (pow_dvd_pow 3 (by simp only [List.length_cons]; omega)) hF
    have r := okw_congr i i' w F F' (m + 1) d
      (by
        have e : m + 1 + w.length = m + (false :: w).length := by simp only [List.length_cons]; omega
        rw [e]; exact hF)
      (fun e h1 h3 => (h2 e h1 (by simp only [List.length_cons]; omega)).of_dvd
        (pow_dvd_pow 3 (by simp only [List.length_cons]; omega)))
    simp only [okw, Int.dvd_iff_emod_eq_zero, hF1, r]
  | true :: w, F, F', m, d, hF, h2 => by
    have h2d := h2 d le_rfl (by simp only [List.length_cons]; omega)
    have hT : (3:ℤ) ^ m * (20 * 2 ^ (i - d - 1) - 3) ≡ 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)
        [ZMOD 3 ^ (m + (true :: w).length)] := by
      rw [pow_add]
      exact Int.ModEq.mul_left' ((h2d.mul_left 20).sub_right 3)
    have hG := hF.add hT
    have hG1 : (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3)) % 3 ^ (m + 1) =
        (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)) % 3 ^ (m + 1) :=
      Int.ModEq.of_dvd (pow_dvd_pow 3 (by simp only [List.length_cons]; omega)) hG
    have r := okw_congr i i' w (F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3))
      (F' + 3 ^ m * (20 * 2 ^ (i' - d - 1) - 3)) (m + 1) (d + 1)
      (by
        have e : m + 1 + w.length = m + (true :: w).length := by simp only [List.length_cons]; omega
        rw [e]; exact hG)
      (fun e h1 h3 => (h2 e (by omega) (by simp only [List.length_cons]; omega)).of_dvd
        (pow_dvd_pow 3 (by simp only [List.length_cons]; omega)))
    simp only [okw, Int.dvd_iff_emod_eq_zero, hG1, r]

theorem okb_le (i : ℕ) : ∀ (D : ℕ) (F : ℤ) (m d : ℕ), BMO5Adm.okb i D F m d = true →
    ∃ v : Fin D → Bool, okw i (List.ofFn v) F m d
  | 0, F, m, d, _ => ⟨Fin.elim0, by simp [okw]⟩
  | D + 1, F, m, d, h => by
    simp only [BMO5Adm.okb, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨v, hv⟩ := okb_le i D F (m + 1) d h2
      refine ⟨Fin.cons false v, ?_⟩
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, okw]
      exact ⟨Int.dvd_of_emod_eq_zero h1, hv⟩
    · obtain ⟨v, hv⟩ := okb_le i D _ (m + 1) (d + 1) h2
      refine ⟨Fin.cons true v, ?_⟩
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, okw]
      exact ⟨Int.dvd_of_emod_eq_zero h1, hv⟩

/-- the fresh-digit lemma: at most one of three lifts satisfies the deepest block -/
theorem fiber (i : ℕ) (w : List Bool) (x : Bool) (hc : w.length + 1 ≤ i) (t1 t2 : ℕ)
    (ht1 : t1 < 3) (ht2 : t2 < 3)
    (h1 : lastc (i + 2 * 3 ^ w.length * t1) x
      (fin (i + 2 * 3 ^ w.length * t1) w (NN (i + 2 * 3 ^ w.length * t1)) 0 0))
    (h2 : lastc (i + 2 * 3 ^ w.length * t2) x
      (fin (i + 2 * 3 ^ w.length * t2) w (NN (i + 2 * 3 ^ w.length * t2)) 0 0)) :
    t1 = t2 := by
  have key : ∀ t, ∃ Z : ℤ,
      (lastc (i + 2 * 3 ^ w.length * t) x
        (fin (i + 2 * 3 ^ w.length * t) w (NN (i + 2 * 3 ^ w.length * t)) 0 0) →
        (3:ℤ) ^ (w.length + 1) ∣ Z) ∧
      Z ≡ (fin i w (NN i) 0 0).1 +
        (if x then 3 ^ w.length * (20 * 2 ^ (i - (fin i w (NN i) 0 0).2.2 - 1) - 3) else 0)
        + 2 * 3 ^ w.length * (t : ℤ) [ZMOD 3 ^ (w.length + 1)] := by
    intro t
    have hm := fin_m (i + 2 * 3 ^ w.length * t) w (NN (i + 2 * 3 ^ w.length * t)) 0 0
    obtain ⟨hd, hdle⟩ := fin_d (i + 2 * 3 ^ w.length * t) i w
      (NN (i + 2 * 3 ^ w.length * t)) (NN i) 0 0
    have hdiff := fin_diff i (i + 2 * 3 ^ w.length * t) (w.length + 1) w (NN i)
      (NN (i + 2 * 3 ^ w.length * t)) 0 0
      (fun e _ he => hpow w.length t i e (by omega))
    have hNt := hN w.length t i
    refine ⟨(fin (i + 2 * 3 ^ w.length * t) w (NN (i + 2 * 3 ^ w.length * t)) 0 0).1 +
      (if x then 3 ^ w.length * (20 * 2 ^ (i + 2 * 3 ^ w.length * t -
        (fin i w (NN i) 0 0).2.2 - 1) - 3) else 0), ?_, ?_⟩
    · intro hl
      unfold lastc at hl
      rw [hm, hd, zero_add] at hl
      cases x
      · simpa using hl
      · simpa using hl
    · have hp : (2:ℤ) ^ (i + 2 * 3 ^ w.length * t - (fin i w (NN i) 0 0).2.2 - 1) ≡
          2 ^ (i - (fin i w (NN i) 0 0).2.2 - 1) [ZMOD 3 ^ (w.length + 1)] :=
        hpow w.length t i _ (by rw [← hd]; omega)
      have hF : (fin (i + 2 * 3 ^ w.length * t) w (NN (i + 2 * 3 ^ w.length * t)) 0 0).1 ≡
          (fin i w (NN i) 0 0).1 + 2 * 3 ^ w.length * (t : ℤ) [ZMOD 3 ^ (w.length + 1)] := by
        have h3 := hdiff.trans hNt
        have h4 := h3.add_right (fin i w (NN i) 0 0).1
        rw [sub_add_cancel] at h4
        rwa [add_comm (2 * 3 ^ w.length * (t : ℤ))] at h4
      cases x
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        exact hF
      · simp only [↓reduceIte]
        have := hF.add (((hp.mul_left 20).sub_right 3).mul_left ((3:ℤ) ^ w.length))
        have e : (fin i w (NN i) 0 0).1 + 2 * 3 ^ w.length * (t : ℤ) +
            3 ^ w.length * (20 * 2 ^ (i - (fin i w (NN i) 0 0).2.2 - 1) - 3) =
            (fin i w (NN i) 0 0).1 + 3 ^ w.length * (20 * 2 ^ (i - (fin i w (NN i) 0 0).2.2 - 1) - 3)
              + 2 * 3 ^ w.length * (t : ℤ) := by ring
        rw [e] at this
        exact this
  obtain ⟨Z1, hZ1, hc1⟩ := key t1
  obtain ⟨Z2, hZ2, hc2⟩ := key t2
  have d1 := (Int.ModEq.dvd hc1.symm)
  have d2 := (Int.ModEq.dvd hc2.symm)
  have e1 := dvd_sub (hZ1 h1) d1
  have e2 := dvd_sub (hZ2 h2) d2
  have e3 := dvd_sub e1 e2
  have e : Z1 - (Z1 - ((fin i w (NN i) 0 0).1 +
        (if x then 3 ^ w.length * (20 * 2 ^ (i - (fin i w (NN i) 0 0).2.2 - 1) - 3) else 0)
        + 2 * 3 ^ w.length * (t1 : ℤ))) -
      (Z2 - (Z2 - ((fin i w (NN i) 0 0).1 +
        (if x then 3 ^ w.length * (20 * 2 ^ (i - (fin i w (NN i) 0 0).2.2 - 1) - 3) else 0)
        + 2 * 3 ^ w.length * (t2 : ℤ)))) = 3 ^ w.length * (2 * ((t1 : ℤ) - t2)) := by ring
  rw [e, pow_succ] at e3
  have e4 := (mul_dvd_mul_iff_left (pow_ne_zero w.length (by norm_num : (3:ℤ) ≠ 0))).mp e3
  omega

open Classical in
theorem word_count (c : ℕ) : ∀ (w : List Bool), w.length + 1 ≤ c →
    ((Finset.range (2 * 3 ^ w.length)).filter (fun r => okw (c + r) w (NN (c + r)) 0 0)).card ≤ 2 := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _; exact (Finset.card_filter_le _ _).trans (by simp)
  | append_singleton w x ih =>
    intro hc
    simp only [List.length_append, List.length_singleton] at hc ⊢
    have hc' : w.length + 1 ≤ c := by omega
    have hMpos : 0 < 2 * 3 ^ w.length := by positivity
    have hsub : (Finset.range (2 * 3 ^ (w.length + 1))).filter
          (fun r => okw (c + r) (w ++ [x]) (NN (c + r)) 0 0) ⊆
        ((Finset.range (2 * 3 ^ w.length)).filter (fun r => okw (c + r) w (NN (c + r)) 0 0)).biUnion
          (fun r => ((Finset.range 3).filter (fun t => lastc (c + r + 2 * 3 ^ w.length * t) x
            (fin (c + r + 2 * 3 ^ w.length * t) w (NN (c + r + 2 * 3 ^ w.length * t)) 0 0))).image
              (fun t => r + 2 * 3 ^ w.length * t)) := by
      intro r' hr'
      rw [Finset.mem_filter, Finset.mem_range] at hr'
      obtain ⟨hlt, hok⟩ := hr'
      rw [okw_append] at hok
      have hdec : r' % (2 * 3 ^ w.length) + 2 * 3 ^ w.length * (r' / (2 * 3 ^ w.length)) = r' :=
        Nat.mod_add_div r' _
      have hrep : c + r' = c + r' % (2 * 3 ^ w.length) +
          2 * 3 ^ w.length * (r' / (2 * 3 ^ w.length)) := by
        rw [Nat.add_assoc, hdec]
      have h3M : 2 * 3 ^ (w.length + 1) = 3 * (2 * 3 ^ w.length) := by rw [pow_succ]; ring
      have ht3 : r' / (2 * 3 ^ w.length) < 3 := by
        rw [Nat.div_lt_iff_lt_mul hMpos]; rw [h3M] at hlt; linarith
      rw [Finset.mem_biUnion]
      refine ⟨r' % (2 * 3 ^ w.length), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.mod_lt _ hMpos, ?_⟩
        have hok1 := hok.1
        rw [hrep] at hok1
        set i := c + r' % (2 * 3 ^ w.length) with hi
        set t := r' / (2 * 3 ^ w.length) with ht
        refine (okw_congr i (i + 2 * 3 ^ w.length * t) w (NN i) (NN (i + 2 * 3 ^ w.length * t)) 0 0
          ?_ ?_).mpr hok1
        · rw [zero_add]
          have hNt := Int.modEq_iff_dvd.mp (hN w.length t i)
          have a1 : (3:ℤ) ^ w.length ∣ 2 * 3 ^ w.length * (t : ℤ) -
              (NN (i + 2 * 3 ^ w.length * t) - NN i) :=
            dvd_trans (pow_dvd_pow 3 (Nat.le_succ _)) hNt
          have a2 : (3:ℤ) ^ w.length ∣ 2 * 3 ^ w.length * (t : ℤ) :=
            Dvd.intro (2 * (t : ℤ)) (by ring)
          have a3 := dvd_sub a2 a1
          rw [sub_sub_cancel] at a3
          exact Int.modEq_iff_dvd.mpr a3
        · intro e _ he
          exact ((hpow w.length t i e (by omega)).symm).of_dvd (pow_dvd_pow 3 (Nat.le_succ _))
      · rw [Finset.mem_image]
        refine ⟨r' / (2 * 3 ^ w.length), ?_, hdec⟩
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨ht3, ?_⟩
        have hok2 := hok.2
        rw [hrep] at hok2
        exact hok2
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ (Finset.range (2 * 3 ^ w.length)).filter (fun r => okw (c + r) w (NN (c + r)) 0 0), 1 := by
        apply Finset.sum_le_sum
        intro r _
        refine (Finset.card_image_le).trans ?_
        rw [Finset.card_le_one]
        intro t1 ht1 t2 ht2
        rw [Finset.mem_filter, Finset.mem_range] at ht1 ht2
        exact fiber (c + r) w x (by omega) t1 t2 ht1.1 ht2.1 ht1.2 ht2.2
      _ = ((Finset.range (2 * 3 ^ w.length)).filter (fun r => okw (c + r) w (NN (c + r)) 0 0)).card := by simp
      _ ≤ 2 := ih hc'

end BMO5C

theorem solution (D : ℕ) :
    ((Finset.range (2 * 3 ^ D)).filter
      (fun r => BMO5Adm.adm D (r + 2 * 3 ^ D * (D + 1)) = true)).card ≤ 2 ^ (D + 1) := by
  classical
  have hcD : D + 1 ≤ 2 * 3 ^ D * (D + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hsub : (Finset.range (2 * 3 ^ D)).filter
        (fun r => BMO5Adm.adm D (r + 2 * 3 ^ D * (D + 1)) = true) ⊆
      (Finset.univ : Finset (Fin D → Bool)).biUnion (fun v =>
        (Finset.range (2 * 3 ^ (List.ofFn v).length)).filter (fun r =>
          BMO5C.okw (2 * 3 ^ D * (D + 1) + r) (List.ofFn v) (BMO5C.NN (2 * 3 ^ D * (D + 1) + r)) 0 0)) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨v, hv⟩ := BMO5C.okb_le (r + 2 * 3 ^ D * (D + 1)) D _ 0 0 hr.2
    rw [Finset.mem_biUnion]
    refine ⟨v, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range, List.length_ofFn, add_comm (2 * 3 ^ D * (D + 1)) r]
    exact ⟨hr.1, hv⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin D → Bool)), 2 := by
      apply Finset.sum_le_sum
      intro v _
      exact BMO5C.word_count _ (List.ofFn v) (by rw [List.length_ofFn]; exact hcD)
    _ = 2 ^ (D + 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        smul_eq_mul, pow_succ]
