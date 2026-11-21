-- Prove2me | solution 1 for FreeOrderEPTAS.claim_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:13:23.404177+00:00
-- url     : https://prove2.me/submissions/7f0a8e9b-8732-4d92-998b-6cd61844a03f

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Schedule
import Definitions.Def_FreeOrderEPTAS_orderOf

open MeasureTheory

namespace Aux_bucket

open FreeOrderEPTAS MeasureTheory

section R

variable {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n))

lemma orc_ge (j : Fin n) (v : ℝ) : v ≤ orc I j v := by
  unfold orc
  have hint : Integrable (fun x => max x v) (I.μ j) := by
    refine Integrable.mono' ((I.integrable j).norm.add (integrable_const |v|))
      ((continuous_id.max continuous_const).aestronglyMeasurable) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, id, Pi.add_apply]
    rcases le_total x v with h | h
    · rw [max_eq_right h]; linarith [abs_nonneg x]
    · rw [max_eq_left h]; linarith [abs_nonneg v]
  have := integral_mono (integrable_const v) hint (fun x => le_max_right x v)
  simpa using this

lemma R_succ (t : ℕ) (ht : t < n) : R I σ t = orc I (σ ⟨t, ht⟩) (R I σ (t + 1)) := by
  unfold R
  rw [List.drop_eq_getElem_cons (by simpa using ht)]
  simp

lemma R_ge_n (t : ℕ) (ht : n ≤ t) : R I σ t = 0 := by
  unfold R
  rw [List.drop_eq_nil_of_le (by simpa using ht)]
  rfl

lemma R_succ_le (t : ℕ) : R I σ (t + 1) ≤ R I σ t := by
  by_cases ht : t < n
  · rw [R_succ I σ t ht]; exact orc_ge I _ _
  · rw [R_ge_n I σ t (by omega), R_ge_n I σ (t + 1) (by omega)]

lemma R_anti : Antitone (R I σ) := antitone_nat_of_succ_le (R_succ_le I σ)

lemma R_nonneg (t : ℕ) : 0 ≤ R I σ t := by
  by_cases ht : t ≤ n
  · have := R_anti I σ ht
    rw [R_ge_n I σ n le_rfl] at this
    exact this
  · rw [R_ge_n I σ t (by omega)]

lemma R_le0 (t : ℕ) : R I σ t ≤ R I σ 0 := R_anti I σ (Nat.zero_le t)

end R

section B

variable {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ)

open Classical

noncomputable def cnt (s : ℕ) : ℕ :=
  ((Finset.range n).filter fun s' => s < s' ∧ IsJump I σ ϵ s').card

open Classical in
lemma bucket_def (s : ℕ) :
    bucket I σ ϵ s = 2 * cnt I σ ϵ s + (if IsJump I σ ϵ s then 1 else 0) := rfl

open Classical in
lemma numJumps_def :
    numJumps I σ ϵ = ((Finset.range n).filter fun s => IsJump I σ ϵ s).card := rfl

lemma jump_lt (s : ℕ) (h : IsJump I σ ϵ s) : s < n := by
  by_contra hs
  push_neg at hs
  obtain ⟨k, h1, h2⟩ := h
  rw [R_ge_n I σ (s + 1) (by omega)] at h1
  rw [R_ge_n I σ s hs] at h2
  linarith

lemma ite_jump_le (s : ℕ) : (if IsJump I σ ϵ s then 1 else 0) ≤ 1 := by
  split_ifs <;> omega

open Classical in
lemma cnt_succ (s : ℕ) :
    cnt I σ ϵ s = cnt I σ ϵ (s + 1) + (if IsJump I σ ϵ (s + 1) then 1 else 0) := by
  unfold cnt
  by_cases hj : IsJump I σ ϵ (s + 1)
  · rw [if_pos hj]
    have hlt := jump_lt I σ ϵ _ hj
    have heq : ((Finset.range n).filter fun s' => s < s' ∧ IsJump I σ ϵ s') =
        insert (s + 1) ((Finset.range n).filter fun s' => s + 1 < s' ∧ IsJump I σ ϵ s') := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
      constructor
      · rintro ⟨hx, hsx, hjx⟩
        by_cases hx1 : x = s + 1
        · exact Or.inl hx1
        · exact Or.inr ⟨hx, by omega, hjx⟩
      · rintro (hx | ⟨hx, hsx, hjx⟩)
        · subst hx; exact ⟨hlt, by omega, hj⟩
        · exact ⟨hx, by omega, hjx⟩
    rw [heq, Finset.card_insert_of_notMem]
    simp
  · rw [if_neg hj, add_zero]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hsx, hjx⟩
      refine ⟨hx, ?_, hjx⟩
      by_contra h
      have : x = s + 1 := by omega
      subst this; exact hj hjx
    · rintro ⟨hx, hsx, hjx⟩; exact ⟨hx, by omega, hjx⟩

open Classical in
lemma numJumps_eq : numJumps I σ ϵ = cnt I σ ϵ 0 + (if IsJump I σ ϵ 0 then 1 else 0) := by
  rw [numJumps_def]
  unfold cnt
  by_cases hj : IsJump I σ ϵ 0
  · rw [if_pos hj]
    have hlt := jump_lt I σ ϵ _ hj
    have heq : ((Finset.range n).filter fun s => IsJump I σ ϵ s) =
        insert 0 ((Finset.range n).filter fun s' => 0 < s' ∧ IsJump I σ ϵ s') := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
      constructor
      · rintro ⟨hx, hjx⟩
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        · exact Or.inr ⟨hx, by omega, hjx⟩
      · rintro (hx | ⟨hx, _, hjx⟩)
        · subst hx; exact ⟨hlt, hj⟩
        · exact ⟨hx, hjx⟩
    rw [heq, Finset.card_insert_of_notMem]
    simp
  · rw [if_neg hj, add_zero]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hjx⟩
      refine ⟨hx, ?_, hjx⟩
      by_contra h
      have : x = 0 := by omega
      subst this; exact hj hjx
    · rintro ⟨hx, _, hjx⟩; exact ⟨hx, hjx⟩

/-- number of jumps at or after `s` -/
noncomputable def G (s : ℕ) : ℕ := cnt I σ ϵ s + (if IsJump I σ ϵ s then 1 else 0)

lemma G_succ (s : ℕ) : G I σ ϵ s = G I σ ϵ (s + 1) + (if IsJump I σ ϵ s then 1 else 0) := by
  unfold G
  rw [cnt_succ I σ ϵ s] <;> ring

lemma G_anti : Antitone (G I σ ϵ) := by
  apply antitone_nat_of_succ_le
  intro s
  have h1 := G_succ I σ ϵ s
  have h2 := ite_jump_le I σ ϵ s
  omega

lemma G_zero : G I σ ϵ 0 = numJumps I σ ϵ := (numJumps_eq I σ ϵ).symm

open Classical in
lemma cnt_ge_n (s : ℕ) (hs : n ≤ s) : cnt I σ ϵ s = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
  intro hx hsx; omega

lemma G_n : G I σ ϵ n = 0 := by
  unfold G
  rw [cnt_ge_n I σ ϵ n le_rfl, zero_add]
  split_ifs with h
  · exact absurd (jump_lt I σ ϵ n h) (lt_irrefl n)
  · rfl

lemma cnt_anti {s s' : ℕ} (h : s ≤ s') : cnt I σ ϵ s' ≤ cnt I σ ϵ s := by
  induction s', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    have := cnt_succ I σ ϵ k
    omega

lemma bucket_eq (s : ℕ) :
    bucket I σ ϵ s + (if IsJump I σ ϵ s then 1 else 0) = 2 * G I σ ϵ s := by
  rw [bucket_def]; unfold G
  have := ite_jump_le I σ ϵ s
  split_ifs <;> omega

lemma bucket_anti : Antitone (bucket I σ ϵ) := by
  apply antitone_nat_of_succ_le
  intro s
  rw [bucket_def, bucket_def, cnt_succ I σ ϵ s]
  have := ite_jump_le I σ ϵ s
  have := ite_jump_le I σ ϵ (s + 1)
  omega

lemma bucket_odd_iff (s : ℕ) : bucket I σ ϵ s % 2 = 1 ↔ IsJump I σ ϵ s := by
  rw [bucket_def]
  by_cases hj : IsJump I σ ϵ s
  · rw [if_pos hj]; simp only [hj, iff_true]; omega
  · rw [if_neg hj]; simp only [hj, iff_false]; omega

lemma bucket_jump_drop {s s' : ℕ} (h : s < s') (hj : IsJump I σ ϵ s') :
    bucket I σ ϵ s' + 1 ≤ bucket I σ ϵ s := by
  have h1 : cnt I σ ϵ (s' - 1) = cnt I σ ϵ s' + 1 := by
    have := cnt_succ I σ ϵ (s' - 1)
    rw [show s' - 1 + 1 = s' by omega, if_pos hj] at this
    exact this
  have h2 : cnt I σ ϵ (s' - 1) ≤ cnt I σ ϵ s := cnt_anti I σ ϵ (by omega)
  rw [bucket_def, bucket_def]
  have := ite_jump_le I σ ϵ s
  have := ite_jump_le I σ ϵ s'
  omega

lemma bucket_lt (s : ℕ) : bucket I σ ϵ s < 2 * numJumps I σ ϵ + 1 := by
  have h1 := bucket_eq I σ ϵ s
  have h2 : G I σ ϵ s ≤ G I σ ϵ 0 := G_anti I σ ϵ (Nat.zero_le s)
  rw [G_zero] at h2
  have h3 := ite_jump_le I σ ϵ s
  omega

open Classical in
lemma endTime_spec (i : ℕ) :
    endTime I σ ϵ i ≤ n ∧ (∀ s, s < endTime I σ ϵ i → i ≤ bucket I σ ϵ s) ∧
      (endTime I σ ϵ i < n → bucket I σ ϵ (endTime I σ ϵ i) < i) := by
  unfold endTime
  cases h : (List.range n).find? (fun s => decide (bucket I σ ϵ s < i)) with
  | none =>
    rw [List.find?_range_eq_none] at h
    simp only [Option.getD_none]
    refine ⟨le_rfl, fun s hs => ?_, fun h' => absurd h' (lt_irrefl _)⟩
    have := h s hs
    simpa using this
  | some e =>
    rw [List.find?_range_eq_some] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [Option.getD_some]
    refine ⟨(List.mem_range.1 h2).le, fun s hs => ?_, fun _ => by simpa using h1⟩
    have := h3 s hs
    simpa using this

lemma cross (a b : ℕ) (hab : a ≤ b) :
    ∀ w, R I σ b < w → w ≤ R I σ a → ∃ s, a ≤ s ∧ s < b ∧ R I σ (s + 1) < w ∧ w ≤ R I σ s := by
  induction b, hab using Nat.le_induction with
  | base => intro w h1 h2; linarith
  | succ b hab ih =>
    intro w h1 h2
    by_cases hw : w ≤ R I σ b
    · exact ⟨b, hab, by omega, h1, hw⟩
    · push_neg at hw
      obtain ⟨s, hs1, hs2, hs3, hs4⟩ := ih w hw h2
      exact ⟨s, hs1, by omega, hs3, hs4⟩

lemma no_mult (hϵ : 0 < ϵ) (hR0 : 0 < R I σ 0) (a b : ℕ) (hab : a ≤ b)
    (hnj : ∀ s, a ≤ s → s < b → ¬ IsJump I σ ϵ s) :
    R I σ a - R I σ b < ϵ * R I σ 0 := by
  by_contra hc
  push_neg at hc
  have hu : 0 < ϵ * R I σ 0 := mul_pos hϵ hR0
  have ha0 : 0 ≤ R I σ a := R_nonneg I σ a
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊R I σ a / (ϵ * R I σ 0)⌋₊ := ⟨_, rfl⟩
  have hk1 : (k : ℝ) * (ϵ * R I σ 0) ≤ R I σ a := by
    have := Nat.floor_le (div_nonneg ha0 hu.le)
    rw [← hk, le_div_iff₀ hu] at this
    exact this
  have hk2 : R I σ b < (k : ℝ) * (ϵ * R I σ 0) := by
    have := Nat.lt_floor_add_one (R I σ a / (ϵ * R I σ 0))
    rw [← hk, div_lt_iff₀ hu] at this
    nlinarith
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := cross I σ a b hab _ hk2 hk1
  exact hnj s hs1 hs2 ⟨k, hs3, hs4⟩

end B

open Classical

theorem main {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) (q : ℕ) (hq : 0 < q)
    (hϵ : ϵ = 1 / (q : ℝ)) :
    (numJumps I σ ϵ : ℝ) ≤ 1 / ϵ ∧
    (∀ i, i < 2 * numJumps I σ ϵ + 1 → Even i →
      BaseVal I σ ϵ (i + 1) - BaseVal I σ ϵ i ≤ ϵ * R I σ 0 ∧
        (0 < R I σ 0 → BaseVal I σ ϵ (i + 1) - BaseVal I σ ϵ i < ϵ * R I σ 0)) ∧
    (∀ i, i < 2 * numJumps I σ ϵ + 1 → Odd i → ∃! s, s < n ∧ bucket I σ ϵ s = i) ∧
    (∀ s, s < n → bucket I σ ϵ s < 2 * numJumps I σ ϵ + 1) ∧
    (∀ s, s < n → (∀ s', s' < n → bucket I σ ϵ s' = bucket I σ ϵ s → s' ≤ s) →
      BaseVal I σ ϵ (bucket I σ ϵ s) = R I σ (s + 1)) ∧
    BaseVal I σ ϵ 0 = 0 ∧
    BaseVal I σ ϵ (2 * numJumps I σ ϵ + 1) = R I σ 0 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hϵ0 : 0 < ϵ := by rw [hϵ]; positivity
  have hinv : 1 / ϵ = q := by rw [hϵ]; field_simp
  have hR0 : 0 ≤ R I σ 0 := R_nonneg I σ 0
  refine ⟨?_, ?_, ?_, fun s _ => bucket_lt I σ ϵ s, ?_, ?_, ?_⟩
  · -- (1) the number of jumps
    rw [hinv]
    by_cases hz : R I σ 0 = 0
    · have : numJumps I σ ϵ = 0 := by
        rw [numJumps_def, Finset.card_eq_zero]
        ext s
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ hj
        obtain ⟨k, h1, _⟩ := hj
        rw [hz, mul_zero, mul_zero] at h1
        linarith [R_nonneg I σ (s + 1)]
      rw [this]; simp
    · have hpos : 0 < R I σ 0 := lt_of_le_of_ne hR0 (Ne.symm hz)
      have hu : 0 < ϵ * R I σ 0 := mul_pos hϵ0 hpos
      have hcard : numJumps I σ ϵ ≤ (Finset.Icc 1 q).card := by
        rw [numJumps_def]
        classical
        refine Finset.card_le_card_of_injOn
          (fun s => if h : IsJump I σ ϵ s then Classical.choose h else 0) ?_ ?_
        · intro s hs
          have hj : IsJump I σ ϵ s := (Finset.mem_filter.1 hs).2
          simp only [dif_pos hj]
          have hspec := Classical.choose_spec hj
          obtain ⟨h1, h2⟩ := hspec
          have hR1 := R_nonneg I σ (s + 1)
          have hRs := R_le0 I σ s
          rw [Finset.mem_coe, Finset.mem_Icc]
          constructor
          · by_contra h0
            push_neg at h0
            have : Classical.choose hj = 0 := by omega
            rw [this] at h1; simp at h1; linarith
          · have h3 : ((Classical.choose hj : ℕ) : ℝ) * (ϵ * R I σ 0) ≤ 1 * R I σ 0 := by linarith
            have h4 : ((Classical.choose hj : ℕ) : ℝ) * ϵ ≤ 1 := by
              have := le_of_mul_le_mul_right (by nlinarith : ((Classical.choose hj : ℕ) : ℝ) * ϵ *
                R I σ 0 ≤ 1 * R I σ 0) hpos
              exact this
            have h5 : ((Classical.choose hj : ℕ) : ℝ) ≤ q := by
              generalize (Classical.choose hj : ℕ) = k at h4 ⊢
              rw [hϵ, mul_one_div, div_le_one hqr] at h4
              exact h4
            exact_mod_cast h5
        · intro s1 hs1 s2 hs2 heq
          have hj1 : IsJump I σ ϵ s1 := (Finset.mem_filter.1 hs1).2
          have hj2 : IsJump I σ ϵ s2 := (Finset.mem_filter.1 hs2).2
          simp only [dif_pos hj1, dif_pos hj2] at heq
          have sp1 := Classical.choose_spec hj1
          have sp2 := Classical.choose_spec hj2
          rw [heq] at sp1
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := R_anti I σ (show s1 + 1 ≤ s2 by omega)
            linarith [sp1.1, sp2.2]
          · have := R_anti I σ (show s2 + 1 ≤ s1 by omega)
            linarith [sp1.2, sp2.1]
      rw [Nat.card_Icc] at hcard
      have : (numJumps I σ ϵ : ℝ) ≤ ((q + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      simpa using this
  · -- (2) stable buckets
    intro i hi he
    have hstrict : 0 < R I σ 0 → BaseVal I σ ϵ (i + 1) - BaseVal I σ ϵ i < ϵ * R I σ 0 := by
      intro hpos
      unfold BaseVal
      obtain ⟨e1le, e1lo, e1hi⟩ := endTime_spec I σ ϵ (i + 1)
      obtain ⟨e0le, e0lo, e0hi⟩ := endTime_spec I σ ϵ i
      by_cases hle : endTime I σ ϵ i ≤ endTime I σ ϵ (i + 1)
      · have := R_anti I σ hle
        have := mul_pos hϵ0 hpos
        linarith
      · push_neg at hle
        apply no_mult I σ ϵ hϵ0 hpos _ _ hle.le
        intro s hs1 hs2 hj
        have hb1 : i ≤ bucket I σ ϵ s := e0lo s hs2
        have hb2 : bucket I σ ϵ (endTime I σ ϵ (i + 1)) < i + 1 := e1hi (by omega)
        have hb3 : bucket I σ ϵ s ≤ bucket I σ ϵ (endTime I σ ϵ (i + 1)) :=
          bucket_anti I σ ϵ hs1
        have hbs : bucket I σ ϵ s = i := by omega
        have := (bucket_odd_iff I σ ϵ s).2 hj
        rw [hbs] at this
        obtain ⟨r, hr⟩ := he
        omega
    refine ⟨?_, hstrict⟩
    by_cases hz : R I σ 0 = 0
    · have hall : ∀ t, R I σ t = 0 := fun t => le_antisymm (hz ▸ R_le0 I σ t) (R_nonneg I σ t)
      unfold BaseVal; rw [hall, hall, hz]; simp
    · exact (hstrict (lt_of_le_of_ne hR0 (Ne.symm hz))).le
  · -- (3) jump buckets
    intro i hi ho
    obtain ⟨c, hc⟩ := ho
    have hcJ : c + 1 ≤ numJumps I σ ϵ := by omega
    have hG0 : c + 1 ≤ G I σ ϵ 0 := by rw [G_zero]; exact hcJ
    obtain ⟨s, hs⟩ : ∃ s, s = Nat.findGreatest (fun s => c + 1 ≤ G I σ ϵ s) n := ⟨_, rfl⟩
    have hspec : c + 1 ≤ G I σ ϵ s := by
      rw [hs]; exact Nat.findGreatest_spec (P := fun s => c + 1 ≤ G I σ ϵ s) (Nat.zero_le n) hG0
    have hsle : s ≤ n := by rw [hs]; exact Nat.findGreatest_le n
    have hsn : s < n := by
      rcases Nat.lt_or_ge s n with h | h
      · exact h
      · have : s = n := by omega
        rw [this, G_n] at hspec; omega
    have hnext : ¬ (c + 1 ≤ G I σ ϵ (s + 1)) := by
      have h := Nat.findGreatest_is_greatest (P := fun s => c + 1 ≤ G I σ ϵ s) (n := n)
        (k := s + 1) (by rw [← hs]; omega) (by omega)
      exact h
    have hGs := G_succ I σ ϵ s
    have hjs : IsJump I σ ϵ s := by
      by_contra hj
      rw [if_neg hj] at hGs; omega
    rw [if_pos hjs] at hGs
    have hcnt : cnt I σ ϵ s = c := by
      have h1 : G I σ ϵ (s + 1) = cnt I σ ϵ s := by
        unfold G; rw [cnt_succ I σ ϵ s]
      omega
    refine ⟨s, ⟨hsn, ?_⟩, ?_⟩
    · rw [bucket_def, if_pos hjs, hcnt]; omega
    · rintro s' ⟨hs'n, hs'b⟩
      have hj' : IsJump I σ ϵ s' := by
        rw [← bucket_odd_iff I σ ϵ s', hs'b, hc]; omega
      have hbs : bucket I σ ϵ s = i := by rw [bucket_def, if_pos hjs, hcnt]; omega
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := bucket_jump_drop I σ ϵ h hjs
        omega
      · have := bucket_jump_drop I σ ϵ h hj'
        omega
  · -- (5) base values of nonempty buckets
    intro s hs hmax
    unfold BaseVal
    obtain ⟨ele, elo, ehi⟩ := endTime_spec I σ ϵ (bucket I σ ϵ s)
    have hge : s + 1 ≤ endTime I σ ϵ (bucket I σ ϵ s) := by
      by_contra h
      push_neg at h
      have h1 := ehi (by omega)
      have h2 := bucket_anti I σ ϵ (show endTime I σ ϵ (bucket I σ ϵ s) ≤ s by omega)
      omega
    have hle : endTime I σ ϵ (bucket I σ ϵ s) ≤ s + 1 := by
      by_contra h
      push_neg at h
      have h1 := elo (s + 1) h
      have h2 := bucket_anti I σ ϵ (show s ≤ s + 1 by omega)
      have h3 := hmax (s + 1) (by omega) (by omega)
      omega
    rw [le_antisymm hle hge]
  · -- (6a)
    unfold BaseVal
    obtain ⟨ele, _, ehi⟩ := endTime_spec I σ ϵ 0
    have : endTime I σ ϵ 0 = n := by
      by_contra h
      have := ehi (by omega)
      omega
    rw [this, R_ge_n I σ n le_rfl]
  · -- (6b)
    unfold BaseVal
    obtain ⟨ele, elo, _⟩ := endTime_spec I σ ϵ (2 * numJumps I σ ϵ + 1)
    have : endTime I σ ϵ (2 * numJumps I σ ϵ + 1) = 0 := by
      by_contra h
      have h1 := elo 0 (by omega)
      have h2 := bucket_lt I σ ϵ 0
      omega
    rw [this]

end Aux_bucket
namespace Aux_VR

open FreeOrderEPTAS

/-- value of the backward recursion for laws `ν` taken in the natural order -/
noncomputable def Rv {n : ℕ} (ν : Fin n → Measure ℝ) (t : ℕ) : ℝ :=
  ((List.finRange n).drop t).foldr (fun s v => ∫ x, max x v ∂(ν s)) 0

lemma Rv_zero_succ {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) :
    Rv ν 0 = ∫ x, max x (Rv (fun j => ν j.succ) 0) ∂(ν 0) := by
  unfold Rv
  rw [List.finRange_succ]
  simp [List.foldr_map]

lemma Rv_shift {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) (t : ℕ) :
    Rv ν (t + 1) = Rv (fun j => ν j.succ) t := by
  unfold Rv
  rw [List.finRange_succ, List.drop_succ_cons, ← List.map_drop, List.foldr_map]

lemma Rv_ge_n {n : ℕ} (ν : Fin n → Measure ℝ) (t : ℕ) (ht : n ≤ t) : Rv ν t = 0 := by
  unfold Rv
  rw [List.drop_eq_nil_of_le (by simpa using ht)]
  rfl

lemma int_max (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) (v : ℝ) :
    Integrable (fun x => max x v) μ := by
  refine Integrable.mono' (hμ.norm.add (integrable_const |v|))
    ((continuous_id.max continuous_const).aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, id, Pi.add_apply]
  rcases le_total x v with h | h
  · rw [max_eq_right h]; linarith [abs_nonneg x]
  · rw [max_eq_left h]; linarith [abs_nonneg v]

lemma measurable_cons_fin {k : ℕ} (a : ℝ) :
    Measurable (fun obs : Fin k → ℝ => (Fin.cons a obs : Fin (k + 1) → ℝ)) := by
  apply measurable_pi_lambda
  intro s
  refine Fin.cases ?_ (fun s => ?_) s
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact measurable_pi_apply s

/-- The rule after the first observation `a`. -/
def shiftRule {n : ℕ} (τ : StoppingRule (n + 1)) (a : ℝ) : StoppingRule n where
  stop t obs := τ.stop t.succ (Fin.cons a obs)
  measurable_stop t := (τ.measurable_stop t.succ).comp (measurable_cons_fin a)

lemma observed_one {n : ℕ} (y : Fin n → ℝ) (t : Fin n) (s : Fin (t.val + 1)) :
    observed 1 y t s = y ⟨s.val, by omega⟩ := rfl

lemma observed_cons_succ {n : ℕ} (a : ℝ) (z : Fin n → ℝ) (t : Fin n) :
    observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t.succ = Fin.cons a (observed 1 z t) := by
  funext s
  refine Fin.cases ?_ (fun s => ?_) s
  · rw [observed_one, Fin.cons_zero]
    have : (⟨(0 : Fin (t.val + 1 + 1)).val, by simp⟩ : Fin (n + 1)) = 0 := rfl
    rw [this, Fin.cons_zero]
  · rw [observed_one, Fin.cons_succ, observed_one]
    have : (⟨(Fin.succ s).val, by simp; omega⟩ : Fin (n + 1)) = Fin.succ ⟨s.val, by omega⟩ :=
      Fin.ext rfl
    rw [this, Fin.cons_succ]

lemma reward_zero (τ : StoppingRule 0) (y : Fin 0 → ℝ) : reward τ 1 y = 0 := by
  unfold reward stopTime
  simp

lemma reward_cons {n : ℕ} (τ : StoppingRule (n + 1)) (a : ℝ) (z : Fin n → ℝ) :
    reward τ 1 (Fin.cons a z : Fin (n + 1) → ℝ) =
      if τ.stop 0 (fun _ => a) then a else reward (shiftRule τ a) 1 z := by
  have h0 : observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) 0 = fun _ => a := by
    funext s
    rw [observed_one]
    have : (⟨s.val, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (by
      have h1 := s.isLt
      simp only [Fin.val_zero, Fin.val_mk] at h1 ⊢
      omega)
    rw [this, Fin.cons_zero]
  unfold reward stopTime
  rw [List.finRange_succ]
  by_cases hs : τ.stop 0 (fun _ => a) = true
  · have hp0 : (fun t : Fin (n + 1) =>
        τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) 0 = true := by
      show τ.stop 0 (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) 0) = true
      rw [h0]; exact hs
    rw [List.find?_cons_of_pos (p := fun t : Fin (n + 1) =>
      τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) (a := 0)
      (l := List.map Fin.succ (List.finRange n)) hp0, if_pos hs]
    rfl
  · have hp0 : ¬ ((fun t : Fin (n + 1) =>
        τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) 0 = true) := by
      show ¬ τ.stop 0 (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) 0) = true
      rw [h0]; exact hs
    rw [List.find?_cons_of_neg (p := fun t : Fin (n + 1) =>
      τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) (a := 0)
      (l := List.map Fin.succ (List.finRange n)) hp0, if_neg hs, List.find?_map]
    have hp : ((fun t : Fin (n + 1) => τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) ∘
        Fin.succ) = fun t => (shiftRule τ a).stop t (observed 1 z t) := by
      funext t
      rw [Function.comp_apply]
      show τ.stop t.succ (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t.succ) = _
      rw [observed_cons_succ]
      rfl
    rw [hp]
    cases h : List.find? (fun t => (shiftRule τ a).stop t (observed 1 z t)) (List.finRange n) with
    | none => rfl
    | some t =>
      simp only [Option.map_some]
      show (Fin.cons a z : Fin (n + 1) → ℝ) ((1 : Equiv.Perm (Fin (n + 1))) t.succ) =
        z ((1 : Equiv.Perm (Fin n)) t)
      simp

lemma reward_abs_le {n : ℕ} (τ : StoppingRule n) (y : Fin n → ℝ) :
    |reward τ 1 y| ≤ ∑ i, |y i| := by
  unfold reward
  split
  · exact Finset.single_le_sum (f := fun i => |y i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ _)
  · simp only [abs_zero]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma measurable_observed {n : ℕ} (t : Fin n) :
    Measurable (fun y : Fin n → ℝ => observed 1 y t) := by
  apply measurable_pi_lambda
  intro s
  exact measurable_pi_apply _

lemma reward_eq_sum {n : ℕ} (τ : StoppingRule n) (y : Fin n → ℝ) :
    reward τ 1 y = ∑ t : Fin n,
      (if (∀ s : Fin n, s < t → τ.stop s (observed 1 y s) = false) ∧
        τ.stop t (observed 1 y t) = true then y t else 0) := by
  unfold reward stopTime
  cases h : List.find? (fun t => τ.stop t (observed 1 y t)) (List.finRange n) with
  | none =>
    rw [List.find?_eq_none] at h
    symm
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact h t (List.mem_finRange t) h2
  | some t0 =>
    rw [List.find?_eq_some_iff_getElem] at h
    obtain ⟨h1, i, hi, hget, hbefore⟩ := h
    have hi' : i = t0.val := by
      have := congrArg Fin.val hget
      simpa using this
    have hprev : ∀ s : Fin n, s < t0 → τ.stop s (observed 1 y s) = false := by
      intro s hs
      have hlt : s.val < i := by rw [hi']; exact hs
      have h2 := hbefore s.val hlt
      have hget' : (List.finRange n)[s.val]'(by rw [List.length_finRange]; exact s.isLt) = s := by
        apply Fin.ext; simp
      rw [hget'] at h2
      simpa using h2
    symm
    rw [Finset.sum_eq_single t0]
    · rw [if_pos ⟨hprev, h1⟩]; rfl
    · intro t _ ht
      rw [if_neg]
      rintro ⟨h2, h3⟩
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · rw [hprev t hlt] at h3; exact absurd h3 (by simp)
      · have := h2 t0 hgt
        rw [this] at h1; exact absurd h1 (by simp)
    · intro h; exact absurd (Finset.mem_univ _) h

lemma reward_measurable {n : ℕ} (τ : StoppingRule n) : Measurable (reward τ 1) := by
  have hfun : reward τ 1 = fun y => ∑ t : Fin n,
      (if (∀ s : Fin n, s < t → τ.stop s (observed 1 y s) = false) ∧
        τ.stop t (observed 1 y t) = true then y t else 0) := funext (reward_eq_sum τ)
  rw [hfun]
  apply Finset.measurable_sum
  intro t _
  have hm : ∀ s : Fin n, Measurable (fun y : Fin n → ℝ => τ.stop s (observed 1 y s)) :=
    fun s => (τ.measurable_stop s).comp (measurable_observed s)
  refine Measurable.ite ?_ (measurable_pi_apply t) measurable_const
  have hset : {y : Fin n → ℝ | (∀ s : Fin n, s < t → τ.stop s (observed 1 y s) = false) ∧
      τ.stop t (observed 1 y t) = true} =
      (⋂ s : Fin n, {y | s < t → τ.stop s (observed 1 y s) = false}) ∩
        ((fun y => τ.stop t (observed 1 y t)) ⁻¹' {true}) := by
    ext y; simp
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun s => ?_) ((hm t) (measurableSet_singleton _))
  by_cases hst : s < t
  · have : {y : Fin n → ℝ | s < t → τ.stop s (observed 1 y s) = false} =
        (fun y => τ.stop s (observed 1 y s)) ⁻¹' {false} := by
      ext y; simp [hst]
    rw [this]; exact (hm s) (measurableSet_singleton _)
  · have : {y : Fin n → ℝ | s < t → τ.stop s (observed 1 y s) = false} = Set.univ := by
      ext y; simp [hst]
    rw [this]; exact MeasurableSet.univ

lemma reward_integrable {n : ℕ} (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule n) :
    Integrable (reward τ 1) (Measure.pi ν) := by
  have hsum : Integrable (fun y : Fin n → ℝ => ∑ i, |y i|) (Measure.pi ν) := by
    apply integrable_finset_sum
    intro i _
    exact (integrable_eval (μ := ν) (hint i)).abs
  refine Integrable.mono' hsum (reward_measurable τ).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs]
  exact reward_abs_le τ y

/-- The key step: splitting off the first coordinate. -/
lemma integral_split {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule (n + 1)) :
    Integrable (fun a => ∫ z, reward τ 1 (Fin.cons a z : Fin (n + 1) → ℝ)
      ∂(Measure.pi fun j => ν j.succ)) (ν 0) ∧
    ∫ y, reward τ 1 y ∂(Measure.pi ν) =
      ∫ a, ∫ z, reward τ 1 (Fin.cons a z : Fin (n + 1) → ℝ) ∂(Measure.pi fun j => ν j.succ)
        ∂(ν 0) := by
  have hmp := (measurePreserving_piFinSuccAbove ν 0).symm
  have hI := reward_integrable ν hP hint τ
  have hI2 : Integrable (fun p : ℝ × (Fin n → ℝ) => reward τ 1 (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ))
      ((ν 0).prod (Measure.pi fun j => ν j.succ)) := by
    have := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hI
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero',
      Function.comp_def] using this
  refine ⟨hI2.integral_prod_left, ?_⟩
  calc ∫ y, reward τ 1 y ∂(Measure.pi ν)
      = ∫ p, reward τ 1 ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p)
          ∂((ν 0).prod (Measure.pi fun j => ν j.succ)) := (hmp.integral_comp' _).symm
    _ = ∫ p, reward τ 1 (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)
          ∂((ν 0).prod (Measure.pi fun j => ν j.succ)) := by
        congr 1
        funext p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    _ = _ := integral_prod _ hI2

theorem bound : ∀ (n : ℕ) (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule n),
    ∫ y, reward τ 1 y ∂(Measure.pi ν) ≤ Rv ν 0 := by
  intro n
  induction n with
  | zero =>
    intro ν hP hint τ
    simp [reward_zero, Rv]
  | succ n ih =>
    intro ν hP hint τ
    obtain ⟨hIa, hE⟩ := integral_split ν hP hint τ
    rw [hE, Rv_zero_succ]
    haveI := hP 0
    apply integral_mono hIa (int_max (ν 0) (hint 0) _)
    intro a
    simp only [reward_cons]
    by_cases hs : τ.stop 0 (fun _ => a) = true
    · haveI : ∀ j, IsProbabilityMeasure ((fun j : Fin n => ν j.succ) j) := fun j => hP j.succ
      simp only [hs, if_true]
      simp
    · simp only [hs, if_false, Bool.false_eq_true]
      have := ih (fun j => ν j.succ) (fun j => hP j.succ) (fun j => hint j.succ) (shiftRule τ a)
      exact le_trans this (le_max_right _ _)

theorem attained : ∀ (n : ℕ) (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule n)
    (hτ : ∀ t obs, τ.stop t obs = decide (Rv ν (t.val + 1) ≤ obs (Fin.last t.val))),
    ∫ y, reward τ 1 y ∂(Measure.pi ν) = Rv ν 0 := by
  intro n
  induction n with
  | zero =>
    intro ν hP hint τ _
    simp [reward_zero, Rv]
  | succ n ih =>
    intro ν hP hint τ hτ
    obtain ⟨_, hE⟩ := integral_split ν hP hint τ
    rw [hE, Rv_zero_succ]
    apply integral_congr_ae
    filter_upwards with a
    simp only [reward_cons]
    have hτ' : ∀ (t : Fin n) obs, (shiftRule τ a).stop t obs =
        decide (Rv (fun j => ν j.succ) (t.val + 1) ≤ obs (Fin.last t.val)) := by
      intro t obs
      show τ.stop t.succ (Fin.cons a obs) = _
      rw [hτ]
      have e1 : (Fin.cons a obs : Fin (t.val + 1 + 1) → ℝ) (Fin.last (t.succ.val)) =
          obs (Fin.last t.val) := by
        have : (Fin.last (t.succ.val) : Fin (t.val + 1 + 1)) = Fin.succ (Fin.last t.val) := rfl
        rw [this, Fin.cons_succ]
      rw [e1]
      congr 2
      have := Rv_shift ν (t.val + 1)
      simpa using this
    have h0 : τ.stop 0 (fun _ => a) = decide (Rv (fun j => ν j.succ) 0 ≤ a) := by
      rw [hτ]
      have := Rv_shift ν 0
      simp only [Fin.val_zero, zero_add] at this ⊢
      rw [this]
    rw [h0]
    have hrec := ih (fun j => ν j.succ) (fun j => hP j.succ) (fun j => hint j.succ)
      (shiftRule τ a) hτ'
    by_cases hc : Rv (fun j => ν j.succ) 0 ≤ a
    · haveI : ∀ j, IsProbabilityMeasure ((fun j : Fin n => ν j.succ) j) := fun j => hP j.succ
      simp [hc, max_eq_left hc]
    · simp only [hc, decide_false, Bool.false_eq_true, if_false]
      rw [hrec, max_eq_right (le_of_lt (lt_of_not_ge hc))]


/-- the threshold rule (a local copy) -/
noncomputable def thr {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) : StoppingRule n where
  stop t obs := decide (R I σ (t.val + 1) ≤ obs (Fin.last t.val))
  measurable_stop t := by
    refine measurable_to_bool ?_
    have : (fun obs : Fin (t.val + 1) → ℝ => decide (R I σ (t.val + 1) ≤ obs (Fin.last t.val))) ⁻¹'
        {true} = {obs | R I σ (t.val + 1) ≤ obs (Fin.last t.val)} := by
      ext obs; simp
    rw [this]
    exact measurableSet_le measurable_const (measurable_pi_apply _)

theorem V_eq_R {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) : V I σ = R I σ 0 := by
  set ν : Fin n → Measure ℝ := fun i => I.μ (σ i) with hν
  have hP : ∀ i, IsProbabilityMeasure (ν i) := fun i => I.prob (σ i)
  have hint : ∀ i, Integrable id (ν i) := fun i => I.integrable (σ i)
  have hR : ∀ t, R I σ t = Rv ν t := fun t => rfl
  have hreward : ∀ (τ : StoppingRule n) (x : Fin n → ℝ),
      reward τ σ x = reward τ 1 (fun i => x (σ i)) := fun τ x => rfl
  have hmp := (measurePreserving_piCongrLeft I.μ σ).symm
  have hint_eq : ∀ τ : StoppingRule n,
      ∫ x, reward τ σ x ∂(Measure.pi I.μ) = ∫ y, reward τ 1 y ∂(Measure.pi ν) := by
    intro τ
    calc ∫ x, reward τ σ x ∂(Measure.pi I.μ)
        = ∫ x, reward τ 1 ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).symm x)
            ∂(Measure.pi I.μ) := by
          congr 1
      _ = ∫ y, reward τ 1 y ∂(Measure.pi ν) := hmp.integral_comp' _
  have hle : ∀ τ : StoppingRule n, ∫ x, reward τ σ x ∂(Measure.pi I.μ) ≤ R I σ 0 := by
    intro τ
    rw [hint_eq, hR]
    exact bound n ν hP hint τ
  have heq : ∫ x, reward (thr I σ) σ x ∂(Measure.pi I.μ) = R I σ 0 := by
    rw [hint_eq, hR]
    exact attained n ν hP hint _ (fun t obs => rfl)
  unfold V
  haveI : Nonempty (StoppingRule n) := ⟨thr I σ⟩
  apply le_antisymm
  · exact ciSup_le hle
  · rw [← heq]
    exact le_ciSup ⟨R I σ 0, by rintro _ ⟨τ, rfl⟩; exact hle τ⟩ (thr I σ)

end Aux_VR

namespace Aux_C34

open FreeOrderEPTAS MeasureTheory

lemma int_sub_max {n : ℕ} (I : Instance n) (j : Fin n) (v : ℝ) :
    Integrable (fun x => max (x - v) 0) (I.μ j) := by
  refine Integrable.mono' ((I.integrable j).norm.add (integrable_const |v|))
    (((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, id, Pi.add_apply]
  rcases le_total (x - v) 0 with h | h
  · rw [max_eq_right h]; simp; positivity
  · rw [max_eq_left h, abs_of_nonneg h]
    have h1 := le_abs_self x
    have h2 := neg_abs_le v
    linarith

lemma orc_eq {n : ℕ} (I : Instance n) (j : Fin n) (v : ℝ) :
    orc I j v = v + excess I j v := by
  unfold orc excess
  have h : (fun x => max x v) = fun x => v + max (x - v) 0 := by
    funext x
    rcases le_total x v with hx | hx
    · rw [max_eq_right hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_left hx, max_eq_left (by linarith)]; ring
  rw [h, integral_add (integrable_const v) (int_sub_max I j v)]
  simp

lemma orc_mono {n : ℕ} (I : Instance n) (j : Fin n) {v w : ℝ} (hvw : v ≤ w) :
    orc I j v ≤ orc I j w := by
  unfold orc
  exact integral_mono (Aux_VR.int_max (I.μ j) (I.integrable j) v)
    (Aux_VR.int_max (I.μ j) (I.integrable j) w) (fun x => max_le_max le_rfl hvw)

lemma excess_nonneg {n : ℕ} (I : Instance n) (j : Fin n) (v : ℝ) : 0 ≤ excess I j v := by
  unfold excess
  exact integral_nonneg (fun x => le_max_right _ _)

lemma excess_anti {n : ℕ} (I : Instance n) (j : Fin n) {v w : ℝ} (hvw : v ≤ w) :
    excess I j w ≤ excess I j v := by
  unfold excess
  exact integral_mono (int_sub_max I j w) (int_sub_max I j v)
    (fun x => max_le_max (by linarith) le_rfl)

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by unfold bit; split_ifs <;> norm_num

theorem main {n : ℕ} (I : Instance n) (σs : Equiv.Perm (Fin n)) (ϵ E : ℝ)
    (b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ) (x : Assignment (2 * numJumps I σs ϵ + 1) n)
    (h : Schedule I σs ϵ E b Δ x) (t : Fin n) (i : Fin (2 * numJumps I σs ϵ + 1))
    (ht : IsFirstAhead I (orderOf x) b x t i) :
    BaseVal I σs ϵ i.val + (1 - ϵ) * Δ i - 2 * ϵ * OPT I ≤ R I (orderOf x) t.val := by
  obtain ⟨q, hq, hϵ⟩ := h.inv_int
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hϵ0 : 0 < ϵ := by rw [hϵ]; positivity
  have hϵ1 : ϵ ≤ 1 := by rw [hϵ, div_le_one (by linarith)]; exact hqr
  have hOPT : OPT I = R I σs 0 := by rw [← h.optimal, Aux_VR.V_eq_R]
  have hOPT0 : 0 ≤ OPT I := by rw [hOPT]; exact Aux_bucket.R_nonneg I σs 0
  have hE := h.est_upper
  have hbl := h.guess.base_lower i
  obtain ⟨hx, hbR, _⟩ := ht
  have hRt := Aux_bucket.R_succ_le I (orderOf x) t.val
  have hϵ2 : ϵ ^ 2 * E ≤ ϵ * OPT I := by
    have h1 : ϵ ^ 2 * E ≤ ϵ ^ 2 * OPT I := mul_le_mul_of_nonneg_left hE (sq_nonneg ϵ)
    have h2 : ϵ ^ 2 * OPT I ≤ ϵ * OPT I := by
      apply mul_le_mul_of_nonneg_right _ hOPT0; nlinarith
    linarith
  by_cases hev : Even i.val
  · have hΔ := h.guess.delta_upper i
    have hΔ0 := h.guess.delta_nonneg i
    have hbk := ((Aux_bucket.main I σs ϵ q hq hϵ).2.1 i.val i.isLt hev).1
    rw [← hOPT] at hbk
    have h1 : (1 - ϵ) * Δ i ≤ Δ i := by nlinarith
    linarith
  · have hodd : i.val % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hev)
    have hcard := h.card.2 i hodd
    have hsum : ∑ j, excess I j (b i) * bit (x i j) = excess I (orderOf x t) (b i) := by
      rw [Finset.sum_eq_single (orderOf x t)]
      · rw [hx]; simp [bit]
      · intro j _ hj
        have hxj : x i j = false := by
          by_contra hc
          have hc' : x i j = true := by simpa using hc
          have hsub : ({j, orderOf x t} : Finset (Fin n)) ⊆
              Finset.univ.filter fun j => x i j = true := by
            intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl
            · simp [hc']
            · simp [hx]
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hj] at this
          omega
        rw [hxj]; simp [bit]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    have hload := h.load i
    rw [hsum] at hload
    have hR := Aux_bucket.R_succ I (orderOf x) t.val t.isLt
    have hfin : (⟨t.val, t.isLt⟩ : Fin n) = t := rfl
    rw [hfin] at hR
    have hmono := orc_mono I (orderOf x t) hbR
    rw [← hR, orc_eq] at hmono
    have hpos : 0 ≤ ϵ * OPT I := mul_nonneg hϵ0.le hOPT0
    linarith

end Aux_C34

open FreeOrderEPTAS in
theorem solution {n : ℕ} (I : Instance n) (σs : Equiv.Perm (Fin n)) (ϵ E : ℝ)
    (b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ) (x : Assignment (2 * numJumps I σs ϵ + 1) n)
    (h : Schedule I σs ϵ E b Δ x) (t : Fin n) (i : Fin (2 * numJumps I σs ϵ + 1))
    (ht : IsFirstAhead I (orderOf x) b x t i) :
    BaseVal I σs ϵ i.val + (1 - ϵ) * Δ i - 2 * ϵ * OPT I ≤ R I (orderOf x) t.val :=
  Aux_C34.main I σs ϵ E b Δ x h t i ht
