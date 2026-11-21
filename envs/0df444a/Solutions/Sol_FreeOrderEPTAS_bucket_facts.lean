-- Prove2me | solution 1 for FreeOrderEPTAS.bucket_facts
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:49:40.907375+00:00
-- url     : https://prove2.me/submissions/f399dd55-ced6-4f4a-a283-630598523e3f

import Mathlib
import Definitions.Def_FreeOrderEPTAS_bucket

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

open FreeOrderEPTAS in
theorem solution {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ : ℝ) (q : ℕ) (hq : 0 < q)
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
    BaseVal I σ ϵ (2 * numJumps I σ ϵ + 1) = R I σ 0 :=
  Aux_bucket.main I σ ϵ q hq hϵ
