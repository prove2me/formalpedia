-- Prove2me | solution 1 for Devaney.period_three_implies_all_periods
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T01:19:25.291841+00:00
-- url     : https://prove2.me/submissions/4acf76ed-dda5-4091-b7fe-02e2a0d9fc34

import Mathlib
import Definitions.Def_Devaney_sarkovskii

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Sark

open Devaney

/-- If `f p = c`, `f q = d` with `p ≤ q` and `c ≤ d`, then some subinterval of `[p,q]` is
carried exactly onto `[c,d]`. -/
theorem shrink_aux (f : ℝ → ℝ) (hf : Continuous f) {p q c d : ℝ} (hpq : p ≤ q) (hcd : c ≤ d)
    (hp : f p = c) (hq : f q = d) :
    ∃ a' b', p ≤ a' ∧ a' ≤ b' ∧ b' ≤ q ∧ f '' Set.Icc a' b' = Set.Icc c d := by
  classical
  set S : Set ℝ := Set.Icc p q ∩ f ⁻¹' {c} with hS
  have hSne : S.Nonempty := ⟨p, ⟨le_rfl, hpq⟩, hp⟩
  have hScomp : IsCompact S :=
    isCompact_Icc.inter_right ((isClosed_singleton).preimage hf)
  set a' := sSup S with ha'
  have ha'S : a' ∈ S := hScomp.sSup_mem hSne
  have ha'le : ∀ u ∈ S, u ≤ a' := fun u hu => le_csSup hScomp.bddAbove hu
  set T : Set ℝ := Set.Icc a' q ∩ f ⁻¹' {d} with hT
  have hTne : T.Nonempty := ⟨q, ⟨ha'S.1.2, le_rfl⟩, hq⟩
  have hTcomp : IsCompact T :=
    isCompact_Icc.inter_right ((isClosed_singleton).preimage hf)
  set b' := sInf T with hb'
  have hb'T : b' ∈ T := hTcomp.sInf_mem hTne
  have hb'le : ∀ u ∈ T, b' ≤ u := fun u hu => csInf_le hTcomp.bddBelow hu
  have hfa' : f a' = c := ha'S.2
  have hfb' : f b' = d := hb'T.2
  have hab' : a' ≤ b' := hb'T.1.1
  refine ⟨a', b', ha'S.1.1, hab', hb'T.1.2, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨t, ht, rfl⟩
    constructor
    · by_contra hlt
      push Not at hlt
      have hcmem : c ∈ Set.Icc (f t) (f b') := by rw [hfb']; exact ⟨le_of_lt hlt, hcd⟩
      obtain ⟨u, hu, hfu⟩ :=
        intermediate_value_Icc ht.2 (hf.continuousOn : ContinuousOn f (Set.Icc t b')) hcmem
      have huS : u ∈ S := ⟨⟨le_trans ha'S.1.1 (le_trans ht.1 hu.1),
        le_trans hu.2 hb'T.1.2⟩, hfu⟩
      have : u ≤ a' := ha'le u huS
      have hta' : t = a' := le_antisymm (le_trans hu.1 this) ht.1
      rw [hta', hfa'] at hlt
      exact lt_irrefl c hlt
    · by_contra hgt
      push Not at hgt
      have hdmem : d ∈ Set.Icc (f a') (f t) := by rw [hfa']; exact ⟨hcd, le_of_lt hgt⟩
      obtain ⟨u, hu, hfu⟩ :=
        intermediate_value_Icc ht.1 (hf.continuousOn : ContinuousOn f (Set.Icc a' t)) hdmem
      have huT : u ∈ T := ⟨⟨hu.1, le_trans (le_trans hu.2 ht.2) hb'T.1.2⟩, hfu⟩
      have : b' ≤ u := hb'le u huT
      have htb' : t = b' := le_antisymm ht.2 (le_trans this hu.2)
      rw [htb', hfb'] at hgt
      exact lt_irrefl d hgt
  · have := intermediate_value_Icc hab' (hf.continuousOn : ContinuousOn f (Set.Icc a' b'))
    rwa [hfa', hfb'] at this


/-- Any interval covering can be shrunk to an exact one. -/
theorem shrink (f : ℝ → ℝ) (hf : Continuous f) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hcov : Set.Icc c d ⊆ f '' Set.Icc a b) :
    ∃ a' b', a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧ f '' Set.Icc a' b' = Set.Icc c d := by
  obtain ⟨p, hp, hpc⟩ := hcov (Set.left_mem_Icc.2 hcd)
  obtain ⟨q, hq, hqd⟩ := hcov (Set.right_mem_Icc.2 hcd)
  rcases le_total p q with hpq | hqp
  · obtain ⟨a', b', h1, h2, h3, h4⟩ := shrink_aux f hf hpq hcd hpc hqd
    exact ⟨a', b', le_trans hp.1 h1, h2, le_trans h3 hq.2, h4⟩
  · have hneg : Continuous (fun x => -f x) := hf.neg
    obtain ⟨a', b', h1, h2, h3, h4⟩ :=
      shrink_aux (fun x => -f x) hneg hqp (neg_le_neg hcd) (by simp [hqd]) (by simp [hpc])
    refine ⟨a', b', le_trans hq.1 h1, h2, le_trans h3 hp.2, ?_⟩
    have himg : (fun x => -f x) '' Set.Icc a' b' = Set.Icc (-d) (-c) := h4
    have : f '' Set.Icc a' b' = Neg.neg '' ((fun x => -f x) '' Set.Icc a' b') := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨-f t, ⟨t, ht, rfl⟩, by ring⟩
      · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩; exact ⟨t, ht, by ring⟩
    rw [this, himg]
    ext y
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩; constructor <;> linarith
    · rintro ⟨hy1, hy2⟩; exact ⟨-y, ⟨by linarith, by linarith⟩, by ring⟩

/-- Pulling a covering chain back: some subinterval of the first interval is carried exactly
onto the last, with every intermediate iterate inside the corresponding interval. -/
theorem pullback_chain (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ (n : ℕ) (a b : ℕ → ℝ), (∀ i ≤ n, a i ≤ b i) →
      (∀ i < n, Covers f (Set.Icc (a i) (b i)) (Set.Icc (a (i + 1)) (b (i + 1)))) →
      ∃ u v, a 0 ≤ u ∧ u ≤ v ∧ v ≤ b 0 ∧
        f^[n] '' Set.Icc u v = Set.Icc (a n) (b n) ∧
        ∀ y ∈ Set.Icc u v, ∀ k ≤ n, f^[k] y ∈ Set.Icc (a k) (b k) := by
  intro n
  induction n with
  | zero =>
    intro a b hab hcov
    refine ⟨a 0, b 0, le_rfl, hab 0 le_rfl, le_rfl, by simp, ?_⟩
    intro y hy k hk
    interval_cases k
    simpa using hy
  | succ n ih =>
    intro a b hab hcov
    obtain ⟨u1, v1, h1, h2, h3, h4, h5⟩ :=
      ih (fun i => a (i + 1)) (fun i => b (i + 1))
        (fun i hi => hab (i + 1) (by omega)) (fun i hi => hcov (i + 1) (by omega))
    have hcov0 : Set.Icc u1 v1 ⊆ f '' Set.Icc (a 0) (b 0) := by
      refine Set.Subset.trans ?_ (hcov 0 (by omega))
      exact Set.Icc_subset_Icc h1 h3
    obtain ⟨u, v, g1, g2, g3, g4⟩ := shrink f hf (hab 0 (by omega)) h2 hcov0
    refine ⟨u, v, g1, g2, g3, ?_, ?_⟩
    · rw [Function.iterate_succ, Set.image_comp, g4]
      exact h4
    · intro y hy k hk
      match k with
      | 0 => simpa using Set.Icc_subset_Icc g1 g3 hy
      | (j + 1) =>
        have hfy : f y ∈ Set.Icc u1 v1 := by
          rw [← g4]; exact ⟨y, hy, rfl⟩
        have := h5 (f y) hfy j (by omega)
        rw [Function.iterate_succ_apply]
        exact this


theorem fixed_of_covers (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ)
    (hab : a ≤ b) (h : Covers f (Set.Icc a b) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = x := by
  obtain ⟨p, hp, hpa⟩ := h (Set.left_mem_Icc.2 hab)
  obtain ⟨q, hq, hqb⟩ := h (Set.right_mem_Icc.2 hab)
  have hgc : ContinuousOn (fun x => f x - x) (Set.uIcc p q) :=
    (hf.sub continuous_id).continuousOn
  have hgp : f p - p ≤ 0 := by rw [hpa]; linarith [hp.1]
  have hgq : 0 ≤ f q - q := by rw [hqb]; linarith [hq.2]
  obtain ⟨x, hx, hx0⟩ :=
    intermediate_value_uIcc hgc (Set.mem_uIcc.2 (Or.inl ⟨hgp, hgq⟩))
  exact ⟨x, Set.uIcc_subset_Icc hp hq hx, by linarith [hx0]⟩

/-- A closed covering loop carries a periodic point that follows the loop. -/
theorem loop_periodic (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (a b : ℕ → ℝ) (hab : ∀ i ≤ n, a i ≤ b i)
    (hcov : ∀ i < n, Covers f (Set.Icc (a i) (b i)) (Set.Icc (a (i + 1)) (b (i + 1))))
    (hla : a n = a 0) (hlb : b n = b 0) :
    ∃ x, f^[n] x = x ∧ ∀ k ≤ n, f^[k] x ∈ Set.Icc (a k) (b k) := by
  obtain ⟨u, v, g1, g2, g3, g4, g5⟩ := pullback_chain f hf n a b hab hcov
  have hcover : Covers (f^[n]) (Set.Icc u v) (Set.Icc u v) := by
    rw [Covers, g4, hla, hlb]
    exact Set.Icc_subset_Icc g1 g3
  obtain ⟨x, hx, hfx⟩ :=
    fixed_of_covers (f^[n]) (hf.iterate n) u v g2 hcover
  exact ⟨x, hfx, fun k hk => g5 x hx k hk⟩

theorem iterate_mod {f : ℝ → ℝ} {x : ℝ} {m : ℕ} (hm : 0 < m) (h : f^[m] x = x) :
    ∀ k : ℕ, f^[k] x = f^[k % m] x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k m with hk | hk
    · rw [Nat.mod_eq_of_lt hk]
    · have hsub : k - m + m = k := by omega
      have h1 : f^[k] x = f^[k - m] x := by
        conv_lhs => rw [← hsub]
        rw [Function.iterate_add_apply, h]
      rw [h1, ih (k - m) (by omega), Nat.mod_eq_sub_mod hk]


/-- The oriented three-cycle case: `a < b < c` with `a ↦ b ↦ c ↦ a`. -/
theorem periods_of_cycle (f : ℝ → ℝ) (hf : Continuous f) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (ha : f a = b) (hb : f b = c) (hc : f c = a)
    (n : ℕ) (hn : 0 < n) : ∃ x, HasPrimePeriod f x n := by
  have cov01 : Covers f (Set.Icc a b) (Set.Icc b c) := by
    have h := intermediate_value_Icc (le_of_lt hab) (hf.continuousOn : ContinuousOn f (Set.Icc a b))
    rwa [ha, hb] at h
  have cov1 : Covers f (Set.Icc b c) (Set.Icc a c) := by
    have h := intermediate_value_Icc' (le_of_lt hbc) (hf.continuousOn : ContinuousOn f (Set.Icc b c))
    rwa [hb, hc] at h
  have cov11 : Covers f (Set.Icc b c) (Set.Icc b c) :=
    Set.Subset.trans (Set.Icc_subset_Icc (le_of_lt hab) le_rfl) cov1
  have cov10 : Covers f (Set.Icc b c) (Set.Icc a b) :=
    Set.Subset.trans (Set.Icc_subset_Icc le_rfl (le_of_lt hbc)) cov1
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- n = 1 : a fixed point inside `[b,c]`
    have hn1' : n = 1 := by omega
    obtain ⟨x, -, hx⟩ := fixed_of_covers f hf b c (le_of_lt hbc) cov11
    refine ⟨x, hn, ?_, ?_⟩
    · rw [hn1']; simpa using hx
    · intro m hm hmn; rw [hn1'] at hmn; omega
  · -- n ≥ 2 : the loop `I₁ → ⋯ → I₁ → I₀ → I₁`
    set A : ℕ → ℝ := fun k => if k + 2 ≤ n then b else if k + 1 = n then a else b with hA
    set B : ℕ → ℝ := fun k => if k + 2 ≤ n then c else if k + 1 = n then b else c with hB
    have hAB : ∀ i ≤ n, A i ≤ B i := by
      intro i _
      simp only [hA, hB]
      split
      · exact le_of_lt hbc
      · split
        · exact le_of_lt hab
        · exact le_of_lt hbc
    have hcovchain : ∀ i < n, Covers f (Set.Icc (A i) (B i)) (Set.Icc (A (i + 1)) (B (i + 1))) := by
      intro i hi
      by_cases h1 : i + 2 ≤ n
      · by_cases h2 : i + 1 + 2 ≤ n
        · simp only [hA, hB, if_pos h1, if_pos h2]; exact cov11
        · have h3 : i + 1 + 1 = n := by omega
          simp only [hA, hB, if_pos h1, if_neg h2, if_pos h3]; exact cov10
      · have h3 : i + 1 = n := by omega
        have h4 : ¬ (i + 1 + 2 ≤ n) := by omega
        have h5 : ¬ (i + 1 + 1 = n) := by omega
        simp only [hA, hB, if_neg h1, if_pos h3, if_neg h4, if_neg h5]; exact cov01
    have hla : A n = A 0 := by
      have h1 : ¬ (n + 2 ≤ n) := by omega
      have h2 : ¬ (n + 1 = n) := by omega
      have h3 : 0 + 2 ≤ n := by omega
      simp only [hA, if_neg h1, if_neg h2, if_pos h3]
    have hlb : B n = B 0 := by
      have h1 : ¬ (n + 2 ≤ n) := by omega
      have h2 : ¬ (n + 1 = n) := by omega
      have h3 : 0 + 2 ≤ n := by omega
      simp only [hB, if_neg h1, if_neg h2, if_pos h3]
    obtain ⟨x, hfix, hmem⟩ := loop_periodic f hf n A B hAB hcovchain hla hlb
    refine ⟨x, hn, hfix, ?_⟩
    intro m hm hmn hcon
    obtain ⟨r, hrm, hstep⟩ : ∃ r, r < m ∧ f^[n - 1] x = f^[r] x :=
      ⟨(n - 1) % m, Nat.mod_lt _ hm, iterate_mod hm hcon (n - 1)⟩
    have hrn : r + 2 ≤ n := by omega
    have hmem1 : f^[n - 1] x ∈ Set.Icc (A (n - 1)) (B (n - 1)) := hmem (n - 1) (by omega)
    have hmemr : f^[r] x ∈ Set.Icc (A r) (B r) := hmem r (by omega)
    have hne1 : ¬ ((n - 1) + 2 ≤ n) := by omega
    have heq1 : (n - 1) + 1 = n := by omega
    have hA1a : A (n - 1) = a := by simp only [hA, if_neg hne1, if_pos heq1]
    have hA1b : B (n - 1) = b := by simp only [hB, if_neg hne1, if_pos heq1]
    have hAra : A r = b := by simp only [hA, if_pos hrn]
    have hArb : B r = c := by simp only [hB, if_pos hrn]
    rw [hA1a, hA1b] at hmem1
    rw [hAra, hArb] at hmemr
    rw [hstep] at hmem1
    have hbval : f^[r] x = b := le_antisymm hmem1.2 hmemr.1
    have hxc : x = c := by
      have hlast : f^[n] x = f (f^[n - 1] x) := by
        conv_lhs => rw [show n = n - 1 + 1 by omega]
        rw [Function.iterate_succ_apply']
      rw [hfix, hstep, hbval, hb] at hlast
      exact hlast
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hr0 : r = 0 := by omega
      rw [hr0] at hbval
      simp only [Function.iterate_zero_apply] at hbval
      rw [hxc] at hbval
      linarith
    · have h1le : 1 + 2 ≤ n := by omega
      have hmemone : f^[1] x ∈ Set.Icc (A 1) (B 1) := hmem 1 (by omega)
      have hA1' : A 1 = b := by simp only [hA, if_pos h1le]
      rw [hA1'] at hmemone
      have hge : b ≤ f x := by simpa using hmemone.1
      rw [hxc, hc] at hge
      linarith


/-- The reversed three-cycle case, obtained from the oriented one by reflecting the line. -/
theorem periods_of_cycle' (f : ℝ → ℝ) (hf : Continuous f) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (ha : f a = c) (hb : f b = a) (hc : f c = b)
    (n : ℕ) (hn : 0 < n) : ∃ x, HasPrimePeriod f x n := by
  set g : ℝ → ℝ := fun x => -f (-x) with hg
  have hgc : Continuous g := (hf.comp continuous_neg).neg
  have hiter : ∀ (k : ℕ) (y : ℝ), g^[k] y = -f^[k] (-y) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
      simp [hg]
  obtain ⟨y, -, hyfix, hylt⟩ := periods_of_cycle g hgc (a := -c) (b := -b) (c := -a)
    (by linarith) (by linarith) (by simp [hg, hc]) (by simp [hg, hb]) (by simp [hg, ha]) n hn
  refine ⟨-y, hn, ?_, ?_⟩
  · rw [hiter] at hyfix
    linarith [hyfix]
  · intro m hm hmn hcon
    have hne := hylt m hm hmn
    rw [hiter] at hne
    apply hne
    rw [hcon]
    ring

/-- Theorem 10.1 (Li–Yorke): period three implies every period. -/
theorem period_three_implies_all_periods (f : ℝ → ℝ) (hf : Continuous f)
    (h3 : ∃ x, HasPrimePeriod f x 3) (n : ℕ) (hn : 0 < n) :
    ∃ x, HasPrimePeriod f x n := by
  obtain ⟨z, -, hz3, hzlt⟩ := h3
  have e1 : f (f (f z)) = z := by
    have := hz3
    simp only [show (3:ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
      show (2:ℕ) = 1 + 1 from rfl, Function.iterate_one] at this
    exact this
  have n1 : z ≠ f z := by
    have h := hzlt 1 (by omega) (by omega)
    simpa [eq_comm] using h
  have n2 : z ≠ f (f z) := by
    have h := hzlt 2 (by omega) (by omega)
    simp only [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_one] at h
    exact fun hc => h hc.symm
  have n3 : f z ≠ f (f z) := by
    intro h
    have h2 : f (f z) = f (f (f z)) := congrArg f h
    rw [e1] at h2
    exact n2 h2.symm
  rcases lt_trichotomy z (f z) with h01 | h01 | h01
  · rcases lt_trichotomy (f z) (f (f z)) with h12 | h12 | h12
    · exact periods_of_cycle f hf h01 h12 rfl rfl e1 n hn
    · exact absurd h12 n3
    · rcases lt_trichotomy z (f (f z)) with h02 | h02 | h02
      · exact periods_of_cycle' f hf h02 h12 rfl e1 rfl n hn
      · exact absurd h02 n2
      · exact periods_of_cycle f hf h02 h01 e1 rfl rfl n hn
  · exact absurd h01 n1
  · rcases lt_trichotomy (f z) (f (f z)) with h12 | h12 | h12
    · rcases lt_trichotomy z (f (f z)) with h02 | h02 | h02
      · exact periods_of_cycle' f hf h01 h02 rfl rfl e1 n hn
      · exact absurd h02 n2
      · exact periods_of_cycle f hf h12 h02 rfl e1 rfl n hn
    · exact absurd h12 n3
    · exact periods_of_cycle' f hf h12 h01 e1 rfl rfl n hn

end Sark

open Devaney in
theorem solution (f : ℝ → ℝ) (hf : Continuous f)
    (h3 : ∃ x, HasPrimePeriod f x 3) (n : ℕ) (hn : 0 < n) :
    ∃ x, HasPrimePeriod f x n :=
  Sark.period_three_implies_all_periods f hf h3 n hn
