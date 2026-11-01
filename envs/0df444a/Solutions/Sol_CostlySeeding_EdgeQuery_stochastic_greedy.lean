-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.stochastic_greedy
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:03:52.969936+00:00
-- url     : https://prove2.me/submissions/9473fb0f-4504-4caa-af99-0ca4a3fe56ce

import Theorems.Thm_CostlySeeding_EdgeQuery_submodular

open CostlySeeding.EdgeQuery

namespace SGAux

lemma Y_nonneg {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n) (S : Finset (Fin n)) :
    0 ≤ Y E v S := by
  unfold Y; split_ifs <;> norm_num

lemma GamCut_nonneg {n T : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (V : Finset (Fin n)) (r : ℝ) (hr : 0 < r) (tau : ℕ) (ss : Fin T → ProbeSeed n)
    (S : Finset (Fin n)) : 0 ≤ GamCut G V r tau ss S := by
  unfold GamCut
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => Y_nonneg _ _ _

lemma OPTof_exists {n : ℕ} (f : Finset (Fin n) → ℝ) (k : ℕ) (hkn : k ≤ n) :
    ∃ S : Finset (Fin n), S.card = k ∧ OPTof f k = f S := by
  have hne : ((Finset.univ : Finset (Fin n)).powersetCard k).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simpa using hkn)
  obtain ⟨S, hS, hEq⟩ := Finset.exists_mem_eq_sup' hne f
  refine ⟨S, (Finset.mem_powersetCard.1 hS).2, ?_⟩
  unfold OPTof
  rw [dif_pos hne, hEq]


lemma choices_nonempty {n : ℕ} (k : ℕ) (eps : ℝ) (L : Finset (Fin n)) :
    0 < (((Finset.univ : Finset (Fin n)) \ L).powersetCard (seedSampleSize n k eps L)).card := by
  rw [Finset.card_pos]
  apply Finset.powersetCard_nonempty.2
  unfold seedSampleSize
  exact min_le_right _ _

lemma subset_bestSeed {n : ℕ} (f : Finset (Fin n) → ℝ) (L R : Finset (Fin n)) :
    L ⊆ bestSeed f L R := by
  unfold bestSeed
  split
  · exact Finset.subset_insert _ _
  · exact le_refl _

lemma gain_le_best {n : ℕ} (f : Finset (Fin n) → ℝ) (L R : Finset (Fin n)) (r : Fin n)
    (hr : r ∈ R) : f (insert r L) - f L ≤ f (bestSeed f L R) - f L := by
  unfold bestSeed
  rcases h : (R.sort (· ≤ ·)).argmax (fun v => f (insert v L) - f L) with _ | v
  · exfalso
    rw [List.argmax_eq_none] at h
    have : r ∈ R.sort (· ≤ ·) := (Finset.mem_sort _).2 hr
    rw [h] at this
    simp at this
  · simp only
    exact List.le_of_mem_argmax ((Finset.mem_sort _).2 hr) h

/-! ### Submodularity -/

lemma sum_gain_ge {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : SubmodularSet f)
    (L A : Finset (Fin n)) (hA : Disjoint A L) :
    f (L ∪ A) - f L ≤ ∑ a ∈ A, (f (insert a L) - f L) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A haA ih =>
    have hdisj : Disjoint A L := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hA
    have haL : a ∉ L := Finset.disjoint_left.1 hA (Finset.mem_insert_self _ _)
    have h1 := ih hdisj
    have hs := hsub (L ∪ A) (insert a L)
    have e1 : L ∪ A ∪ insert a L = L ∪ insert a A := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have e2 : (L ∪ A) ∩ insert a L = L := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨h | h, h' | h'⟩
        · exact h
        · exact h
        · subst h'; exact absurd h haA
        · exact absurd h' (Finset.disjoint_left.1 hdisj h)
      · intro h; exact ⟨Or.inl h, Or.inr h⟩
    rw [e1, e2] at hs
    rw [Finset.sum_insert haA]
    linarith

/-! ### Counting -/

lemma descFactorial_ratio (a t : ℕ) : ∀ m : ℕ,
    a.descFactorial m * (a + t) ^ m ≤ (a + t).descFactorial m * a ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := descFactorial_ratio a t m
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have key : (a - m) * (a + t) ≤ (a + t - m) * a := by
      rcases le_or_gt m a with h | h
      · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
        have e1 : m + b - m = b := by omega
        have e2 : m + b + t - m = b + t := by omega
        rw [e1, e2]; nlinarith
      · have : a - m = 0 := by omega
        rw [this]; simp
    calc (a - m) * a.descFactorial m * ((a + t) ^ m * (a + t))
        = (a.descFactorial m * (a + t) ^ m) * ((a - m) * (a + t)) := by ring
      _ ≤ ((a + t).descFactorial m * a ^ m) * ((a + t - m) * a) :=
          Nat.mul_le_mul ih key
      _ = (a + t - m) * (a + t).descFactorial m * (a ^ m * a) := by ring

lemma choose_ratio (a t m : ℕ) :
    ((a.choose m : ℕ) : ℝ) * ((a + t : ℕ) : ℝ) ^ m ≤ (((a + t).choose m : ℕ) : ℝ) * (a : ℝ) ^ m := by
  have h := descFactorial_ratio a t m
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h
  have h2 : a.choose m * (a + t) ^ m ≤ (a + t).choose m * a ^ m := by
    have hf : 0 < m.factorial := Nat.factorial_pos m
    have : m.factorial * (a.choose m * (a + t) ^ m) ≤ m.factorial * ((a + t).choose m * a ^ m) := by
      calc _ = m.factorial * a.choose m * (a + t) ^ m := by ring
        _ ≤ m.factorial * (a + t).choose m * a ^ m := h
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hf
  exact_mod_cast h2

lemma convex_bound (eps x : ℝ) (heps : 0 < eps) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (x * Real.log eps) ≤ 1 - (1 - eps) * x := by
  have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (Real.log eps))
    (by linarith : 0 ≤ 1 - x) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
    Real.exp_log heps] at this
  linarith

lemma miss_count {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (L A : Finset (Fin n)) (hAU : A ⊆ (Finset.univ : Finset (Fin n)) \ L)
    (ht1 : 1 ≤ A.card) (htk : A.card ≤ k) :
    ((((Finset.univ : Finset (Fin n)) \ L).powersetCard (seedSampleSize n k eps L)).filter
        (fun R => Disjoint R A)).card ≤
      ((((Finset.univ : Finset (Fin n)) \ L).powersetCard (seedSampleSize n k eps L)).card : ℝ) *
        (1 - (1 - eps) * A.card / k) := by
  set U := (Finset.univ : Finset (Fin n)) \ L with hU
  set m := seedSampleSize n k eps L with hm
  set t := A.card with ht
  have hfilter : (U.powersetCard m).filter (fun R => Disjoint R A) = (U \ A).powersetCard m := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_sdiff]
    tauto
  rw [hfilter, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hAU]
  set u := U.card with hu
  have htu : t ≤ u := Finset.card_le_card hAU
  obtain ⟨a, ha⟩ : ∃ a, u = a + t := ⟨u - t, by omega⟩
  have hsub : u - t = a := by omega
  rw [hsub, ha]
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have htkR : (t : ℝ) ≤ k := by exact_mod_cast htk
  have hrhs0 : 0 ≤ 1 - (1 - eps) * t / k := by
    rw [sub_nonneg, div_le_one hkR]
    nlinarith
  have hratio := choose_ratio a t m
  have hupos : (0 : ℝ) < ((a + t : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + t)
  have hun : u ≤ n := by
    rw [hu, hU]; exact (Finset.card_le_univ _).trans (by simp)
  -- Case analysis on the sample size
  by_cases hcap : Nat.ceil ((n : ℝ) / (k : ℝ) * Real.log (1 / eps)) ≤ u
  · have hmx : m = Nat.ceil ((n : ℝ) / (k : ℝ) * Real.log (1 / eps)) := by
      rw [hm]; unfold seedSampleSize; rw [← hU, ← hu]; exact min_eq_left hcap
    have hmge : (n : ℝ) / (k : ℝ) * Real.log (1 / eps) ≤ m := by rw [hmx]; exact Nat.le_ceil _
    -- C(a,m) ≤ C(a+t,m) (a/(a+t))^m
    have h1 : ((a.choose m : ℕ) : ℝ) ≤ (((a + t).choose m : ℕ) : ℝ) * ((a : ℝ) / (a + t : ℕ)) ^ m := by
      rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hupos m)]
      exact hratio
    have h2 : ((a : ℝ) / (a + t : ℕ)) ^ m ≤ Real.exp (-(t : ℝ) * m / (a + t : ℕ)) := by
      have hb : (a : ℝ) / (a + t : ℕ) ≤ Real.exp (-(t : ℝ) / (a + t : ℕ)) := by
        have := Real.add_one_le_exp (-(t : ℝ) / (a + t : ℕ))
        have e : (a : ℝ) / (a + t : ℕ) = -(t : ℝ) / (a + t : ℕ) + 1 := by
          field_simp; push_cast; ring
        linarith
      calc ((a : ℝ) / (a + t : ℕ)) ^ m ≤ (Real.exp (-(t : ℝ) / (a + t : ℕ))) ^ m :=
            pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hb m
        _ = Real.exp (-(t : ℝ) * m / (a + t : ℕ)) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 : Real.exp (-(t : ℝ) * m / (a + t : ℕ)) ≤ Real.exp ((t / k : ℝ) * Real.log eps) := by
      apply Real.exp_le_exp.2
      have hn : ((a + t : ℕ) : ℝ) ≤ n := by exact_mod_cast (ha ▸ hun)
      have hlog : Real.log (1 / eps) = -Real.log eps := by rw [one_div, Real.log_inv]
      have hle : 0 < -Real.log eps := by have := Real.log_neg heps heps1; linarith
      -- t m /(a+t) ≥ t m / n ≥ (t/k) * log(1/eps)
      have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hupos hn
      have e1 : (t : ℝ) * m / (a + t : ℕ) ≥ (t : ℝ) * m / n := by
        apply div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hupos hn
      have e2 : (t : ℝ) * m / n ≥ (t / k : ℝ) * (-Real.log eps) := by
        rw [ge_iff_le, le_div_iff₀ hnpos]
        rw [hlog] at hmge
        have : (t : ℝ) * ((n : ℝ) / (k : ℝ) * -Real.log eps) ≤ t * m :=
          mul_le_mul_of_nonneg_left hmge (Nat.cast_nonneg _)
        calc (t / k : ℝ) * (-Real.log eps) * n = (t : ℝ) * ((n : ℝ) / (k : ℝ) * -Real.log eps) := by
              field_simp
          _ ≤ _ := this
      have : -(t : ℝ) * m / (a + t : ℕ) = -((t : ℝ) * m / (a + t : ℕ)) := by ring
      rw [this]
      nlinarith
    have h4 := convex_bound eps (t / k) heps (div_nonneg (Nat.cast_nonneg _) hkR.le) (by rw [div_le_one hkR]; exact htkR)
    have hC0 : (0 : ℝ) ≤ (((a + t).choose m : ℕ) : ℝ) := by positivity
    calc ((a.choose m : ℕ) : ℝ) ≤ (((a + t).choose m : ℕ) : ℝ) * ((a : ℝ) / (a + t : ℕ)) ^ m := h1
      _ ≤ (((a + t).choose m : ℕ) : ℝ) * (1 - (1 - eps) * t / k) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          calc _ ≤ _ := h2
            _ ≤ _ := h3
            _ ≤ 1 - (1 - eps) * (t / k) := h4
            _ = _ := by ring
  · have hmx : m = u := by
      rw [hm]; unfold seedSampleSize; rw [← hU, ← hu]; exact min_eq_right (by omega)
    rw [hmx, ha, Nat.choose_eq_zero_of_lt (by omega : a < a + t)]
    simp only [Nat.cast_zero]
    positivity

lemma weight_symm {n : ℕ} (U A : Finset (Fin n)) (hAU : A ⊆ U) (m : ℕ) (a a' : Fin n)
    (ha : a ∈ A) (ha' : a' ∈ A) :
    ∑ R ∈ U.powersetCard m, (if a ∈ R then 1 / ((R ∩ A).card : ℝ) else 0) =
      ∑ R ∈ U.powersetCard m, (if a' ∈ R then 1 / ((R ∩ A).card : ℝ) else 0) := by
  set σ : Equiv.Perm (Fin n) := Equiv.swap a a' with hσ
  have hσσ : ∀ x, σ (σ x) = x := fun x => Equiv.swap_apply_self a a' x
  have hσU : ∀ x ∈ U, σ x ∈ U := by
    intro x hx
    rw [hσ, Equiv.swap_apply_def]
    split_ifs
    · exact hAU ha'
    · exact hAU ha
    · exact hx
  have hσA : ∀ x, σ x ∈ A ↔ x ∈ A := by
    intro x
    rw [hσ, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; simp [ha, ha']
    · subst h2; simp [ha, ha']
    · rfl
  have hmap : ∀ R : Finset (Fin n), ((R.map σ.toEmbedding) ∩ A).card = (R ∩ A).card := by
    intro R
    have : (R.map σ.toEmbedding) ∩ A = (R ∩ A).map σ.toEmbedding := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_map_equiv]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := (hσA (σ.symm x)).1
        rw [show σ (σ.symm x) = x by simp] at this
        exact this h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := (hσA (σ.symm x)).2 h2
        rwa [show σ (σ.symm x) = x by simp] at this
    rw [this, Finset.card_map]
  apply Finset.sum_nbij' (fun R => R.map σ.toEmbedding) (fun R => R.map σ.toEmbedding)
  · intro R hR
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hR ⊢
    refine ⟨?_, by rw [Finset.card_map]; exact hR.2⟩
    intro x hx
    rw [Finset.mem_map_equiv] at hx
    have := hσU _ (hR.1 hx)
    rwa [show σ (σ.symm x) = x by simp] at this
  · intro R hR
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hR ⊢
    refine ⟨?_, by rw [Finset.card_map]; exact hR.2⟩
    intro x hx
    rw [Finset.mem_map_equiv] at hx
    have := hσU _ (hR.1 hx)
    rwa [show σ (σ.symm x) = x by simp] at this
  · intro R _
    ext x; simp [Finset.mem_map_equiv, hσ]
  · intro R _
    ext x; simp [Finset.mem_map_equiv, hσ]
  · intro R _
    have hmem : a' ∈ R.map σ.toEmbedding ↔ a ∈ R := by
      rw [Finset.mem_map_equiv]
      simp [hσ]
    simp only [hmem, hmap]

/-! ### One step of stochastic greedy -/

lemma one_step {n : ℕ} (f : Finset (Fin n) → ℝ) (hmono : MonotoneSet f) (hsub : SubmodularSet f)
    (k : ℕ) (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (L O : Finset (Fin n)) (hO : O.card ≤ k) :
    f L + ((1 - eps) / k) * (f O - f L) ≤
      ∑ R ∈ ((Finset.univ : Finset (Fin n)) \ L).powersetCard (seedSampleSize n k eps L),
        (1 / ((((Finset.univ : Finset (Fin n)) \ L).powersetCard
          (seedSampleSize n k eps L)).card : ℝ)) * f (bestSeed f L R) := by
  set U := (Finset.univ : Finset (Fin n)) \ L with hU
  set m := seedSampleSize n k eps L with hm
  set C := U.powersetCard m with hC
  set A := O \ L with hA
  set g : Fin n → ℝ := fun v => f (insert v L) - f L with hg
  have hcpos : (0 : ℝ) < C.card := by exact_mod_cast choices_nonempty k eps L
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hG : ∀ R, 0 ≤ f (bestSeed f L R) - f L := fun R => by
    have := hmono _ _ (subset_bestSeed f L R); linarith
  have hg0 : ∀ v, 0 ≤ g v := fun v => by
    have := hmono _ _ (Finset.subset_insert v L); simp only [hg]; linarith
  have hAU : A ⊆ U := by
    intro x hx; rw [hA, Finset.mem_sdiff] at hx; rw [hU, Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, hx.2⟩
  have hAk : A.card ≤ k := (Finset.card_le_card Finset.sdiff_subset).trans hO
  -- rewrite the right-hand side as f L plus an average gain
  have hrhs : ∑ R ∈ C, (1 / (C.card : ℝ)) * f (bestSeed f L R) =
      f L + (1 / (C.card : ℝ)) * ∑ R ∈ C, (f (bestSeed f L R) - f L) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
    ring
  rw [hrhs]
  have hfo : f O - f L ≤ ∑ a ∈ A, g a := by
    have h1 : f O ≤ f (L ∪ A) := hmono _ _ (by
      intro x hx
      by_cases hxL : x ∈ L
      · exact Finset.mem_union_left _ hxL
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hx, hxL⟩))
    have h2 := sum_gain_ge f hsub L A Finset.sdiff_disjoint
    simp only [hg]; linarith
  have hcoef : 0 ≤ (1 - eps) / k := div_nonneg (by linarith) hkR.le
  suffices hmain : (1 - eps) / k * ∑ a ∈ A, g a ≤
      (1 / (C.card : ℝ)) * ∑ R ∈ C, (f (bestSeed f L R) - f L) by
    have := mul_le_mul_of_nonneg_left hfo hcoef
    linarith
  have hGsum : 0 ≤ ∑ R ∈ C, (f (bestSeed f L R) - f L) := Finset.sum_nonneg fun R _ => hG R
  rcases Nat.eq_zero_or_pos A.card with ht | ht
  · rw [Finset.card_eq_zero.1 ht, Finset.sum_empty, mul_zero]
    exact mul_nonneg (by positivity) hGsum
  obtain ⟨a0, ha0⟩ := Finset.card_pos.1 ht
  set t := A.card with htdef
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  set w : Fin n → ℝ := fun a => ∑ R ∈ C, (if a ∈ R then 1 / ((R ∩ A).card : ℝ) else 0) with hw
  -- each sampled set's gain dominates the average gain over its hits in A
  have key1 : ∀ R ∈ C, (1 / ((R ∩ A).card : ℝ)) * ∑ a ∈ R ∩ A, g a ≤
      f (bestSeed f L R) - f L := by
    intro R _
    rcases Nat.eq_zero_or_pos (R ∩ A).card with h0 | hpos
    · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty, mul_zero]; exact hG R
    · have hle : ∑ a ∈ R ∩ A, g a ≤ ∑ _a ∈ R ∩ A, (f (bestSeed f L R) - f L) :=
        Finset.sum_le_sum fun a ha => gain_le_best f L R a (Finset.mem_inter.1 ha).1
      rw [Finset.sum_const, nsmul_eq_mul] at hle
      have hp : (0 : ℝ) < (R ∩ A).card := by exact_mod_cast hpos
      rw [one_div, inv_mul_le_iff₀ hp]
      exact hle
  have hswap : ∑ R ∈ C, (1 / ((R ∩ A).card : ℝ)) * ∑ a ∈ R ∩ A, g a =
      ∑ a ∈ A, g a * w a := by
    have : ∀ R ∈ C, (1 / ((R ∩ A).card : ℝ)) * ∑ a ∈ R ∩ A, g a =
        ∑ a ∈ A, g a * (if a ∈ R then 1 / ((R ∩ A).card : ℝ) else 0) := by
      intro R _
      rw [Finset.mul_sum]
      rw [show R ∩ A = A.filter (fun a => a ∈ R) by
        ext x; simp [Finset.mem_filter, and_comm]]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [hw, Finset.mul_sum]
  have hwconst : ∀ a ∈ A, w a = w a0 := by
    intro a ha
    exact weight_symm U A hAU m a a0 ha ha0
  -- total weight equals the number of sampled sets hitting A
  set D := (C.filter (fun R => Disjoint R A)).card with hD
  have hwtot : ∑ a ∈ A, w a = C.card - D := by
    rw [hw, Finset.sum_comm]
    have : ∀ R ∈ C, ∑ a ∈ A, (if a ∈ R then 1 / ((R ∩ A).card : ℝ) else 0) =
        1 - (if Disjoint R A then 1 else 0) := by
      intro R _
      rw [← Finset.sum_filter]
      rw [show A.filter (fun a => a ∈ R) = R ∩ A by
        ext x; simp [Finset.mem_filter, and_comm]]
      rw [Finset.sum_const, nsmul_eq_mul]
      by_cases hd : Disjoint R A
      · rw [Finset.disjoint_iff_inter_eq_empty.1 hd]; simp [hd]
      · have hne : (R ∩ A).card ≠ 0 := by
          intro h0; exact hd (Finset.disjoint_iff_inter_eq_empty.2 (Finset.card_eq_zero.1 h0))
        rw [if_neg hd, mul_one_div_cancel (by exact_mod_cast hne)]
        ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.sum_boole]
  have hw0 : w a0 = (C.card - D) / t := by
    rw [← hwtot, Finset.sum_congr rfl hwconst, Finset.sum_const, nsmul_eq_mul, ← htdef]
    field_simp
  have hmiss := miss_count k hk eps heps heps1 L A hAU ht hAk
  rw [← hU, ← hm, ← hC, ← hD] at hmiss
  have hsum1 : w a0 * ∑ a ∈ A, g a ≤ ∑ R ∈ C, (f (bestSeed f L R) - f L) := by
    calc w a0 * ∑ a ∈ A, g a = ∑ a ∈ A, g a * w a := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; rw [hwconst a ha]; ring
      _ = _ := hswap.symm
      _ ≤ _ := Finset.sum_le_sum key1
  have hgsum : 0 ≤ ∑ a ∈ A, g a := Finset.sum_nonneg fun a _ => hg0 a
  -- (1-eps)/k ≤ w a0 / |C|
  have hfrac : (1 - eps) / k ≤ (1 / (C.card : ℝ)) * w a0 := by
    rw [hw0]
    rw [show (1 / (C.card : ℝ)) * ((C.card - D) / t) = (C.card - D) / (C.card * t) by
      field_simp]
    rw [le_div_iff₀ (mul_pos hcpos htR)]
    have : (C.card : ℝ) * (1 - (1 - eps) * t / k) = C.card - (1 - eps) / k * (C.card * t) := by
      field_simp
    linarith
  calc (1 - eps) / k * ∑ a ∈ A, g a ≤ ((1 / (C.card : ℝ)) * w a0) * ∑ a ∈ A, g a :=
        mul_le_mul_of_nonneg_right hfrac hgsum
    _ = (1 / (C.card : ℝ)) * (w a0 * ∑ a ∈ A, g a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum1 (by positivity)

/-! ### Iterating the step -/

lemma beta_pow_le (k : ℕ) (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    (1 - (1 - eps) / k) ^ k ≤ Real.exp (-1) + eps := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb0 : 0 ≤ 1 - (1 - eps) / k := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h1 : 1 - (1 - eps) / k ≤ Real.exp (-((1 - eps) / k)) := by
    have := Real.add_one_le_exp (-((1 - eps) / k)); linarith
  have h2 : (1 - (1 - eps) / k) ^ k ≤ Real.exp (-(1 - eps)) := by
    calc _ ≤ (Real.exp (-((1 - eps) / k))) ^ k := pow_le_pow_left₀ hb0 h1 k
      _ = Real.exp (-(1 - eps)) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : Real.exp eps ≤ 1 + eps * Real.exp 1 := by
    have a1 := Real.add_one_le_exp (-eps)
    have a2 : Real.exp (-eps) * Real.exp eps = 1 := by rw [← Real.exp_add]; simp
    have a3 : Real.exp eps ≤ Real.exp 1 := Real.exp_le_exp.2 heps1.le
    have a4 : 0 < Real.exp eps := Real.exp_pos _
    nlinarith
  have h4 : Real.exp (-(1 - eps)) = Real.exp (-1) * Real.exp eps := by
    rw [← Real.exp_add]; ring_nf
  have h5 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have h6 : 0 < Real.exp (-1) := Real.exp_pos _
  have : Real.exp (-1) * Real.exp eps ≤ Real.exp (-1) * (1 + eps * Real.exp 1) :=
    mul_le_mul_of_nonneg_left h3 h6.le
  nlinarith

lemma greedy_general {n : ℕ} (f : Finset (Fin n) → ℝ) (hmono : MonotoneSet f)
    (hsub : SubmodularSet f) (hf0 : 0 ≤ f ∅) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    (1 - Real.exp (-1) - eps) * OPTof f k ≤ seedExpectation f eps k f := by
  obtain ⟨O, hO, hOeq⟩ := OPTof_exists f k hkn
  rw [hOeq]
  set β := 1 - (1 - eps) / k with hβ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb0 : 0 ≤ β := by
    rw [hβ, sub_nonneg, div_le_one (by linarith)]; linarith
  let Vf : ℕ → Finset (Fin n) → ℝ := fun j L =>
    ∑ A : Finset (Fin n), seedProb f eps k j L A * f A
  have hV0 : ∀ L, Vf 0 L = f L := by
    intro L
    simp only [Vf, seedProb]
    rw [Finset.sum_eq_single L]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; simp
    · intro h; exact absurd (Finset.mem_univ L) h
  have hVs : ∀ j L, Vf (j + 1) L =
      ∑ R ∈ ((Finset.univ : Finset (Fin n)) \ L).powersetCard (seedSampleSize n k eps L),
        (1 / ((((Finset.univ : Finset (Fin n)) \ L).powersetCard
          (seedSampleSize n k eps L)).card : ℝ)) * Vf j (bestSeed f L R) := by
    intro j L
    simp only [Vf, seedProb]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro R _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring
  have hclaim : ∀ j L, f O - Vf j L ≤ β ^ j * (f O - f L) := by
    intro j
    induction j with
    | zero => intro L; rw [hV0]; simp
    | succ j ih =>
      intro L
      rw [hVs]
      set C := ((Finset.univ : Finset (Fin n)) \ L).powersetCard (seedSampleSize n k eps L)
        with hC
      have hcpos : (0 : ℝ) < C.card := by exact_mod_cast choices_nonempty k eps L
      have hsum1 : ∑ R ∈ C, (1 / (C.card : ℝ)) = 1 := by
        rw [Finset.sum_const, nsmul_eq_mul]; field_simp
      have hstep := one_step f hmono hsub k hk eps heps heps1 L O hO.le
      rw [← hC] at hstep
      have hbj : 0 ≤ β ^ j := pow_nonneg hb0 j
      -- lower bound each term by the induction hypothesis
      have hlow : ∑ R ∈ C, (1 / (C.card : ℝ)) * (f O - β ^ j * (f O - f (bestSeed f L R))) ≤
          ∑ R ∈ C, (1 / (C.card : ℝ)) * Vf j (bestSeed f L R) := by
        apply Finset.sum_le_sum
        intro R _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := ih (bestSeed f L R); linarith
      have hexpand : ∑ R ∈ C, (1 / (C.card : ℝ)) * (f O - β ^ j * (f O - f (bestSeed f L R))) =
          f O - β ^ j * (f O - ∑ R ∈ C, (1 / (C.card : ℝ)) * f (bestSeed f L R)) := by
        have : ∀ R ∈ C, (1 / (C.card : ℝ)) * (f O - β ^ j * (f O - f (bestSeed f L R))) =
            (1 - β ^ j) * f O * (1 / (C.card : ℝ)) +
              β ^ j * ((1 / (C.card : ℝ)) * f (bestSeed f L R)) := by
          intro R _; ring
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hsum1]
        ring
      rw [hexpand] at hlow
      have hβstep : f O - ∑ R ∈ C, (1 / (C.card : ℝ)) * f (bestSeed f L R) ≤ β * (f O - f L) := by
        rw [hβ]; linarith
      have := mul_le_mul_of_nonneg_left hβstep hbj
      rw [pow_succ]
      nlinarith
  have hfin := hclaim k ∅
  have hOPT0 : 0 ≤ f O := le_trans hf0 (hmono _ _ (Finset.empty_subset _))
  have hbk : β ^ k ≤ Real.exp (-1) + eps := beta_pow_le k hk eps heps heps1
  have hbk0 : 0 ≤ β ^ k := pow_nonneg hb0 k
  have hE : seedExpectation f eps k f = Vf k ∅ := rfl
  rw [hE]
  have : β ^ k * (f O - f ∅) ≤ β ^ k * f O := by nlinarith
  nlinarith

end SGAux

theorem solution (n k T tau : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hT : 0 < T) (htau : 0 < tau)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (rho eps : ℝ)
    (hrho : 0 < rho) (heps : 0 < eps) (heps1 : eps < 1)
    (ss : Fin T → ProbeSeed n) :
    (1 - Real.exp (-1) - eps) * OPTof (GamCut G Vrho rho tau ss) k ≤
      seedExpectation (GamCut G Vrho rho tau ss) eps k
        (GamCut G Vrho rho tau ss) := by
  obtain ⟨hmono, hsub⟩ := submodular n T tau hT htau G Vrho rho hrho ss
  exact SGAux.greedy_general _ hmono hsub (SGAux.GamCut_nonneg G Vrho rho hrho tau ss ∅)
    k hk hkn eps heps heps1

