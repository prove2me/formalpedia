-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:13.714949+00:00
-- url     : https://prove2.me/submissions/944b4ba0-b6f4-476b-bcf3-01b888efe2e9

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Theorem 7, p. 41: with Leximin-Leontief preferences, NASH is group-strategyproof. -/
theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (g : Mechanism n m) (hg : ∀ P, IsNashOutcome P (g P).1) :
    IsLexGroupSP g := by
      classical
      have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
      have u_le : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (j : Fin m), 0 < p.1 j →
          leontief p q ≤ q j / p.1 j := by
        intro p q j hj
        unfold leontief
        exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have le_u : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (c : ℝ),
          (∀ j, 0 < p.1 j → c ≤ q j / p.1 j) → c ≤ leontief p q := by
        intro p q c h
        unfold leontief
        rw [Finset.le_inf'_iff]
        intro j hj
        exact h j (Finset.mem_filter.mp hj).2
      have mem_crit : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (j : Fin m),
          j ∈ crit p q ↔ 0 < p.1 j ∧ q j / p.1 j = leontief p q := by
        intro p q j
        simp [crit, Finset.mem_filter]
      have nash_pos : ∀ (P : Profile n m) (q : Fin m → ℝ), IsNashOutcome P q →
          0 < nashProduct P q := by
        intro P q hq
        have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
        have hU : (fun _ : Fin m => (1:ℝ)/m) ∈ stdSimplex ℝ (Fin m) := by
          refine ⟨fun _ => by positivity, ?_⟩
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
        refine lt_of_lt_of_le ?_ (hq.2 _ hU)
        unfold nashProduct
        apply Finset.prod_pos
        intro i _
        unfold leontief
        rw [Finset.lt_inf'_iff]
        intro j hj
        have := (Finset.mem_filter.mp hj).2
        positivity
      -- Hall-type lemma
      have H : ∀ (P : Profile n m) (q : Fin m → ℝ), IsNashOutcome P q →
          ∀ (A : Finset (Fin n)) (X : Finset (Fin m)), (∀ i ∈ A, crit (P i) q ⊆ X) →
          (A.card : ℝ) / n ≤ ∑ j ∈ X, q j := by
        intro P q hq A X hAX
        by_contra hlt
        push_neg at hlt
        set lam := ∑ j ∈ X, q j with hlam
        have hq0 : ∀ j, 0 ≤ q j := hq.1.1
        have hqs : ∑ j, q j = 1 := hq.1.2
        have lam0 : 0 ≤ lam := Finset.sum_nonneg (fun j _ => hq0 j)
        have hA : (A.card : ℝ) ≤ n := by
          have := Finset.card_le_univ A
          rw [Fintype.card_fin] at this
          exact_mod_cast this
        set a : ℝ := (A.card : ℝ) with ha
        have hlt' : n * lam < a := by
          rw [lt_div_iff₀ hn] at hlt; linarith
        have lam1 : lam < 1 := by
          by_contra h1; push_neg at h1; nlinarith
        let x : ℝ → Fin m → ℝ := fun t j => q j * (1 + t * ((if j ∈ X then 1 else 0) - lam))
        have hxS : ∀ t, 0 ≤ t → t ≤ 1 → x t ∈ stdSimplex ℝ (Fin m) := by
          intro t t0 t1
          refine ⟨fun j => ?_, ?_⟩
          · apply mul_nonneg (hq0 j)
            have : 0 ≤ t * (if j ∈ X then (1:ℝ) else 0) := by
              apply mul_nonneg t0; split_ifs <;> norm_num
            nlinarith
          · have e : ∀ j, x t j = q j + t * (if j ∈ X then q j else 0) - t * lam * q j := by
              intro j; simp only [x]; split_ifs <;> ring
            rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib,
              Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqs]
            rw [← Finset.sum_filter]
            have : Finset.univ.filter (fun j => j ∈ X) = X := by ext; simp
            rw [this, ← hlam]; ring
        have hcond : ∀ i j, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), (i ∈ A → 0 < (P i).1 j → j ∉ X →
            leontief (P i) q * (1 + t * (1 - lam)) ≤ q j / (P i).1 j * (1 - t * lam)) := by
          intro i j
          by_cases h : i ∈ A ∧ 0 < (P i).1 j ∧ j ∉ X
          · obtain ⟨hiA, hp, hjX⟩ := h
            set u := leontief (P i) q
            set r := q j / (P i).1 j
            have hur : u ≤ r := u_le _ _ _ hp
            have hne : r ≠ u := by
              intro he
              exact hjX (hAX i hiA ((mem_crit _ _ _).mpr ⟨hp, he⟩))
            have hur' : u < r := lt_of_le_of_ne hur (Ne.symm hne)
            have u0 : 0 ≤ u := le_u _ _ _ (fun k hk => div_nonneg (hq0 k) hk.le)
            have r0 : 0 ≤ r := le_trans u0 hur
            have hpos : 0 < r + u + 1 := by linarith
            have hδ : 0 < (r - u) / (r + u + 1) := div_pos (by linarith) hpos
            filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
            intro _ _ _
            have h1 : t * (r + u + 1) < r - u := (lt_div_iff₀ hpos).mp ht.2
            have t0 : 0 ≤ t := ht.1.le
            nlinarith [mul_nonneg (mul_nonneg t0 u0) lam0,
              mul_nonneg (mul_nonneg t0 r0) (sub_nonneg.mpr lam1.le)]
          · exact Filter.Eventually.of_forall (fun t h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h)
        have hcond' := (Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hcond i)))
        set b : ℝ := n - a with hb
        have b0 : 0 ≤ b := by linarith
        set e : ℝ := a - n * lam with he
        have e0 : 0 < e := by linarith
        set c : ℝ := a * b * lam * (1 - lam) with hc
        have c0 : 0 ≤ c := by
          have : 0 ≤ a := by positivity
          have := sub_nonneg.mpr lam1.le
          positivity
        have hδ0 : 0 < min 1 (min (e / (c + 1)) (1 / (b * lam + 1))) := by
          apply lt_min one_pos
          apply lt_min
          · exact div_pos e0 (by linarith)
          · exact div_pos one_pos (by nlinarith)
        obtain ⟨t, ⟨htI, hct⟩, -⟩ :=
          ((Filter.Eventually.and (Ioo_mem_nhdsGT hδ0) hcond').and self_mem_nhdsWithin).exists
        have t0 : 0 < t := htI.1
        have tδ := htI.2
        have tlt1 : t < 1 := lt_of_lt_of_le tδ (min_le_left _ _)
        have tlt2 : t < e / (c+1) :=
          lt_of_lt_of_le tδ (le_trans (min_le_right _ _) (min_le_left _ _))
        have tlt3 : t < 1 / (b*lam+1) :=
          lt_of_lt_of_le tδ (le_trans (min_le_right _ _) (min_le_right _ _))
        have h2 : t * (c+1) < e := (lt_div_iff₀ (by linarith)).mp tlt2
        have h3 : t * (b*lam+1) < 1 := (lt_div_iff₀ (by nlinarith)).mp tlt3
        have tl0 : 0 ≤ t * (1 - lam) := mul_nonneg t0.le (sub_nonneg.mpr lam1.le)
        have tl1 : t * lam ≤ t := by
          have := mul_le_mul_of_nonneg_left lam1.le t0.le; linarith
        have tl2 : 0 ≤ t * lam := mul_nonneg t0.le lam0
        have α0 : 0 ≤ 1 + t * (1 - lam) := by linarith
        have β0 : 0 ≤ 1 - t * lam := by linarith
        have u0 : ∀ i, 0 ≤ leontief (P i) q :=
          fun i => le_u _ _ _ (fun k hk => div_nonneg (hq0 k) hk.le)
        have hlow : ∀ i, leontief (P i) q * (if i ∈ A then 1 + t * (1 - lam) else 1 - t * lam)
            ≤ leontief (P i) (x t) := by
          intro i
          apply le_u
          intro j hp
          have ex : x t j / (P i).1 j =
              q j / (P i).1 j * (1 + t * ((if j ∈ X then 1 else 0) - lam)) := by
            simp only [x]; ring
          rw [ex]
          have hu := u_le (P i) q j hp
          have r0 : 0 ≤ q j / (P i).1 j := div_nonneg (hq0 j) hp.le
          split_ifs with hiA hjX hjX
          · nlinarith [mul_le_mul_of_nonneg_right hu α0]
          · have := (hct i j) hiA hp hjX
            linarith
          · nlinarith [mul_le_mul_of_nonneg_right hu β0, mul_nonneg r0 t0.le]
          · nlinarith [mul_le_mul_of_nonneg_right hu β0]
        set kB := (Finset.univ.filter (fun i => i ∉ A)).card with hkB
        have hkBr : (kB : ℝ) = b := by
          have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
            (fun i => i ∈ A)
          have hfA : Finset.univ.filter (fun i => i ∈ A) = A := by ext; simp
          rw [hfA, Finset.card_univ, Fintype.card_fin] at h
          have h' : ((A.card + kB : ℕ) : ℝ) = n := by exact_mod_cast h
          push_cast at h'
          rw [hb, ha]; linarith
        have hprod : nashProduct P q * ((1 + t * (1 - lam)) ^ A.card * (1 - t * lam) ^ kB)
            ≤ nashProduct P (x t) := by
          unfold nashProduct
          have : ∏ i, (if i ∈ A then 1 + t * (1 - lam) else 1 - t * lam) =
              (1 + t * (1 - lam)) ^ A.card * (1 - t * lam) ^ kB := by
            rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
            have hfA : Finset.univ.filter (fun i => i ∈ A) = A := by ext; simp
            rw [hfA]
          rw [← this, ← Finset.prod_mul_distrib]
          apply Finset.prod_le_prod
          · intro i _; apply mul_nonneg (u0 i); split_ifs <;> assumption
          · intro i _; exact hlow i
        have hαp : 1 + (A.card : ℝ) * (t * (1 - lam)) ≤ (1 + t * (1 - lam)) ^ A.card :=
          one_add_mul_le_pow (by linarith) _
        have hβp : 1 + (kB : ℝ) * (-(t * lam)) ≤ (1 + -(t * lam)) ^ kB :=
          one_add_mul_le_pow (by linarith) _
        rw [← sub_eq_add_neg, hkBr] at hβp
        rw [← ha] at hαp
        have hbl : 0 ≤ 1 + b * -(t * lam) := by linarith
        have hmul := mul_le_mul hαp hβp hbl (pow_nonneg α0 _)
        have hgt : 1 < (1 + a * (t * (1 - lam))) * (1 + b * -(t * lam)) := by
          have hid : (1 + a * (t * (1 - lam))) * (1 + b * -(t * lam)) = 1 + t * (e - c * t) := by
            rw [he, hc, hb]; ring
          rw [hid]
          have : 0 < e - c * t := by linarith
          have := mul_pos t0 this
          linarith
        have hNp := nash_pos P q hq
        have hle := hq.2 (x t) (hxS t t0.le tlt1.le)
        have := mul_lt_mul_of_pos_left (lt_of_lt_of_le hgt hmul) hNp
        linarith
      have lexlem : ∀ (p : stdSimplex ℝ (Fin m)) (q q' : Fin m → ℝ) (y : Fin m), 0 < p.1 y →
          q' y / p.1 y < leontief p q → LexGt p q q' := by
        intro p q q' y hy hlt
        unfold LexGt
        have mem1 : q' y / p.1 y ∈ ratioList p q' := by
          unfold ratioList
          rw [Multiset.mem_sort, Multiset.mem_map]
          exact ⟨y, Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩), rfl⟩
        have mem2' : q y / p.1 y ∈ ratioList p q := by
          unfold ratioList
          rw [Multiset.mem_sort, Multiset.mem_map]
          exact ⟨y, Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩), rfl⟩
        have mem2 : ∀ b ∈ ratioList p q, leontief p q ≤ b := by
          intro b hb
          unfold ratioList at hb
          rw [Multiset.mem_sort, Multiset.mem_map] at hb
          obtain ⟨k, hk, rfl⟩ := hb
          exact u_le p q k (Finset.mem_filter.mp (Finset.mem_val.mp hk)).2
        have sorted1 : List.Pairwise (· ≤ ·) (ratioList p q') := by
          unfold ratioList; exact Multiset.pairwise_sort _ _
        obtain ⟨b, t2, hb⟩ : ∃ b t2, ratioList p q = b :: t2 := by
          cases h : ratioList p q with
          | nil => rw [h] at mem2'; simp at mem2'
          | cons b t2 => exact ⟨b, t2, rfl⟩
        obtain ⟨a, t1, ha⟩ : ∃ a t1, ratioList p q' = a :: t1 := by
          cases h : ratioList p q' with
          | nil => rw [h] at mem1; simp at mem1
          | cons a t1 => exact ⟨a, t1, rfl⟩
        have hb' : leontief p q ≤ b := mem2 b (by rw [hb]; exact List.mem_cons_self ..)
        have ha' : a ≤ q' y / p.1 y := by
          rw [ha] at sorted1 mem1
          rcases List.mem_cons.mp mem1 with h | h
          · exact le_of_eq h.symm
          · exact List.rel_of_pairwise_cons sorted1 h
        rw [ha, hb]
        apply List.Lex.rel
        show a < b
        linarith
      intro S P P' hP'
      have hN := hg P
      have hN' := hg P'
      by_cases hex : ∃ i ∈ S, LexGt (P i) (g P).1 (g P').1
      · exact Or.inl hex
      right
      push_neg at hex
      have L : ∀ i ∈ S, ∀ y, 0 < (P i).1 y → leontief (P i) (g P).1 ≤ (g P').1 y / (P i).1 y := by
        intro i hi y hy
        by_contra hcon
        push_neg at hcon
        exact hex i hi (lexlem (P i) (g P).1 (g P').1 y hy hcon)
      have Sge : ∀ i ∈ S, leontief (P i) (g P).1 ≤ leontief (P i) (g P').1 :=
        fun i hi => le_u _ _ _ (L i hi)
      set q := g P with hqdef
      set q' := g P' with hq'def
      set D := Finset.univ.filter (fun j => q'.1 j < q.1 j) with hD
      set W := Finset.univ.filter (fun i => leontief (P i) q'.1 < leontief (P i) q.1) with hW
      set Wc := Finset.univ.filter (fun i => ¬ (leontief (P i) q'.1 < leontief (P i) q.1)) with hWc
      set Dc := Finset.univ.filter (fun j => ¬ (q'.1 j < q.1 j)) with hDc
      have H1 := H P q.1 hN Wc Dc (by
        intro i hi j hj
        rw [hWc, Finset.mem_filter, not_lt] at hi
        rw [hDc, Finset.mem_filter, not_lt]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [mem_crit] at hj
        obtain ⟨hp, he⟩ := hj
        have h1 := u_le (P i) q'.1 j hp
        have : q.1 j / (P i).1 j ≤ q'.1 j / (P i).1 j := by linarith [hi.2]
        exact (div_le_div_iff_of_pos_right hp).mp this)
      have H2 := H P' q'.1 hN' W D (by
        intro i hi j hj
        rw [hW, Finset.mem_filter] at hi
        have hiS : i ∉ S := fun hiS => by
          have := Sge i hiS
          linarith [hi.2]
        rw [hP' i hiS, mem_crit] at hj
        obtain ⟨hp, he⟩ := hj
        rw [hD, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 := u_le (P i) q.1 j hp
        have : q'.1 j / (P i).1 j < q.1 j / (P i).1 j := by linarith [hi.2]
        exact (div_lt_div_iff_of_pos_right hp).mp this)
      have hcard : (W.card : ℝ) + Wc.card = n := by
        have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
          (fun i => leontief (P i) q'.1 < leontief (P i) q.1)
        rw [Finset.card_univ, Fintype.card_fin] at h
        have h' : ((W.card + Wc.card : ℕ) : ℝ) = n := by exact_mod_cast h
        push_cast at h'
        exact h'
      have hfrac : (W.card : ℝ) / n + Wc.card / n = 1 := by
        rw [← add_div, hcard, div_self hn.ne']
      have hsum : ∑ j ∈ D, q.1 j + ∑ j ∈ Dc, q.1 j = 1 := by
        rw [hD, hDc, Finset.sum_filter_add_sum_filter_not]; exact q.2.2
      have hDe : D = ∅ := by
        by_contra hne
        have hlt := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hne)
          (fun j hj => (Finset.mem_filter.mp hj).2)
        linarith
      have hle : ∀ j, q.1 j ≤ q'.1 j := by
        intro j
        by_contra hj
        push_neg at hj
        have : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        rw [hDe] at this
        simp at this
      have heq : q.1 = q'.1 := by
        funext j
        exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp (by rw [q.2.2, q'.2.2]) j
          (Finset.mem_univ j)
      intro i _
      unfold LexEq
      rw [heq]
