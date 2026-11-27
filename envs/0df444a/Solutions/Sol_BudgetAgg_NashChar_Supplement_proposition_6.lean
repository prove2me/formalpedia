-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:46.645783+00:00
-- url     : https://prove2.me/submissions/9603a83d-249d-46f1-b2e5-7b53208273f5

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Proposition 6, p. 41: with Leximin-Leontief preferences, the Nash outcome
satisfies core fair share. -/
theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hnash : IsNashOutcome P q.1) : IsLexCoreFairShare P q := by
      classical
      have hu_nonneg : ∀ (p : stdSimplex ℝ (Fin m)) (x : Fin m → ℝ), (∀ j, 0 ≤ x j) →
          0 ≤ leontief p x := by
        intro p x hx
        unfold leontief
        rw [Finset.le_inf'_iff]
        intro j _
        exact div_nonneg (hx j) (p.2.1 j)
      have hu_le : ∀ (p : stdSimplex ℝ (Fin m)) (x : Fin m → ℝ) (j : Fin m), 0 < p.1 j →
          leontief p x ≤ x j / p.1 j := by
        intro p x j hj
        unfold leontief
        exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hu_ge : ∀ (p : stdSimplex ℝ (Fin m)) (x : Fin m → ℝ) (a : ℝ),
          (∀ j, 0 < p.1 j → a ≤ x j / p.1 j) → a ≤ leontief p x := by
        intro p x a h
        unfold leontief
        rw [Finset.le_inf'_iff]
        intro j hj
        exact h j (Finset.mem_filter.mp hj).2
      have hN0 : 0 < nashProduct P q.1 := by
        have hm : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
        obtain ⟨w, hw⟩ : ∃ w : Fin m → ℝ, ∀ j, w j = 1 / (m:ℝ) := ⟨_, fun _ => rfl⟩
        have hwmem : w ∈ stdSimplex ℝ (Fin m) := by
          refine ⟨fun j => by rw [hw]; positivity, ?_⟩
          simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
        refine lt_of_lt_of_le ?_ (hnash.2 w hwmem)
        unfold nashProduct
        apply Finset.prod_pos
        intro i _
        unfold leontief
        rw [Finset.lt_inf'_iff]
        intro j hj
        rw [hw]
        exact div_pos (by positivity) (Finset.mem_filter.mp hj).2
      have hcrit : ∀ (p : stdSimplex ℝ (Fin m)) (x : Fin m → ℝ) (j : Fin m),
          j ∈ crit p x ↔ 0 < p.1 j ∧ x j / p.1 j = leontief p x := by
        intro p x j
        unfold crit
        simp [Finset.mem_filter]
      have aux : ∀ (lx lr : List ℝ) (c : ℝ), List.Lex (· < ·) lx lr → lx ≠ [] →
          (∀ y ∈ lx, c ≤ y) → List.Pairwise (· ≤ ·) lr → ∀ z ∈ lr, c ≤ z := by
        intro lx lr c h hne hx hs z hz
        cases h with
        | nil => exact absurd rfl hne
        | @cons a l1 l2 h =>
          have hca : c ≤ a := hx a (List.mem_cons_self ..)
          rcases List.mem_cons.1 hz with rfl | hz'
          · exact hca
          · exact hca.trans ((List.pairwise_cons.1 hs).1 z hz')
        | @rel a b l1 l2 hab =>
          have hca : c ≤ a := hx a (List.mem_cons_self ..)
          rcases List.mem_cons.1 hz with rfl | hz'
          · exact hca.trans hab.le
          · exact (hca.trans hab.le).trans ((List.pairwise_cons.1 hs).1 z hz')
      have hlex : ∀ (p : stdSimplex ℝ (Fin m)) (r x : Fin m → ℝ), LexGt p r x →
          ∀ j ∈ crit p x, x j ≤ r j := by
        intro p r x h j hj
        obtain ⟨hpj, hjeq⟩ := (hcrit p x j).1 hj
        have hmemx : ∀ y ∈ ratioList p x, leontief p x ≤ y := by
          intro y hy
          unfold ratioList at hy
          rw [Multiset.mem_sort, Multiset.mem_map] at hy
          obtain ⟨k, hk, rfl⟩ := hy
          simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact hu_le p x k hk
        have hsorted : List.Pairwise (· ≤ ·) (ratioList p r) := Multiset.pairwise_sort _ _
        have hmemr : r j / p.1 j ∈ ratioList p r := by
          unfold ratioList
          rw [Multiset.mem_sort, Multiset.mem_map]
          exact ⟨j, by simp [hpj], rfl⟩
        have hne : ratioList p x ≠ [] := by
          intro he
          have : x j / p.1 j ∈ ratioList p x := by
            unfold ratioList
            rw [Multiset.mem_sort, Multiset.mem_map]
            exact ⟨j, by simp [hpj], rfl⟩
          rw [he] at this
          simp at this
        have key := aux _ _ _ h hne hmemx hsorted _ hmemr
        rw [← hjeq] at key
        exact (div_le_div_iff_of_pos_right hpj).1 key
      intro S hS ⟨q', hq'⟩
      have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
      set α : ℝ := (S.card : ℝ) / (n : ℝ) with hα
      set T := critG P q.1 S with hT
      set Q := ∑ j ∈ T, q.1 j with hQ
      have hα0 : 0 ≤ α := by positivity
      have hα1 : α ≤ 1 := by
        rw [hα, div_le_one hn]
        have := Finset.card_le_univ S
        simp only [Fintype.card_fin] at this
        exact_mod_cast this
      have hmemT : ∀ j, j ∈ T ↔ ∃ i ∈ S, j ∈ crit (P i) q.1 := by
        intro j
        simp [hT, critG, Finset.mem_biUnion]
      have hq0 : ∀ j, 0 ≤ q.1 j := q.2.1
      have hq1 : ∑ j, q.1 j = 1 := q.2.2
      have hQc : ∑ j ∈ Tᶜ, q.1 j = 1 - Q := by
        rw [← hq1, ← Finset.sum_add_sum_compl T]; ring
      have hQle1 : Q ≤ 1 := by
        have := Finset.sum_nonneg (fun j (_ : j ∈ Tᶜ) => hq0 j)
        linarith
      have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => hq0 j)
      -- Nash step
      have hQα : α ≤ Q := by
        by_contra hlt
        push Not at hlt
        have hQ1 : Q < 1 := lt_of_lt_of_le hlt hα1
        obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = Q / (1 - Q) := ⟨_, rfl⟩
        have hβ0 : 0 ≤ β := by rw [hβ]; exact div_nonneg hQ0 (by linarith)
        obtain ⟨s, hs⟩ : ∃ s : ℕ, s = S.card := ⟨_, rfl⟩
        obtain ⟨k, hk⟩ : ∃ k : ℕ, k = Sᶜ.card := ⟨_, rfl⟩
        have hsk : (k:ℝ) + s = n := by
          have := Finset.card_compl_add_card S
          simp only [Fintype.card_fin] at this
          rw [hk, hs]; exact_mod_cast this
        have hpos : 0 < (s:ℝ) - k * β := by
          have h1 : (n:ℝ) * Q < s := by
            rw [hα, lt_div_iff₀ hn] at hlt
            rw [hs]; linarith
          have h2 : (k:ℝ) * β = ((n:ℝ) - s) * Q / (1 - Q) := by
            rw [hβ, ← hsk]; ring
          rw [h2, sub_pos, div_lt_iff₀ (by linarith)]
          nlinarith
        obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ ε, g ε = (1 + ε)^s * (1 - ε*β)^k := ⟨_, fun _ => rfl⟩
        have hgd : HasDerivAt g ((s:ℝ) - k*β) 0 := by
          have h1 : HasDerivAt (fun ε : ℝ => (1 + ε)^s) ((s:ℝ) * (1 + 0)^(s-1) * 1) 0 :=
            ((hasDerivAt_id (0:ℝ)).const_add 1).fun_pow s
          have h2 : HasDerivAt (fun ε : ℝ => (1 - ε*β)^k)
              ((k:ℝ) * (1 - 0*β)^(k-1) * (-(1*β))) 0 :=
            (((hasDerivAt_id (0:ℝ)).mul_const β).const_sub 1).fun_pow k
          have h3 := (h1.mul h2).congr_deriv (show _ = (s:ℝ) - k*β by simp; ring)
          have hgeq : g = (fun ε : ℝ => (1 + ε)^s) * (fun ε : ℝ => (1 - ε*β)^k) := by
            funext ε; rw [hg]; rfl
          rw [hgeq]; exact h3
        have hev_g : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), 1 < g ε := by
          have hsl := (hasDerivAt_iff_tendsto_slope.1 hgd).mono_left
            (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioi (0:ℝ)) =>
              (Set.mem_compl_singleton_iff.2 (ne_of_gt hx))))
          filter_upwards [hsl.eventually_const_lt hpos, self_mem_nhdsWithin] with ε h1 h2
          rw [slope_def_field] at h1
          have h2' : (0:ℝ) < ε := h2
          rw [lt_div_iff₀ (by linarith)] at h1
          have hg0 : g 0 = 1 := by rw [hg]; simp
          rw [hg0] at h1
          nlinarith
        have hev_β : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ε * β < 1 := by
          have : Filter.Tendsto (fun ε : ℝ => ε * β) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (0 * β)) :=
            ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
          rw [zero_mul] at this
          exact this.eventually_lt_const one_pos
        have hev_pos : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < ε := self_mem_nhdsWithin
        have hev_S : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ i, ∀ j, i ∈ S → 0 < (P i).1 j → j ∉ T →
            (1 + ε) * leontief (P i) q.1 ≤ (1 - ε*β) * (q.1 j / (P i).1 j) := by
          rw [Filter.eventually_all]; intro i
          rw [Filter.eventually_all]; intro j
          by_cases hi : i ∈ S
          · by_cases hp : 0 < (P i).1 j
            · by_cases hjT : j ∈ T
              · filter_upwards with ε h1 h2 h3
                exact absurd hjT h3
              · have hstrict : leontief (P i) q.1 < q.1 j / (P i).1 j := by
                  refine lt_of_le_of_ne (hu_le _ _ _ hp) (fun h => hjT ?_)
                  exact (hmemT j).2 ⟨i, hi, (hcrit _ _ _).2 ⟨hp, h.symm⟩⟩
                have t1 : Filter.Tendsto (fun ε : ℝ => (1 + ε) * leontief (P i) q.1) (nhdsWithin (0:ℝ) (Set.Ioi 0))
                    (nhds ((1 + 0) * leontief (P i) q.1)) :=
                  (((continuous_const.add continuous_id).mul continuous_const).tendsto 0).mono_left
                    nhdsWithin_le_nhds
                have t2 : Filter.Tendsto (fun ε : ℝ => (1 - ε*β) * (q.1 j / (P i).1 j)) (nhdsWithin (0:ℝ) (Set.Ioi 0))
                    (nhds ((1 - 0*β) * (q.1 j / (P i).1 j))) :=
                  (((continuous_const.sub (continuous_id.mul continuous_const)).mul
                    continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
                have hlt' : (1 + 0) * leontief (P i) q.1 < (1 - 0*β) * (q.1 j / (P i).1 j) := by
                  simpa using hstrict
                filter_upwards [t1.eventually_lt t2 hlt'] with ε hε _ _ _
                exact hε.le
            · filter_upwards with ε h1 h2 h3
              exact absurd h2 hp
          · filter_upwards with ε h1 h2 h3
            exact absurd h1 hi
        obtain ⟨ε, hgε, hβε, hε, hSε⟩ := (hev_g.and (hev_β.and (hev_pos.and hev_S))).exists
        obtain ⟨qε, hqε⟩ : ∃ qε : Fin m → ℝ, ∀ j,
            qε j = if j ∈ T then (1 + ε) * q.1 j else (1 - ε*β) * q.1 j := ⟨_, fun _ => rfl⟩
        have hmem : qε ∈ stdSimplex ℝ (Fin m) := by
          refine ⟨fun j => ?_, ?_⟩
          · rw [hqε]
            split_ifs
            · exact mul_nonneg (by linarith) (hq0 j)
            · exact mul_nonneg (by linarith) (hq0 j)
          · have e1 : ∑ j ∈ T, qε j = (1 + ε) * Q := by
              rw [hQ, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j hj => by rw [hqε, if_pos hj])
            have e2 : ∑ j ∈ Tᶜ, qε j = (1 - ε*β) * (1 - Q) := by
              rw [← hQc, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j hj => by rw [hqε, if_neg (Finset.mem_compl.1 hj)])
            rw [← Finset.sum_add_sum_compl T qε, e1, e2, hβ]
            have : (1 - Q) ≠ 0 := by linarith
            field_simp
            ring
        have hle := hnash.2 qε hmem
        obtain ⟨f, hf⟩ : ∃ f : Fin n → ℝ, ∀ i, f i = if i ∈ S then 1 + ε else 1 - ε*β :=
          ⟨_, fun _ => rfl⟩
        have hf0 : ∀ i, 0 ≤ f i := by
          intro i; rw [hf]; split_ifs <;> linarith
        have hprodf : ∏ i, f i = g ε := by
          have e1 : ∏ i ∈ S, f i = ∏ i ∈ S, (1 + ε) :=
            Finset.prod_congr rfl (fun i hi => by rw [hf, if_pos hi])
          have e2 : ∏ i ∈ Sᶜ, f i = ∏ i ∈ Sᶜ, (1 - ε*β) :=
            Finset.prod_congr rfl (fun i hi => by rw [hf, if_neg (Finset.mem_compl.1 hi)])
          rw [← Finset.prod_mul_prod_compl S f, e1, e2, Finset.prod_const, Finset.prod_const, hg,
            hs, hk]
        have hlow : ∀ i, f i * leontief (P i) q.1 ≤ leontief (P i) qε := by
          intro i
          apply hu_ge
          intro j hp
          have hul := hu_le (P i) q.1 j hp
          have hr0 : 0 ≤ q.1 j / (P i).1 j := div_nonneg (hq0 j) ((P i).2.1 j)
          have hu0 := hu_nonneg (P i) q.1 hq0
          rw [hf, hqε]
          by_cases hi : i ∈ S
          · by_cases hj : j ∈ T
            · rw [if_pos hi, if_pos hj, mul_div_assoc]
              exact mul_le_mul_of_nonneg_left hul (by linarith)
            · rw [if_pos hi, if_neg hj, mul_div_assoc]
              exact hSε i j hi hp hj
          · by_cases hj : j ∈ T
            · rw [if_neg hi, if_pos hj, mul_div_assoc]
              have hεβ : 0 ≤ ε * β := mul_nonneg hε.le hβ0
              nlinarith
            · rw [if_neg hi, if_neg hj, mul_div_assoc]
              exact mul_le_mul_of_nonneg_left hul (by linarith)
        have hbig : g ε * nashProduct P q.1 ≤ nashProduct P qε := by
          rw [← hprodf]
          unfold nashProduct
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_le_prod (fun i _ => mul_nonneg (hf0 i) (hu_nonneg _ _ hq0))
            (fun i _ => hlow i)
        nlinarith
      have hkey : ∀ q'' : stdSimplex ℝ (Fin m), ∀ j ∈ T,
          q.1 j ≤ α * q'.1 j + (1 - α) * q''.1 j := by
        intro q'' j hj
        obtain ⟨i, hi, hji⟩ := (hmemT j).1 hj
        exact hlex (P i) _ q.1 (hq' q'' i hi) j hji
      have hfin : ∀ q'' : stdSimplex ℝ (Fin m),
          (∀ j, q.1 j ≤ α * q'.1 j + (1 - α) * q''.1 j) → False := by
        intro q'' hle
        have hsum : ∑ j, q.1 j = ∑ j, (α * q'.1 j + (1 - α) * q''.1 j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, q'.2.2, q''.2.2, hq1]
          ring
        have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).1 hsum
        have hfun : (fun j => α * q'.1 j + (1 - α) * q''.1 j) = q.1 :=
          funext fun j => (heq j (Finset.mem_univ _)).symm
        obtain ⟨i, hi⟩ := hS
        have h := hq' q'' i hi
        rw [hfun] at h
        exact List.lex_irrefl (fun x => lt_irrefl x) _ h
      by_cases hQ1 : Q < 1
      · obtain ⟨v, hv⟩ : ∃ v : Fin m → ℝ, ∀ j, v j = if j ∈ T then 0 else q.1 j / (1 - Q) :=
          ⟨_, fun _ => rfl⟩
        have hvmem : v ∈ stdSimplex ℝ (Fin m) := by
          refine ⟨fun j => ?_, ?_⟩
          · rw [hv]; split_ifs
            · exact le_refl 0
            · exact div_nonneg (hq0 j) (by linarith)
          · have e1 : ∑ j ∈ T, v j = 0 :=
              Finset.sum_eq_zero (fun j hj => by rw [hv, if_pos hj])
            have e2 : ∑ j ∈ Tᶜ, v j = ∑ j ∈ Tᶜ, q.1 j / (1 - Q) :=
              Finset.sum_congr rfl (fun j hj => by rw [hv, if_neg (Finset.mem_compl.1 hj)])
            rw [← Finset.sum_add_sum_compl T v, e1, e2, ← Finset.sum_div, hQc, zero_add]
            exact div_self (by linarith)
        apply hfin ⟨v, hvmem⟩
        intro j
        by_cases hj : j ∈ T
        · exact hkey ⟨v, hvmem⟩ j hj
        · show q.1 j ≤ α * q'.1 j + (1 - α) * v j
          rw [hv, if_neg hj]
          have h1 : q.1 j ≤ (1 - α) * (q.1 j / (1 - Q)) := by
            rw [mul_div_assoc', le_div_iff₀ (by linarith)]
            nlinarith [hq0 j]
          nlinarith [mul_nonneg hα0 (q'.2.1 j)]
      · apply hfin q
        intro j
        by_cases hj : j ∈ T
        · exact hkey q j hj
        · have hz : q.1 j = 0 := by
            have hs0 : ∑ k ∈ Tᶜ, q.1 k = 0 := by linarith
            exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq0 k)).1 hs0 j
              (Finset.mem_compl.2 hj)
          rw [hz]
          nlinarith [mul_nonneg hα0 (q'.2.1 j)]
