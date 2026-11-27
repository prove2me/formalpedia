-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:01.027798+00:00
-- url     : https://prove2.me/submissions/ea6ff9ad-3b03-4a6f-8d0b-7fa8ea4222ea

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 16, p. 42: for a continuous Leximin-Leontief-strategyproof mechanism `f`,
(a) on every strictly positive profile `P`, moving to the key profile `P∗` (built from
`q = f(P)` with `starPeak`) keeps the outcome; (b) for every profile, the critical
sets at `q = f(P)` are the same under `P∗` as under `P`. -/
theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (f : Mechanism n m) (hf_cont : Continuous f) (hf_sp : IsLexStrategyproof f) :
    (∀ P : Profile n m, (∀ i j, 0 < (P i).1 j) →
      ∃ Ps : Profile n m, (∀ i, (Ps i).1 = starPeak (P i) (f P).1) ∧ f Ps = f P) ∧
    (∀ P Ps : Profile n m, (∀ i, (Ps i).1 = starPeak (P i) (f P).1) →
      ∀ i, crit (Ps i) (f P).1 = crit (P i) (f P).1) := by
        classical
        -- basic facts about critical sets
        have memC : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (j : Fin m),
            j ∈ crit p q ↔ 0 < p.1 j ∧ q j / p.1 j = leontief p q := by
          intro p q j
          simp [crit]
        have leL : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) (j : Fin m),
            0 < p.1 j → leontief p q ≤ q j / p.1 j := by
          intro p q j hj
          unfold leontief
          exact Finset.inf'_le (fun j => q j / p.1 j) (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
        have Cne : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ), (crit p q).Nonempty := by
          intro p q
          obtain ⟨j0, hj0, heq⟩ := Finset.exists_mem_eq_inf' (positive_support_nonempty p)
            (fun j => q j / p.1 j)
          refine ⟨j0, (memC p q j0).mpr ⟨(Finset.mem_filter.mp hj0).2, ?_⟩⟩
          unfold leontief
          exact heq.symm
        have Spos : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ), 0 < ∑ k ∈ crit p q, p.1 k := by
          intro p q
          exact Finset.sum_pos (fun k hk => ((memC p q k).mp hk).1) (Cne p q)
        have Sle : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ), ∑ k ∈ crit p q, p.1 k ≤ 1 := by
          intro p q
          rw [← p.2.2]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => p.2.1 k)
        have H0 : ∀ (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ), starPeak p q ∈ stdSimplex ℝ (Fin m) := by
          intro p q
          have hS := Spos p q
          refine ⟨fun j => ?_, ?_⟩
          · unfold starPeak
            split_ifs
            · exact div_nonneg (p.2.1 j) hS.le
            · exact le_refl _
          · unfold starPeak
            rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, div_self hS.ne']
        -- Part (b), in general form
        have partB : ∀ (p ps : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ), ps.1 = starPeak p q →
            crit ps q = crit p q := by
          intro p ps q hps
          have hS := Spos p q
          set S := ∑ k ∈ crit p q, p.1 k with hSdef
          have supp : ∀ j, 0 < ps.1 j ↔ j ∈ crit p q := by
            intro j
            rw [hps]
            unfold starPeak
            constructor
            · intro h
              by_contra hj
              rw [if_neg hj] at h
              exact lt_irrefl _ h
            · intro hj
              rw [if_pos hj]
              exact div_pos ((memC p q j).mp hj).1 hS
          have ratio : ∀ j ∈ crit p q, q j / ps.1 j = S * leontief p q := by
            intro j hj
            have h1 := (memC p q j).mp hj
            rw [hps]
            unfold starPeak
            rw [if_pos hj, div_div_eq_mul_div, mul_div_right_comm, h1.2, mul_comm]
          have hlps : leontief ps q = S * leontief p q := by
            obtain ⟨j0, hj0⟩ := Cne p q
            apply le_antisymm
            · rw [← ratio j0 hj0]
              exact leL ps q j0 ((supp j0).mpr hj0)
            · unfold leontief
              apply Finset.le_inf'
              intro b hb
              have hb' := (supp b).mp (Finset.mem_filter.mp hb).2
              rw [ratio b hb']
              exact le_rfl
          ext j
          rw [memC ps q j, supp j, hlps]
          constructor
          · intro h; exact h.1
          · intro h; exact ⟨h, ratio j h⟩
        -- list lemmas
        have lexMap : ∀ (g : ℝ → ℝ), StrictMono g → ∀ A B : List ℝ,
            List.Lex (· < ·) A B → List.Lex (· < ·) (A.map g) (B.map g) := by
          intro g hg A B h
          induction h with
          | nil => exact List.Lex.nil
          | cons _ ih => exact List.Lex.cons ih
          | rel h => exact List.Lex.rel (hg h)
        have reflect : ∀ (g : ℝ → ℝ), StrictMono g → ∀ A B : List ℝ,
            (List.Lex (· < ·) (A.map g) (B.map g) ∨ B.map g = A.map g) →
            (List.Lex (· < ·) A B ∨ B = A) := by
          intro g hg A B h
          rcases Std.Trichotomous.rel_or_eq_or_rel_swap (r := List.Lex (· < ·)) (a := A) (b := B)
            with h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1.symm
          · exfalso
            have h2 := lexMap g hg B A h1
            rcases h with h | h
            · exact List.lt_asymm (List.lex_lt.mp h) (List.lex_lt.mp h2)
            · rw [h] at h2
              exact List.lt_irrefl _ (List.lex_lt.mp h2)
        have sortMap : ∀ (g : ℝ → ℝ), Monotone g → ∀ M : Multiset ℝ,
            (M.map g).sort (· ≤ ·) = (M.sort (· ≤ ·)).map g := by
          intro g hg M
          apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
          · exact Multiset.pairwise_sort _ _
          · exact List.Pairwise.map g (fun a b hab => hg hab) (Multiset.pairwise_sort _ _)
          · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, ← Multiset.map_coe, Multiset.sort_eq]
        have H1 : ∀ (Q : Profile n m) (a : Fin n), (∀ j, 0 < (Q a).1 j) →
            ∀ ps : stdSimplex ℝ (Fin m), ps.1 = starPeak (Q a) (f Q).1 →
            f (Function.update Q a ps) = f Q := by
          intro Q a hpos ps hps
          set p := Q a with hpdef
          set q := f Q with hqdef
          set C := crit p q.1 with hCdef
          set S := ∑ k ∈ C, p.1 k with hSdef
          have hS : 0 < S := Spos p q.1
          set L := leontief p q.1 with hLdef
          set x : Fin m → ℝ := fun j => q.1 j / p.1 j with hxdef
          obtain ⟨D, hD, hDgap⟩ : ∃ D : ℝ, 0 < D ∧ ∀ j k, x j ≠ x k → D ≤ |x j - x k| := by
            refine ⟨Finset.univ.inf' Finset.univ_nonempty
              (fun pr : Fin m × Fin m => if x pr.1 = x pr.2 then 1 else |x pr.1 - x pr.2|), ?_, ?_⟩
            · rw [Finset.lt_inf'_iff]
              intro pr _
              split_ifs with h
              · exact one_pos
              · exact abs_pos.mpr (sub_ne_zero.mpr h)
            · intro j k hjk
              have := Finset.inf'_le (fun pr : Fin m × Fin m =>
                if x pr.1 = x pr.2 then 1 else |x pr.1 - x pr.2|) (Finset.mem_univ (j, k))
              simp only [if_neg hjk] at this
              exact this
          obtain ⟨j0, hj0⟩ := Cne p q.1
          have hxj0 : x j0 = L := ((memC p q.1 j0).mp hj0).2
          have hL0 : 0 ≤ L := by
            rw [← hxj0]
            exact div_nonneg (q.2.1 j0) (hpos j0).le
          set t := L + D / 2 with htdef
          have ht : 0 < t := by linarith
          have sideC : ∀ z : Fin m → ℝ, (∀ j, |z j / p.1 j - x j| < D / 2) →
              (∀ j ∈ C, z j / p.1 j < t) ∧ (∀ j ∉ C, t ≤ z j / p.1 j) := by
            intro z hz
            constructor
            · intro j hj
              have h1 : x j = L := ((memC p q.1 j).mp hj).2
              have h2 := hz j
              rw [abs_lt] at h2
              linarith
            · intro j hj
              have h1 : x j ≠ x j0 := fun h => hj ((memC p q.1 j).mpr ⟨hpos j, h.trans hxj0⟩)
              have h3 : L ≤ x j := leL p q.1 j (hpos j)
              have h4 := hDgap j j0 h1
              rw [hxj0, abs_of_nonneg (by linarith)] at h4
              have h2 := hz j
              rw [abs_lt] at h2
              linarith
          let cc : ℝ → ℝ := fun c => (Set.projIcc (0:ℝ) 1 zero_le_one c : ℝ)
          have hcc_cont : Continuous cc := continuous_subtype_val.comp continuous_projIcc
          have hcc01 : ∀ c, 0 ≤ cc c ∧ cc c ≤ 1 := fun c => (Set.projIcc (0:ℝ) 1 zero_le_one c).2
          have hccid : ∀ c ∈ Set.Icc (0:ℝ) 1, cc c = c := fun c hc => by
            simp only [cc, Set.projIcc_of_mem _ hc]
          let pk : ℝ → stdSimplex ℝ (Fin m) := fun c =>
            ⟨(1 - cc c) • p.1 + cc c • ps.1, convex_stdSimplex ℝ (Fin m) p.2 ps.2
              (by linarith [hcc01 c]) (hcc01 c).1 (by ring)⟩
          have pk_apply : ∀ c j, (pk c).1 j = (1 - cc c) * p.1 j + cc c * ps.1 j := fun c j => by
            simp [pk]
          have pk_cont : Continuous pk := by
            apply Continuous.subtype_mk
            exact ((continuous_const.sub hcc_cont).smul continuous_const).add
              (hcc_cont.smul continuous_const)
          let QP : ℝ → Profile n m := fun c => Function.update Q a (pk c)
          have QP_cont : Continuous QP := Continuous.update continuous_const a pk_cont
          have pk0 : pk 0 = p := by
            apply Subtype.ext; funext j; rw [pk_apply, hccid 0 ⟨le_rfl, zero_le_one⟩]; ring
          have pk1 : pk 1 = ps := by
            apply Subtype.ext; funext j; rw [pk_apply, hccid 1 ⟨zero_le_one, le_rfl⟩]; ring
          have hmonoS : ∀ c, 0 ≤ c → c < 1 → StrictMono
              (fun v : ℝ => if v < t then v / ((1 - c) + c / S) else v / (1 - c)) := by
            intro c hc0 hc1 u v huv
            have hb : 0 < 1 - c := by linarith
            have hab : 1 - c ≤ (1 - c) + c / S := by have := div_nonneg hc0 hS.le; linarith
            have ha : 0 < (1 - c) + c / S := by linarith
            simp only
            split_ifs with h1 h2 h2
            · gcongr
            · have h2' : t ≤ v := not_lt.mp h2
              calc u / ((1 - c) + c / S) < t / ((1 - c) + c / S) := by gcongr
                _ ≤ t / (1 - c) := by gcongr
                _ ≤ v / (1 - c) := by gcongr
            · exfalso; linarith [not_lt.mp h1]
            · gcongr
          have CV : ∀ c, 0 ≤ c → c < 1 → ∀ z : Fin m → ℝ, (∀ j ∈ C, z j / p.1 j < t) →
              (∀ j ∉ C, t ≤ z j / p.1 j) →
              ratioList (pk c) z = (ratioList p z).map
                (fun v : ℝ => if v < t then v / ((1 - c) + c / S) else v / (1 - c)) := by
            intro c hc0 hc1 z hzC hzN
            have hcc : cc c = c := hccid c ⟨hc0, hc1.le⟩
            have hpkpos : ∀ j, 0 < (pk c).1 j := by
              intro j; rw [pk_apply, hcc]
              have h1 := ps.2.1 j
              have h2 := hpos j
              have h3 : 0 < (1 - c) * p.1 j := mul_pos (by linarith) h2
              have h4 : 0 ≤ c * ps.1 j := mul_nonneg hc0 h1
              linarith
            unfold ratioList
            rw [Finset.filter_true_of_mem (fun j _ => hpkpos j),
              Finset.filter_true_of_mem (fun j _ => hpos j)]
            rw [← sortMap _ (hmonoS c hc0 hc1).monotone]
            congr 1
            rw [Multiset.map_map]
            apply Multiset.map_congr rfl
            intro j _
            simp only [Function.comp]
            have hpj := hpos j
            have hb : 0 < 1 - c := by linarith
            by_cases hj : j ∈ C
            · rw [if_pos (hzC j hj), pk_apply, hcc]
              have : ps.1 j = p.1 j / S := by rw [hps]; unfold starPeak; rw [if_pos hj]
              rw [this]
              have ha : 0 < (1 - c) + c / S := by have := div_nonneg hc0 hS.le; linarith
              field_simp
            · rw [if_neg (not_lt.mpr (hzN j hj)), pk_apply, hcc]
              have : ps.1 j = 0 := by rw [hps]; unfold starPeak; rw [if_neg hj]
              rw [this]
              field_simp
              ring
          let A : Set ℝ := {c | f (QP c) = q}
          have hAcl : IsClosed A := isClosed_eq (hf_cont.comp QP_cont) continuous_const
          have h1A : (1:ℝ) ∈ A := by
            refine IsClosed.mem_of_ge_of_forall_exists_gt (hAcl.inter isClosed_Icc) ?_ zero_le_one ?_
            · show f (Function.update Q a (pk 0)) = f Q
              rw [pk0, hpdef, Function.update_eq_self]
            · rintro c ⟨hcA, hc0, hc1⟩
              have hfc : f (QP c) = q := hcA
              have hcont : Continuous (fun c : ℝ => fun j => (f (QP c)).1 j / p.1 j) := by
                apply continuous_pi; intro j
                exact ((continuous_apply j).comp
                  (continuous_subtype_val.comp (hf_cont.comp QP_cont))).div_const _
              obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.mp hcont c (D / 2) (by linarith)
              set c' := min (c + δ / 2) ((c + 1) / 2) with hc'
              have hc'1 : c < c' := lt_min (by linarith) (by linarith)
              have hc'2 : c' < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
              have hc'3 : c' ≤ c + δ / 2 := min_le_left _ _
              have hc'0 : 0 ≤ c' := by linarith
              have hdist : dist c' c < δ := by
                rw [Real.dist_eq, abs_lt]; constructor <;> linarith
              have hclose := hδc c' hdist
              rw [dist_pi_lt_iff (by linarith)] at hclose
              set qh := f (QP c') with hqh
              have hz : ∀ j, |qh.1 j / p.1 j - x j| < D / 2 := by
                intro j; have := hclose j; rw [hfc, Real.dist_eq] at this; exact this
              have hz0 : ∀ j, |q.1 j / p.1 j - x j| < D / 2 := by
                intro j; simp only [x, sub_self, abs_zero]; linarith
              have SC := sideC _ hz
              have SC0 := sideC _ hz0
              have sp1 : LexGe (pk c) q.1 qh.1 := by
                have h := hf_sp a (QP c) (QP c') (fun j hj => by
                  simp only [QP]; rw [Function.update_of_ne hj, Function.update_of_ne hj])
                have e : QP c a = pk c := Function.update_self a _ Q
                rw [e, hfc] at h; exact h
              have sp2 : LexGe (pk c') qh.1 q.1 := by
                have h := hf_sp a (QP c') (QP c) (fun j hj => by
                  simp only [QP]; rw [Function.update_of_ne hj, Function.update_of_ne hj])
                have e : QP c' a = pk c' := Function.update_self a _ Q
                rw [e, hfc] at h; exact h
              unfold LexGe LexGt LexEq at sp1 sp2
              rw [CV c hc0 hc1 qh.1 SC.1 SC.2, CV c hc0 hc1 q.1 SC0.1 SC0.2] at sp1
              rw [CV c' hc'0 hc'2 qh.1 SC.1 SC.2, CV c' hc'0 hc'2 q.1 SC0.1 SC0.2] at sp2
              have r1 := reflect _ (hmonoS c hc0 hc1) _ _ sp1
              have r2 := reflect _ (hmonoS c' hc'0 hc'2) _ _ sp2
              have heq : ratioList p q.1 = ratioList p qh.1 := by
                rcases r1 with r1 | r1
                · rcases r2 with r2 | r2
                  · exact absurd (List.lex_lt.mp r2) (List.lt_asymm (List.lex_lt.mp r1))
                  · exact r2.symm
                · exact r1
              have hM := congrArg (fun l : List ℝ => (l : Multiset ℝ)) heq
              simp only [ratioList, Multiset.sort_eq] at hM
              rw [Finset.filter_true_of_mem (fun j _ => hpos j)] at hM
              have hqh_eq : qh = q := by
                apply Subtype.ext; funext j
                have hmem : qh.1 j / p.1 j ∈ Finset.univ.val.map (fun j => qh.1 j / p.1 j) :=
                  Multiset.mem_map_of_mem _ (Finset.mem_univ j)
                rw [← hM] at hmem
                obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp hmem
                have hk' : x k = qh.1 j / p.1 j := hk
                have hxy : qh.1 j / p.1 j = x j := by
                  by_contra hne
                  have h1 : x k ≠ x j := by rw [hk']; exact hne
                  have h2 := hDgap k j h1
                  have h3 := hz j
                  rw [hk'] at h2
                  linarith
                exact (div_left_inj' (hpos j).ne').mp hxy
              exact ⟨c', hqh_eq, hc'1, hc'2.le⟩
          have h1 : f (QP 1) = q := h1A
          have e : QP 1 = Function.update Q a ps := by simp only [QP, pk1]
          rw [← e]; exact h1
        refine ⟨?_, fun P Ps hPs i => partB (P i) (Ps i) (f P).1 (hPs i)⟩
        intro P hP
        let star : Fin n → stdSimplex ℝ (Fin m) := fun i => ⟨starPeak (P i) (f P).1, H0 _ _⟩
        let PT : Finset (Fin n) → Profile n m := fun T i => if i ∈ T then star i else P i
        have hPT : ∀ T, f (PT T) = f P := by
          intro T
          induction T using Finset.induction_on with
          | empty =>
            have e : PT ∅ = P := by funext i; simp [PT]
            rw [e]
          | insert a T haT ih =>
            have e : PT (insert a T) = Function.update (PT T) a (star a) := by
              funext i
              by_cases hi : i = a
              · subst hi; simp [PT]
              · simp [PT, hi]
            have ea : PT T a = P a := by simp [PT, haT]
            rw [e, H1 (PT T) a (by rw [ea]; exact hP a) (star a) (by rw [ea, ih])]
            exact ih
        exact ⟨PT Finset.univ, fun i => by simp [PT, star], hPT _⟩
