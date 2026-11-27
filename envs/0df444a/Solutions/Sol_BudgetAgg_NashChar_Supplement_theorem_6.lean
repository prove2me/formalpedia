-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:16.853963+00:00
-- url     : https://prove2.me/submissions/21d0f153-dec2-45ea-9410-06e73bce0b2e

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

/-- Theorem 6, p. 18: for `m = 2` and any admissible domain `U ⊆ U_SP`, the uniform
phantom rule is the only continuous, strategyproof and proportional mechanism. -/
theorem solution {n : ℕ} [NeZero n] (U : Set (ℝ → ℝ)) (hU : IsSPDomain U)
    (f : Mechanism2 n) :
    (Continuous f ∧ IsSP2 U f ∧ IsProportional2 f) ↔
      ∀ P, (f P : ℝ) = uniformPhantom P := by
        classical
        have rank : ∀ (l : List ℝ), l.SortedLE → ∀ (p : ℝ → Prop),
            (∀ a b, a ≤ b → p b → p a) → ∀ k, k < l.length →
            (p (l.getD k 0) ↔ k < (l.filter p).length) := by
          intro l
          induction l with
          | nil => simp
          | cons a l ih =>
            intro hs p hp k hk
            have hl : l.SortedLE := hs.pairwise.tail.sortedLE
            have ha : ∀ b ∈ l, a ≤ b := (List.pairwise_cons.mp hs.pairwise).1
            by_cases hpa : p a
            · cases k with
              | zero => simp [hpa]
              | succ k =>
                simpa [hpa] using ih hl p hp k (by simpa using hk)
            · have hempty : l.filter p = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro b hb
                exact fun hpb => hpa (hp a b (ha b hb) (by simpa using hpb))
              have hnot : ¬ p ((a :: l).getD k 0) := by
                intro h
                cases k with
                | zero => exact hpa (by simpa using h)
                | succ k =>
                  have hkl : k < l.length := by simpa using hk
                  rw [List.getD_cons_succ, List.getD_eq_getElem _ _ hkl] at h
                  exact hpa (hp a l[k] (ha _ (List.getElem_mem hkl)) h)
              simpa only [List.filter_cons, decide_eq_true_eq, if_neg hpa, hempty, List.length_nil, Nat.not_lt_zero, iff_false] using hnot
        have med_le_count : ∀ {ι : Type} [Fintype ι] (x : ι → ℝ) (t : ℝ),
            0 < Fintype.card ι →
            (med x ≤ t ↔ Fintype.card ι / 2 < (Finset.univ.filter (fun i => x i ≤ t)).card) := by
          intro ι inst x t hc
          let l := ((Finset.univ.val.map x).sort (· ≤ ·))
          have hl : l.SortedLE := (Multiset.pairwise_sort _ _).sortedLE
          have hlen : l.length = Fintype.card ι := by simp [l]
          have hfilter : (l.filter (fun a => a ≤ t)).length =
              (Finset.univ.filter (fun i => x i ≤ t)).card := by
            change ((↑l : Multiset ℝ).filter (fun a => a ≤ t)).card = _
            rw [show (↑l : Multiset ℝ) = Finset.univ.val.map x from Multiset.sort_eq _ _]
            simp [Multiset.filter_map, ← Finset.filter_val]
          change l.getD (Fintype.card ι / 2) 0 ≤ t ↔ _
          rw [rank l hl (fun a => a ≤ t) (fun a b hab hb => hab.trans hb)
            _ (by omega), hfilter]
        have med_lt_count : ∀ {ι : Type} [Fintype ι] (x : ι → ℝ) (t : ℝ),
            0 < Fintype.card ι →
            (med x < t ↔ Fintype.card ι / 2 < (Finset.univ.filter (fun i => x i < t)).card) := by
          intro ι inst x t hc
          let l := ((Finset.univ.val.map x).sort (· ≤ ·))
          have hl : l.SortedLE := (Multiset.pairwise_sort _ _).sortedLE
          have hlen : l.length = Fintype.card ι := by simp [l]
          have hfilter : (l.filter (fun a => a < t)).length =
              (Finset.univ.filter (fun i => x i < t)).card := by
            change ((↑l : Multiset ℝ).filter (fun a => a < t)).card = _
            rw [show (↑l : Multiset ℝ) = Finset.univ.val.map x from Multiset.sort_eq _ _]
            simp [Multiset.filter_map, ← Finset.filter_val]
          change l.getD (Fintype.card ι / 2) 0 < t ↔ _
          rw [rank l hl (fun a => a < t) (fun a b hab hb => hab.trans_lt hb)
            _ (by omega), hfilter]
        have hc : Fintype.card (Fin n ⊕ Fin (n + 1)) = 2 * n + 1 := by simp; omega
        have m_le (x : (Fin n ⊕ Fin (n + 1)) → ℝ) (t : ℝ) :
            med x ≤ t ↔ n < (Finset.univ.filter (fun i => x i ≤ t)).card := by
          have hh : Fintype.card (Fin n ⊕ Fin (n + 1)) / 2 = n := by rw [hc]; omega
          simpa only [hh] using med_le_count x t (by rw [hc]; omega)
        have m_lt (x : (Fin n ⊕ Fin (n + 1)) → ℝ) (t : ℝ) :
            med x < t ↔ n < (Finset.univ.filter (fun i => x i < t)).card := by
          have hh : Fintype.card (Fin n ⊕ Fin (n + 1)) / 2 = n := by rw [hc]; omega
          simpa only [hh] using med_lt_count x t (by rw [hc]; omega)
        have m_ge (x : (Fin n ⊕ Fin (n + 1)) → ℝ) (t : ℝ) :
            t ≤ med x ↔ n < (Finset.univ.filter (fun i => t ≤ x i)).card := by
          have hh := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n ⊕ Fin (n + 1)))) (fun i => x i < t)
          simp only [not_lt, Finset.card_univ, hc] at hh
          rw [← not_lt, m_lt]
          omega
        have m_gt (x : (Fin n ⊕ Fin (n + 1)) → ℝ) (t : ℝ) :
            t < med x ↔ n < (Finset.univ.filter (fun i => t < x i)).card := by
          have hh := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n ⊕ Fin (n + 1)))) (fun i => x i ≤ t)
          simp only [not_le, Finset.card_univ, hc] at hh
          rw [← not_le, m_le]
          omega
        have open_count {A : Type} [TopologicalSpace A] (p : (Fin n ⊕ Fin (n + 1)) → A → Prop)
            (hp : ∀ i, IsOpen {a | p i a}) :
            IsOpen {a | n < (Finset.univ.filter (fun i => p i a)).card} := by
          have he : {a | n < (Finset.univ.filter (fun i => p i a)).card} =
              ⋃ s : Finset (Fin n ⊕ Fin (n + 1)), ⋃ (_ : n < s.card), ⋂ i ∈ s, {a | p i a} := by
            ext a
            simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
            constructor
            · intro h
              exact ⟨Finset.univ.filter (fun i => p i a), h, fun i hi => (Finset.mem_filter.mp hi).2⟩
            · rintro ⟨s, hs, hh⟩
              have hsub : s ⊆ Finset.univ.filter (fun i => p i a) := by
                intro i hi
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh i hi⟩
              exact hs.trans_le (Finset.card_le_card hsub)
          rw [he]
          exact isOpen_iUnion fun s => isOpen_iUnion fun _ => isOpen_biInter_finset fun i _ => hp i
        have continuous_med {A : Type} [TopologicalSpace A]
            (x : A → (Fin n ⊕ Fin (n + 1)) → ℝ) (hx : ∀ i, Continuous (fun a => x a i)) :
            Continuous (fun a => med (x a)) := by
          apply OrderTopology.continuous_iff.mpr
          intro t
          constructor
          · have he : (fun a => med (x a)) ⁻¹' Set.Ioi t =
                {a | n < (Finset.univ.filter (fun i => t < x a i)).card} := by
              ext a; exact m_gt (x a) t
            rw [he]
            exact open_count (fun i a => t < x a i) (fun i => isOpen_lt continuous_const (hx i))
          · have he : (fun a => med (x a)) ⁻¹' Set.Iio t =
                {a | n < (Finset.univ.filter (fun i => x a i < t)).card} := by
              ext a; exact m_lt (x a) t
            rw [he]
            exact open_count (fun i a => x a i < t) (fun i => isOpen_lt (hx i) continuous_const)
        have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
        let X (P : Profile2 n) : (Fin n ⊕ Fin (n + 1)) → ℝ :=
          Sum.elim (fun i => (P i : ℝ)) (fun k => (k : ℝ) / (n : ℝ))
        have hX (P : Profile2 n) (i) : 0 ≤ X P i ∧ X P i ≤ 1 := by
          cases i with
          | inl i => exact (P i).property
          | inr k =>
            dsimp [X]
            constructor
            · positivity
            · apply (div_le_one hn).mpr
              exact_mod_cast (Nat.le_of_lt_succ k.isLt)
        have hbound (P : Profile2 n) : 0 ≤ uniformPhantom P ∧ uniformPhantom P ≤ 1 := by
          change 0 ≤ med (X P) ∧ med (X P) ≤ 1
          constructor
          · apply (m_ge _ _).mpr
            have he : Finset.univ.filter (fun i => 0 ≤ X P i) = Finset.univ := by
              ext i; simp [(hX P i).1]
            rw [he, Finset.card_univ, hc]; omega
          · apply (m_le _ _).mpr
            have he : Finset.univ.filter (fun i => X P i ≤ 1) = Finset.univ := by
              ext i; simp [(hX P i).2]
            rw [he, Finset.card_univ, hc]; omega
        let g : Mechanism2 n := fun P => ⟨uniformPhantom P, hbound P⟩
        have hg_cont : Continuous g := by
          apply Continuous.subtype_mk
          apply continuous_med X
          intro i
          cases i with
          | inl i => exact continuous_subtype_val.comp (continuous_apply i)
          | inr k => exact continuous_const
        have peakmax (u : ℝ → ℝ) (p : unitInterval) (hu : IsSinglePeakedAt u p)
            (a : unitInterval) (ha : a ≠ p) : u a < u p := by
          have h := hu a (fun h => ha (Subtype.ext h)) (1 / 2) (by norm_num) (by norm_num)
          exact h.2.trans h.1
        have prefL (u : ℝ → ℝ) (p : unitInterval) (hu : IsSinglePeakedAt u p)
            (a b : unitInterval) (hab : (a : ℝ) < b) (hbp : (b : ℝ) ≤ p) : u a < u b := by
          by_cases hb : b = p
          · subst b
            exact peakmax u p hu a (fun h => by simpa [h] using hab)
          · have hbp' : (b : ℝ) < p := lt_of_le_of_ne hbp (fun h => hb (Subtype.ext h))
            have hap : (a : ℝ) < p := hab.trans hbp'
            have hden : 0 < (p : ℝ) - a := sub_pos.mpr hap
            have ht0 : 0 < ((b : ℝ) - a) / ((p : ℝ) - a) := div_pos (sub_pos.mpr hab) hden
            have ht1 : ((b : ℝ) - a) / ((p : ℝ) - a) < 1 := (div_lt_one hden).mpr (by linarith)
            have he : (((b : ℝ) - a) / ((p : ℝ) - a)) * p +
                (1 - ((b : ℝ) - a) / ((p : ℝ) - a)) * a = b := by
              field_simp; ring
            have hh := (hu a (ne_of_lt hap) _ ht0 ht1).2
            simpa only [he] using hh
        have prefR (u : ℝ → ℝ) (p : unitInterval) (hu : IsSinglePeakedAt u p)
            (a b : unitInterval) (hpa : (p : ℝ) ≤ a) (hab : (a : ℝ) < b) : u b < u a := by
          by_cases ha : a = p
          · subst a
            exact peakmax u p hu b (fun h => by simpa [h] using hab)
          · have hpa' : (p : ℝ) < a := lt_of_le_of_ne hpa (fun h => ha (Subtype.ext h.symm))
            have hpb : (p : ℝ) < b := hpa'.trans hab
            have hden : 0 < (b : ℝ) - p := sub_pos.mpr hpb
            have ht0 : 0 < ((b : ℝ) - a) / ((b : ℝ) - p) := div_pos (sub_pos.mpr hab) hden
            have ht1 : ((b : ℝ) - a) / ((b : ℝ) - p) < 1 := (div_lt_one hden).mpr (by linarith)
            have he : (((b : ℝ) - a) / ((b : ℝ) - p)) * p +
                (1 - ((b : ℝ) - a) / ((b : ℝ) - p)) * b = a := by
              field_simp; ring
            have hh := (hu b (ne_of_gt hpb) _ ht0 ht1).2
            simpa only [he] using hh
        have weakL (u : ℝ → ℝ) (p : unitInterval) (hu : IsSinglePeakedAt u p)
            (a b : unitInterval) (hab : (a : ℝ) ≤ b) (hbp : (b : ℝ) ≤ p) : u a ≤ u b := by
          rcases hab.eq_or_lt with he | he
          · exact le_of_eq (congrArg u he)
          · exact (prefL u p hu a b he hbp).le
        have weakR (u : ℝ → ℝ) (p : unitInterval) (hu : IsSinglePeakedAt u p)
            (a b : unitInterval) (hpa : (p : ℝ) ≤ a) (hab : (a : ℝ) ≤ b) : u b ≤ u a := by
          rcases hab.eq_or_lt with he | he
          · exact le_of_eq (congrArg u he.symm)
          · exact (prefR u p hu a b hpa he).le
        have hg_sp : IsSP2 U g := by
          intro i P q u hu hup
          let Q := Function.update P i q
          change u (g Q) ≤ u (g P)
          rcases lt_trichotomy (g P : ℝ) (P i : ℝ) with hlt | heq | hgt
          · have hsub : Finset.univ.filter (fun j => X P j ≤ (g P : ℝ)) ⊆
                Finset.univ.filter (fun j => X Q j ≤ (g P : ℝ)) := by
              intro j hj
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, ?_⟩
              have hj' := (Finset.mem_filter.mp hj).2
              cases j with
              | inr k => exact hj'
              | inl j =>
                by_cases hji : j = i
                · subst j; exact (not_le_of_gt hlt hj').elim
                · simpa [X, Q, Function.update_of_ne hji] using hj'
            have hy : (g Q : ℝ) ≤ g P := (m_le _ _).mpr
              (lt_of_lt_of_le ((m_le _ _).mp le_rfl) (Finset.card_le_card hsub))
            exact weakL u (P i) hup (g Q) (g P) hy hlt.le
          · have hp : g P = P i := Subtype.ext heq
            by_cases hq : g Q = P i
            · rw [show g Q = g P from hq.trans hp.symm]
            · rw [hp]
              exact (peakmax u (P i) hup (g Q) hq).le
          · have hsub : Finset.univ.filter (fun j => (g P : ℝ) ≤ X P j) ⊆
                Finset.univ.filter (fun j => (g P : ℝ) ≤ X Q j) := by
              intro j hj
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, ?_⟩
              have hj' := (Finset.mem_filter.mp hj).2
              cases j with
              | inr k => exact hj'
              | inl j =>
                by_cases hji : j = i
                · subst j; exact (not_le_of_gt hgt hj').elim
                · simpa [X, Q, Function.update_of_ne hji] using hj'
            have hy : (g P : ℝ) ≤ g Q := (m_ge _ _).mpr
              (lt_of_lt_of_le ((m_ge _ _).mp le_rfl) (Finset.card_le_card hsub))
            exact weakR u (P i) hup (g P) (g Q) hgt.le hy
        have sum_count (P : Profile2 n) (hP : IsSingleMinded2 P) :
            (∑ i, (P i : ℝ)) = ((Finset.univ.filter (fun i => (P i : ℝ) = 1)).card : ℝ) := by
          rw [← Finset.sum_boole]
          apply Finset.sum_congr rfl
          intro i hi
          rcases hP i with hi | hi <;> simp [hi]
        have count_sum (p : (Fin n ⊕ Fin (n + 1)) → Prop) :
            (Finset.univ.filter p).card =
            (Finset.univ.filter (fun i => p (.inl i))).card +
            (Finset.univ.filter (fun i => p (.inr i))).card := by
          have he : Finset.univ.filter p =
              (Finset.univ.filter (fun i => p (.inl i))).disjSum
              (Finset.univ.filter (fun i => p (.inr i))) := by
            ext i; cases i <;> simp
          rw [he, Finset.card_disjSum]
        have hg_prop : IsProportional2 g := by
          intro P hP
          let k := (Finset.univ.filter (fun i => (P i : ℝ) = 1)).card
          have hk : k ≤ n := by
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          have hs : (∑ i, (P i : ℝ)) = (k : ℝ) := sum_count P hP
          rw [hs]
          change med (X P) = (k : ℝ) / n
          have hk0 : 0 ≤ (k : ℝ) / n := by positivity
          have hk1 : (k : ℝ) / n ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hk)
          have hzero : (Finset.univ.filter (fun i => (P i : ℝ) = 0)).card + k = n := by
            have hh := Finset.card_filter_add_card_filter_not
              (s := (Finset.univ : Finset (Fin n))) (fun i => (P i : ℝ) = 1)
            have he : Finset.univ.filter (fun i => ¬ (P i : ℝ) = 1) =
                Finset.univ.filter (fun i => (P i : ℝ) = 0) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rcases hP i with hi | hi <;> rw [hi] <;> norm_num
            rw [he] at hh
            simpa [k, Nat.add_comm] using hh
          apply le_antisymm
          · apply (m_le _ _).mpr
            rw [count_sum]
            have hp : (Finset.univ.filter (fun i : Fin n => (P i : ℝ) = 0)).card ≤
                (Finset.univ.filter (fun i => X P (.inl i) ≤ (k : ℝ) / n)).card := by
              apply Finset.card_le_card
              intro i hi
              have hi' := (Finset.mem_filter.mp hi).2
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              simpa [X, hi'] using hk0
            have hphant : (Finset.univ.filter (fun j : Fin (n + 1) => X P (.inr j) ≤ (k : ℝ) / n)).card = k + 1 := by
              have he : Finset.univ.filter (fun j : Fin (n + 1) => X P (.inr j) ≤ (k : ℝ) / n) =
                  Finset.univ.filter (fun j : Fin (n + 1) => j.val < k + 1) := by
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, X, Sum.elim_inr,
                  div_le_div_iff_of_pos_right hn]
                rw [Nat.cast_le]
                omega
              rw [he]
              rw [Fin.card_filter_val_lt]
              omega
            rw [hphant]
            omega
          · apply (m_ge _ _).mpr
            rw [count_sum]
            have hp : k ≤ (Finset.univ.filter (fun i => (k : ℝ) / n ≤ X P (.inl i))).card := by
              apply Finset.card_le_card
              intro i hi
              have hi' := (Finset.mem_filter.mp hi).2
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              simpa [X, hi'] using hk1
            have hphant : (Finset.univ.filter (fun j : Fin (n + 1) => (k : ℝ) / n ≤ X P (.inr j))).card = n + 1 - k := by
              have he : Finset.univ.filter (fun j : Fin (n + 1) => (k : ℝ) / n ≤ X P (.inr j)) =
                  Finset.univ.filter (fun j : Fin (n + 1) => ¬ j.val < k) := by
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, X, Sum.elim_inr,
                  div_le_div_iff_of_pos_right hn]
                rw [Nat.cast_le]
                omega
              rw [he]
              have hh := Finset.card_filter_add_card_filter_not
                (s := (Finset.univ : Finset (Fin (n + 1)))) (fun j => j.val < k)
              have hh' := Fin.card_filter_val_lt (n := n + 1) (m := k)
              simp only [Finset.card_univ, Fintype.card_fin] at hh
              omega
            rw [hphant]
            omega
        have slice (r : Mechanism2 n) (hrc : Continuous r) (hrs : IsSP2 U r)
            (P : Profile2 n) (i : Fin n) :
            r P = max (r (Function.update P i 0)) (min (P i) (r (Function.update P i 1))) := by
          let v : unitInterval → unitInterval := fun q => r (Function.update P i q)
          have hv : Continuous v := hrc.comp (continuous_const.update i continuous_id)
          have hsp (p q : unitInterval) (u : ℝ → ℝ) (hu : u ∈ U)
              (hup : IsSinglePeakedAt u p) : u (v q) ≤ u (v p) := by
            have hh := hrs i (Function.update P i p) q u hu (by simpa using hup)
            simpa [v] using hh
          have hlo (q : unitInterval) : v 0 ≤ v q := by
            obtain ⟨u, hu, hup⟩ := hU.2 0
            by_contra h
            have hlt : (v q : ℝ) < v 0 := lt_of_not_ge h
            have hh := prefR u 0 hup (v q) (v 0) (v q).property.1 hlt
            exact (not_lt_of_ge (hsp 0 q u hu hup)) hh
          have hhi (q : unitInterval) : v q ≤ v 1 := by
            obtain ⟨u, hu, hup⟩ := hU.2 1
            by_contra h
            have hlt : (v 1 : ℝ) < v q := lt_of_not_ge h
            have hh := prefL u 1 hup (v 1) (v q) hlt (v q).property.2
            exact (not_lt_of_ge (hsp 1 q u hu hup)) hh
          have hab : v 0 ≤ v 1 := hlo 1
          have hfix (p : unitInterval) (hp : v 0 ≤ p ∧ p ≤ v 1) : v p = p := by
            obtain ⟨q, hq, he⟩ := intermediate_value_Icc
              (show (0 : unitInterval) ≤ 1 from zero_le_one) hv.continuousOn hp
            obtain ⟨u, hu, hup⟩ := hU.2 p
            by_contra hne
            have hh := hsp p q u hu hup
            rw [he] at hh
            exact (not_lt_of_ge hh) (peakmax u p hup (v p) hne)
          have hclamp (p : unitInterval) : v p = max (v 0) (min p (v 1)) := by
            by_cases hpa : p ≤ v 0
            · have hvp : v p = v 0 := by
                apply le_antisymm _ (hlo p)
                by_contra h
                have hlt : (v 0 : ℝ) < v p := lt_of_not_ge h
                obtain ⟨u, hu, hup⟩ := hU.2 p
                have hh := prefR u p hup (v 0) (v p) hpa hlt
                exact (not_lt_of_ge (hsp p 0 u hu hup)) hh
              rw [hvp, min_eq_left (hpa.trans hab), max_eq_left hpa]
            · by_cases hbp : v 1 ≤ p
              · have hvp : v p = v 1 := by
                  apply le_antisymm (hhi p)
                  by_contra h
                  have hlt : (v p : ℝ) < v 1 := lt_of_not_ge h
                  obtain ⟨u, hu, hup⟩ := hU.2 p
                  have hh := prefL u p hup (v p) (v 1) hlt hbp
                  exact (not_lt_of_ge (hsp p 1 u hu hup)) hh
                rw [hvp, min_eq_right hbp, max_eq_right hab]
              · rw [hfix p ⟨(le_of_not_ge hpa), (le_of_not_ge hbp)⟩,
                  min_eq_left (le_of_not_ge hbp), max_eq_right (le_of_not_ge hpa)]
          have hh := hclamp (P i)
          simpa [v] using hh
        have unique (r s : Mechanism2 n) (hrc : Continuous r) (hrs : IsSP2 U r)
            (hsc : Continuous s) (hss : IsSP2 U s)
            (hvert : ∀ P, IsSingleMinded2 P → r P = s P) : r = s := by
          have hh : ∀ (t : Finset (Fin n)) (P : Profile2 n),
              (∀ i, i ∉ t → P i = 0 ∨ P i = 1) → r P = s P := by
            intro t
            induction t using Finset.induction_on with
            | empty =>
              intro P hP
              apply hvert P
              intro i
              rcases hP i (by simp) with h | h <;> simp [h]
            | @insert i t hit ih =>
              intro P hP
              have hzero : r (Function.update P i 0) = s (Function.update P i 0) := by
                apply ih
                intro j hj
                by_cases hji : j = i
                · subst j; simp
                · simpa [Function.update_of_ne hji] using hP j (by simp [hj, hji])
              have hone : r (Function.update P i 1) = s (Function.update P i 1) := by
                apply ih
                intro j hj
                by_cases hji : j = i
                · subst j; simp
                · simpa [Function.update_of_ne hji] using hP j (by simp [hj, hji])
              rw [slice r hrc hrs P i, slice s hsc hss P i, hzero, hone]
          funext P
          exact hh Finset.univ P (by simp)
        constructor
        · rintro ⟨hfc, hfs, hfp⟩
          have he : f = g := unique f g hfc hfs hg_cont hg_sp (by
            intro P hP
            apply Subtype.ext
            exact (hfp P hP).trans (hg_prop P hP).symm)
          intro P
          rw [he]
        · intro h
          have he : f = g := by
            funext P
            exact Subtype.ext (h P)
          rw [he]
          exact ⟨hg_cont, hg_sp, hg_prop⟩
