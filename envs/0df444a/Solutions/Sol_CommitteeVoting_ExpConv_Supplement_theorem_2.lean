-- Prove2me | solution 1 for CommitteeVoting.ExpConv.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:41.30594+00:00
-- url     : https://prove2.me/submissions/e5593a09-dfe9-44ec-b08d-385a0998555f

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Supplement_RandomTypes
import Definitions.Def_CommitteeVoting_ExpConv_Supplement_Formula

open CommitteeVoting
open CommitteeVoting.ExpConv
open CommitteeVoting.ExpConv.Supplement

/-- Theorem 2 (p.16), corrected at integer p*k: success under iid Bernoulli(p) types
and conditionally independent type-specific score laws equals (12) with all three
occurrences of ceil(p*k) replaced by floor(p*k)+1. A committee is nonempty. -/
theorem solution {m n k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (fh fm : PMF (Fin (n + 1))) :
    successProbability (m := m) k p fh fm = correctedFormula m k p fh fm := by
      classical
      -- arithmetic of cutoffs
      have hfl0 : (0 : ℤ) ≤ ⌊p * (k : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
      have hce0 : (0 : ℤ) ≤ ⌈(1 - p) * (k : ℝ)⌉ :=
        Int.ceil_nonneg (mul_nonneg (by linarith) (by positivity))
      have hsumZ : ⌈(1 - p) * (k : ℝ)⌉ = (k : ℤ) - ⌊p * (k : ℝ)⌋ := by
        have h1 : (1 - p) * (k : ℝ) = -(p * (k : ℝ)) + ((k : ℤ) : ℝ) := by push_cast; ring
        rw [h1, Int.ceil_add_intCast, Int.ceil_neg]; ring
      obtain ⟨c, hc⟩ : ∃ c, c = honestCutoff k p := ⟨_, rfl⟩
      obtain ⟨d, hd⟩ : ∃ d, d = dishonestCutoff k p := ⟨_, rfl⟩
      have hcZ : ⌈(1 - p) * (k : ℝ)⌉ = (c : ℤ) := by
        rw [hc, honestCutoff, Int.toNat_of_nonneg hce0]
      have hcd : c + d = k + 1 := by
        have : (d : ℤ) = ⌊p * (k : ℝ)⌋ + 1 := by
          rw [hd, dishonestCutoff]; push_cast; rw [Int.toNat_of_nonneg hfl0]
        omega
      have hd1 : 1 ≤ d := by rw [hd, dishonestCutoff]; omega
      have hc1 : p ≠ 1 → 1 ≤ c := by
        intro hpne
        have hlt : p < 1 := lt_of_le_of_ne hp1 hpne
        have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
        have : (0 : ℤ) < ⌈(1 - p) * (k : ℝ)⌉ := Int.ceil_pos.mpr (mul_pos (by linarith) hkpos)
        omega
      -- pmf sums
      have pmf1 : ∀ f : PMF (Fin (n + 1)), ∑ v, (f v).toReal = 1 := by
        intro f
        rw [← ENNReal.toReal_sum (fun v _ => f.apply_ne_top v), ← tsum_fintype (L := .unconditional _), f.tsum_coe]
        simp
      -- existence of greedy committee
      have greedy : ∀ key : Fin m → ℕ, ∀ t, t ≤ m → ∃ T : Finset (Fin m), T.card = t ∧
          ∀ a ∈ T, ∀ b ∉ T, key b ≤ key a := by
        intro key t
        induction t with
        | zero => intro _; exact ⟨∅, by simp, by simp⟩
        | succ t ih =>
          intro ht
          obtain ⟨T, hT, hTk⟩ := ih (by omega)
          have hne : (Tᶜ).Nonempty := by
            rw [← Finset.card_pos, Finset.card_compl, hT, Fintype.card_fin]; omega
          obtain ⟨b, hb, hbm⟩ := Finset.exists_max_image Tᶜ key hne
          have hbT : b ∉ T := Finset.mem_compl.mp hb
          refine ⟨insert b T, by rw [Finset.card_insert_of_notMem hbT, hT], ?_⟩
          intro a ha y hy
          have hyT : y ∉ T := fun h => hy (Finset.mem_insert_of_mem h)
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hbm y (Finset.mem_compl.mpr hyT)
          · exact hTk a ha y hyT
      have cardsplit : ∀ T Hon : Finset (Fin m), (T ∩ Hon).card + (T \ Hon).card = T.card :=
        fun T Hon => Finset.card_inter_add_card_sdiff T Hon
      -- combinatorial characterisation
      have comb : 1 ≤ c → ∀ (Hon : Finset (Fin m)) (s : Fin m → Fin (n + 1)),
          CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ)) ↔
          ∃ x : Fin (n + 1), c ≤ (Hon.filter (fun j => x ≤ s j)).card ∧
            (Honᶜ.filter (fun j => x ≤ s j)).card < d := by
        intro hc1 Hon s
        constructor
        · intro hO
          obtain ⟨T, hT, hTk⟩ := greedy (fun j => 2 * (s j : ℕ) + if j ∈ Hon then 0 else 1) k hkm
          have hadm : CommitteeVoting.ExpConv.Admissible k (fun j => (s j : ℕ)) T := by
            refine ⟨hT, ?_⟩
            intro a ha b hb
            have := hTk a ha b hb
            dsimp only at this ⊢
            split_ifs at this <;> omega
          have h1 := hO T hadm
          rw [hcZ] at h1
          have h2 : c ≤ (T ∩ Hon).card := by exact_mod_cast h1
          have hne : (T ∩ Hon).Nonempty := by rw [← Finset.card_pos]; omega
          obtain ⟨h0, hh0, hmin⟩ := Finset.exists_min_image (T ∩ Hon) s hne
          have hh0' := Finset.mem_inter.mp hh0
          refine ⟨s h0, le_trans h2 (Finset.card_le_card ?_), ?_⟩
          · intro j hj
            exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hj).2, hmin j hj⟩
          · have hsub : (Honᶜ.filter (fun j => s h0 ≤ s j)) ⊆ T \ Hon := by
              intro j hj
              obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
              have hjH : j ∉ Hon := Finset.mem_compl.mp hj1
              refine Finset.mem_sdiff.mpr ⟨?_, hjH⟩
              by_contra hjT
              have h3 := hTk h0 hh0'.1 j hjT
              have h4 : (s h0 : ℕ) ≤ (s j : ℕ) := hj2
              simp only [hjH, hh0'.2, if_true, if_false] at h3
              omega
            have h5 := Finset.card_le_card hsub
            have h6 := cardsplit T Hon
            omega
        · rintro ⟨x, hx1, hx2⟩ T ⟨hT, hTk⟩
          rw [hcZ]
          by_contra hlt
          have hlt' : (T ∩ Hon).card < c := by
            have := not_le.mp hlt
            exact_mod_cast this
          obtain ⟨h, hh, hhT⟩ : ∃ h ∈ Hon.filter (fun j => x ≤ s j), h ∉ T := by
            by_contra hcon
            push Not at hcon
            have hsub : Hon.filter (fun j => x ≤ s j) ⊆ T ∩ Hon := fun j hj =>
              Finset.mem_inter.mpr ⟨hcon j hj, (Finset.mem_filter.mp hj).1⟩
            have := Finset.card_le_card hsub
            omega
          obtain ⟨t, ht, htx⟩ : ∃ t ∈ T \ Hon, ¬ x ≤ s t := by
            by_contra hcon
            push Not at hcon
            have hsub : T \ Hon ⊆ Honᶜ.filter (fun j => x ≤ s j) := fun j hj =>
              Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr (Finset.mem_sdiff.mp hj).2, hcon j hj⟩
            have h5 := Finset.card_le_card hsub
            have h6 := cardsplit T Hon
            omega
          have h7 : (s h : ℕ) ≤ (s t : ℕ) := hTk t (Finset.mem_sdiff.mp ht).1 h hhT
          exact htx (le_trans (Finset.mem_filter.mp hh).2 h7)
      -- indicator expansion
      have indic : 1 ≤ c → ∀ (Hon : Finset (Fin m)) (s : Fin m → Fin (n + 1)) (W : ℝ),
          (if CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ)) then W else 0) =
          ∑ x : Fin (n + 1),
            ((if (Hon.filter (fun j => x < s j)).card < c ∧
                (Honᶜ.filter (fun j => x ≤ s j)).card < d then W else 0) -
             (if (Hon.filter (fun j => x ≤ s j)).card < c ∧
                (Honᶜ.filter (fun j => x ≤ s j)).card < d then W else 0)) := by
        intro hc1 Hon s W
        have hgtge : ∀ x : Fin (n + 1), (Hon.filter (fun j => x < s j)).card ≤
            (Hon.filter (fun j => x ≤ s j)).card := fun x =>
          Finset.card_le_card (Finset.monotone_filter_right _ (fun j _ h => le_of_lt h))
        have hgegt : ∀ x y : Fin (n + 1), x < y → (Hon.filter (fun j => y ≤ s j)).card ≤
            (Hon.filter (fun j => x < s j)).card := fun x y hxy =>
          Finset.card_le_card (Finset.monotone_filter_right _ (fun j _ h => lt_of_lt_of_le hxy h))
        have hMmono : ∀ x y : Fin (n + 1), x ≤ y → (Honᶜ.filter (fun j => y ≤ s j)).card ≤
            (Honᶜ.filter (fun j => x ≤ s j)).card := fun x y hxy =>
          Finset.card_le_card (Finset.monotone_filter_right _ (fun j _ h => le_trans hxy h))
        by_cases hP : ∃ x : Fin (n + 1), c ≤ (Hon.filter (fun j => x ≤ s j)).card ∧
            (Honᶜ.filter (fun j => x ≤ s j)).card < d
        · rw [if_pos ((comb hc1 Hon s).mpr hP)]
          obtain ⟨y, hy1, hy2⟩ := hP
          obtain ⟨x0, hx0, hmax⟩ := Finset.exists_max_image
            (Finset.univ.filter (fun x : Fin (n + 1) => c ≤ (Hon.filter (fun j => x ≤ s j)).card))
            id ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy1⟩⟩
          have hx0c := (Finset.mem_filter.mp hx0).2
          have hmax' : ∀ z : Fin (n + 1), c ≤ (Hon.filter (fun j => z ≤ s j)).card → z ≤ x0 :=
            fun z hz => hmax z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
          have hMx0 := lt_of_le_of_lt (hMmono y x0 (hmax' y hy1)) hy2
          have hgt : (Hon.filter (fun j => x0 < s j)).card < c := by
            by_contra hcon
            have hne : (Hon.filter (fun j => x0 < s j)).Nonempty := by
              rw [← Finset.card_pos]; omega
            obtain ⟨j0, hj0, hjmin⟩ := Finset.exists_min_image _ s hne
            have hsub : (Hon.filter (fun j => x0 < s j)) ⊆ (Hon.filter (fun j => s j0 ≤ s j)) :=
              fun j hj => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, hjmin j hj⟩
            have h1 := Finset.card_le_card hsub
            have h2 := hmax' (s j0) (by omega)
            exact absurd (Finset.mem_filter.mp hj0).2 (not_lt.mpr h2)
          rw [Finset.sum_eq_single x0]
          · rw [if_pos ⟨hgt, hMx0⟩, if_neg (fun h => absurd h.1 (not_lt.mpr hx0c)), sub_zero]
          · intro x _ hx
            rcases lt_or_gt_of_ne hx with hlt | hgt'
            · have h1 := hgegt x x0 hlt
              have h2 := hgtge x
              rw [if_neg (fun h => by omega), if_neg (fun h => by omega), sub_zero]
            · have h1 : (Hon.filter (fun j => x ≤ s j)).card < c := by
                by_contra hcon
                exact absurd (hmax' x (not_lt.mp hcon)) (not_le.mpr hgt')
              have h2 := lt_of_le_of_lt (hgtge x) h1
              simp only [h1, h2, true_and, sub_self]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [if_neg (fun h => hP ((comb hc1 Hon s).mp h))]
          symm
          apply Finset.sum_eq_zero
          intro x _
          by_cases hM : (Honᶜ.filter (fun j => x ≤ s j)).card < d
          · have h1 : (Hon.filter (fun j => x ≤ s j)).card < c := by
              by_contra hcon
              exact hP ⟨x, not_lt.mp hcon, hM⟩
            have h2 := lt_of_le_of_lt (hgtge x) h1
            simp only [h1, h2, true_and, sub_self]
          · simp only [hM, and_false, if_false, sub_self]
      -- binomial partial sums over powersets
      have binsum : ∀ (S : Finset (Fin m)) (e : ℕ) (q r : ℝ),
          (∑ A ∈ S.powerset, if A.card < e then q ^ A.card * r ^ (S.card - A.card) else 0) =
          ∑ j ∈ Finset.range (min e (S.card + 1)), (Nat.choose S.card j : ℝ) * q ^ j *
            r ^ (S.card - j) := by
        intro S e q r
        rw [Finset.sum_powerset_apply_card
          (fun j => if j < e then q ^ j * r ^ (S.card - j) else 0)]
        have : Finset.range (min e (S.card + 1)) =
            (Finset.range (S.card + 1)).filter (fun j => j < e) := by
          ext j; simp [and_comm]
        rw [this, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j < e
        · simp only [hj, if_true, nsmul_eq_mul]; ring
        · simp [hj]
      -- main factorization
      have fact : ∀ (Hon : Finset (Fin m)) (QH QM : Fin (n + 1) → Prop) [DecidablePred QH]
          [DecidablePred QM] (c d : ℕ),
          (∑ s : Fin m → Fin (n + 1),
            if (Hon.filter (fun j => QH (s j))).card < c ∧
                (Honᶜ.filter (fun j => QM (s j))).card < d then
              ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0) =
          (∑ j ∈ Finset.range (min c (Hon.card + 1)), (Nat.choose Hon.card j : ℝ) *
              (∑ v ∈ Finset.univ.filter QH, (fh v).toReal) ^ j *
              (∑ v ∈ Finset.univ.filter (fun v => ¬ QH v), (fh v).toReal) ^ (Hon.card - j)) *
          (∑ j ∈ Finset.range (min d (Honᶜ.card + 1)), (Nat.choose Honᶜ.card j : ℝ) *
              (∑ v ∈ Finset.univ.filter QM, (fm v).toReal) ^ j *
              (∑ v ∈ Finset.univ.filter (fun v => ¬ QM v), (fm v).toReal) ^ (Honᶜ.card - j)) := by
        intro Hon QH QM _ _ c d
        rw [← binsum, ← binsum, Finset.sum_mul_sum, ← Finset.sum_product']
        -- fibre over the pair of exceedance sets
        rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
          (t := Hon.powerset ×ˢ Honᶜ.powerset)
          (g := fun s : Fin m → Fin (n + 1) =>
            (Hon.filter (fun j => QH (s j)), Honᶜ.filter (fun j => QM (s j))))
          (fun s _ => Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
            Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩)]
        apply Finset.sum_congr rfl
        rintro ⟨A, B⟩ hAB
        have hA : A ⊆ Hon := Finset.mem_powerset.mp (Finset.mem_product.mp hAB).1
        have hB : B ⊆ Honᶜ := Finset.mem_powerset.mp (Finset.mem_product.mp hAB).2
        have hfib : (Finset.univ.filter (fun s : Fin m → Fin (n + 1) =>
            (Hon.filter (fun j => QH (s j)), Honᶜ.filter (fun j => QM (s j))) = (A, B))) =
            Fintype.piFinset (fun j : Fin m => if j ∈ Hon then
              (if j ∈ A then Finset.univ.filter QH else Finset.univ.filter (fun v => ¬ QH v)) else
              (if j ∈ B then Finset.univ.filter QM else Finset.univ.filter (fun v => ¬ QM v))) := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
            Fintype.mem_piFinset]
          constructor
          · rintro ⟨rfl, rfl⟩ j
            by_cases hj : j ∈ Hon
            · by_cases hq : QH (s j) <;> simp [hj, hq]
            · by_cases hq : QM (s j) <;> simp [hj, hq]
          · intro h
            constructor
            · ext j
              have hj := h j
              by_cases hH : j ∈ Hon
              · by_cases hjA : j ∈ A
                · simpa [hH, hjA] using hj
                · simpa [hH, hjA] using hj
              · have : j ∉ A := fun h => hH (hA h)
                simp [hH, this]
            · ext j
              have hj := h j
              by_cases hH : j ∈ Hon
              · have : j ∉ B := fun h => (Finset.mem_compl.mp (hB h)) hH
                simp [hH, this]
              · by_cases hjB : j ∈ B
                · simpa [hH, hjB] using hj
                · simpa [hH, hjB] using hj
        have hstep : (∑ s ∈ Finset.univ.filter (fun s : Fin m → Fin (n + 1) =>
            (Hon.filter (fun j => QH (s j)), Honᶜ.filter (fun j => QM (s j))) = (A, B)),
            if (Hon.filter (fun j => QH (s j))).card < c ∧
                (Honᶜ.filter (fun j => QM (s j))).card < d then
              ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0) =
            if A.card < c ∧ B.card < d then
              ∑ s ∈ Finset.univ.filter (fun s : Fin m → Fin (n + 1) =>
                (Hon.filter (fun j => QH (s j)), Honᶜ.filter (fun j => QM (s j))) = (A, B)),
                ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0 := by
          have hcg : ∀ s ∈ Finset.univ.filter (fun s : Fin m → Fin (n + 1) =>
              (Hon.filter (fun j => QH (s j)), Honᶜ.filter (fun j => QM (s j))) = (A, B)),
              (if (Hon.filter (fun j => QH (s j))).card < c ∧
                (Honᶜ.filter (fun j => QM (s j))).card < d then
              ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0) =
              if A.card < c ∧ B.card < d then
              ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0 := by
            intro s hs
            have := (Finset.mem_filter.mp hs).2
            rw [Prod.mk.injEq] at this
            rw [this.1, this.2]
          rw [Finset.sum_congr rfl hcg]
          by_cases hAB' : A.card < c ∧ B.card < d
          · simp only [hAB', and_self, if_true]
          · simp only [hAB', if_false, Finset.sum_const_zero]
        rw [hstep, hfib]
        have hprod : (∑ s ∈ Fintype.piFinset (fun j : Fin m => if j ∈ Hon then
              (if j ∈ A then Finset.univ.filter QH else Finset.univ.filter (fun v => ¬ QH v)) else
              (if j ∈ B then Finset.univ.filter QM else Finset.univ.filter (fun v => ¬ QM v))),
                ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal)) =
            ((∑ v ∈ Finset.univ.filter QH, (fh v).toReal) ^ A.card *
              (∑ v ∈ Finset.univ.filter (fun v => ¬ QH v), (fh v).toReal) ^ (Hon.card - A.card)) *
            ((∑ v ∈ Finset.univ.filter QM, (fm v).toReal) ^ B.card *
              (∑ v ∈ Finset.univ.filter (fun v => ¬ QM v), (fm v).toReal) ^ (Honᶜ.card - B.card)) := by
          rw [← Finset.prod_univ_sum (fun j : Fin m => if j ∈ Hon then
              (if j ∈ A then Finset.univ.filter QH else Finset.univ.filter (fun v => ¬ QH v)) else
              (if j ∈ B then Finset.univ.filter QM else Finset.univ.filter (fun v => ¬ QM v)))
              (fun j v => if j ∈ Hon then (fh v).toReal else (fm v).toReal)]
          rw [← Finset.prod_mul_prod_compl Hon]
          have pw : ∀ (S A : Finset (Fin m)) (q r : ℝ), A ⊆ S →
              ∏ j ∈ S, (if j ∈ A then q else r) = q ^ A.card * r ^ (S.card - A.card) := by
            intro S A q r hAS
            rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
              Finset.inter_eq_right.mpr hAS, Finset.filter_notMem_eq_sdiff,
              Finset.card_sdiff_of_subset hAS]
          rw [← pw Hon A _ _ hA, ← pw Honᶜ B _ _ hB]
          congr 1
          · apply Finset.prod_congr rfl
            intro j hj
            by_cases hjA : j ∈ A <;> simp [hj, hjA]
          · apply Finset.prod_congr rfl
            intro j hj
            have hj := Finset.mem_compl.mp hj
            by_cases hjB : j ∈ B <;> simp [hj, hjB]
        rw [hprod]
        by_cases h1 : A.card < c <;> by_cases h2 : B.card < d <;> simp [h1, h2]
      -- tail sums
      have tail_le : ∀ (f : PMF (Fin (n + 1))) (x : Fin (n + 1)),
          (∑ v ∈ Finset.univ.filter (fun v => ¬ x < v), (f v).toReal) = voteCDF f x := by
        intro f x
        simp only [voteCDF, not_lt]
      have tail_gt : ∀ (f : PMF (Fin (n + 1))) (x : Fin (n + 1)),
          (∑ v ∈ Finset.univ.filter (fun v => x < v), (f v).toReal) = 1 - voteCDF f x := by
        intro f x
        have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => x < v)
          (fun v => (f v).toReal)
        rw [tail_le, pmf1] at h
        linarith
      have tail_ge : ∀ (f : PMF (Fin (n + 1))) (x : Fin (n + 1)),
          (∑ v ∈ Finset.univ.filter (fun v => x ≤ v), (f v).toReal) =
            1 - voteCDF f x + (f x).toReal := by
        intro f x
        have : Finset.univ.filter (fun v => x ≤ v) =
            insert x (Finset.univ.filter (fun v => x < v)) := by
          ext v; simp [le_iff_eq_or_lt, eq_comm]
        rw [this, Finset.sum_insert (by simp), tail_gt]; ring
      have tail_lt : ∀ (f : PMF (Fin (n + 1))) (x : Fin (n + 1)),
          (∑ v ∈ Finset.univ.filter (fun v => ¬ x ≤ v), (f v).toReal) =
            voteCDF f x - (f x).toReal := by
        intro f x
        have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => x ≤ v)
          (fun v => (f v).toReal)
        rw [tail_ge, pmf1] at h
        linarith
      -- total mass
      have total : ∀ Hon : Finset (Fin m), (∑ s : Fin m → Fin (n + 1),
          ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal)) = 1 := by
        intro Hon
        have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (Fin (n + 1))))
          (fun j v => if j ∈ Hon then (fh v).toReal else (fm v).toReal)
        rw [Fintype.piFinset_univ] at h
        rw [← h]
        apply Finset.prod_eq_one
        intro j _
        by_cases hj : j ∈ Hon <;> simp [hj, pmf1]
      -- conditional success probability
      obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, G = fun a => if m < a + d then 1 else
          if c ≤ a then ∑ x : Fin (n + 1), honestRankMass a c fh x * dishonestRankCDF (m - a) d fm x
          else 0 := ⟨_, rfl⟩
      have cond : 1 ≤ c → ∀ Hon : Finset (Fin m), (∑ s : Fin m → Fin (n + 1),
          if CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ)) then
            ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0) =
          G Hon.card := by
        intro hc1 Hon
        have hcc : Honᶜ.card = m - Hon.card := by rw [Finset.card_compl, Fintype.card_fin]
        have hHm : Hon.card ≤ m := by simpa using Finset.card_le_univ Hon
        rw [hG]
        dsimp only
        by_cases h1 : m < Hon.card + d
        · rw [if_pos h1, ← total Hon]
          apply Finset.sum_congr rfl
          intro s _
          rw [if_pos]
          refine (comb hc1 Hon s).mpr ⟨0, ?_, ?_⟩
          · simp; omega
          · simp only [Fin.zero_le, Finset.filter_true]; omega
        · rw [if_neg h1]
          by_cases h2 : c ≤ Hon.card
          · rw [if_pos h2]
            rw [Finset.sum_congr rfl (fun s _ => indic hc1 Hon s _), Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_sub_distrib, fact Hon (fun v => x < v) (fun v => x ≤ v) c d,
              fact Hon (fun v => x ≤ v) (fun v => x ≤ v) c d, tail_le, tail_gt, tail_ge, tail_lt,
              tail_ge, tail_lt, hcc, ← sub_mul, ← Finset.sum_sub_distrib]
            rw [honestRankMass, dishonestRankCDF]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            ring
          · rw [if_neg h2]
            apply Finset.sum_eq_zero
            intro s _
            rw [if_neg]
            intro h
            obtain ⟨x, hx, _⟩ := (comb hc1 Hon s).mp h
            have := Finset.card_filter_le Hon (fun j => x ≤ s j)
            omega
      -- assemble
      have hsucc : successProbability (m := m) k p fh fm =
          ∑ Hon : Finset (Fin m), p ^ Hon.card * (1 - p) ^ (m - Hon.card) * G Hon.card := by
        rw [successProbability]
        apply Finset.sum_congr rfl
        intro Hon _
        have hHm : Hon.card ≤ m := by simpa using Finset.card_le_univ Hon
        have hfac : (∑ s : Fin m → Fin (n + 1),
            if CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ))
            then jointWeight p fh fm Hon s else 0) =
            p ^ Hon.card * (1 - p) ^ (m - Hon.card) * (∑ s : Fin m → Fin (n + 1),
          if CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ)) then
            ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [mul_ite, mul_zero]
          rfl
        have hgoal : p ^ Hon.card * (1 - p) ^ (m - Hon.card) * (∑ s : Fin m → Fin (n + 1),
          if CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ)) then
            ∏ j : Fin m, (if j ∈ Hon then (fh (s j)).toReal else (fm (s j)).toReal) else 0) =
            p ^ Hon.card * (1 - p) ^ (m - Hon.card) * G Hon.card := by
          by_cases hp : p = 1
          · by_cases ha : Hon.card = m
            · have hc0 : c = 0 := by
                have : ⌈(1 - p) * (k : ℝ)⌉ = 0 := by rw [hp]; simp
                omega
              have hall : ∀ s : Fin m → Fin (n + 1),
                  CommitteeVoting.ExpConv.IsHonestOutcome k p Hon (fun j => (s j : ℕ)) := by
                intro s T _
                rw [hcZ, hc0]
                exact_mod_cast Nat.zero_le _
              simp only [hall, if_true]
              rw [total, hG]
              dsimp only
              rw [if_pos (by omega)]
            · have : (1 - p) ^ (m - Hon.card) = 0 := by
                rw [hp, sub_self, zero_pow (by omega)]
              rw [this]; ring
          · rw [cond (hc1 hp) Hon]
        exact hfac.trans hgoal
      rw [hsucc]
      have hpow := Finset.sum_powerset_apply_card
        (fun a => p ^ a * (1 - p) ^ (m - a) * G a) (x := (Finset.univ : Finset (Fin m)))
      rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at hpow
      rw [hpow, correctedFormula]
      rw [← hc, ← hd, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have ham : a ≤ m := by have := Finset.mem_range.mp ha; omega
      rw [hG]
      dsimp only
      rw [nsmul_eq_mul]
      have e1 : ((m : ℤ) - (d : ℤ) + 1 ≤ (a : ℤ)) ↔ m < a + d := by omega
      have e2 : ((a : ℤ) ≤ (m : ℤ) - (d : ℤ)) ↔ ¬ m < a + d := by omega
      simp only [e1, e2]
      by_cases h1 : m < a + d
      · simp only [h1, not_true, and_false, if_true, if_false]; ring
      · by_cases h2 : c ≤ a
        · simp only [h1, h2, not_false_eq_true, and_self, if_true, if_false]; ring
        · simp only [h1, h2, false_and, if_false]; ring
