-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:12.713842+00:00
-- url     : https://prove2.me/submissions/3ef2c375-f8ce-410d-b23f-2af9cb47fb69

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

/-- Lemma 12, p. 36: for `m = 2`, `n = 1` and any admissible domain `U ⊆ U_SP`, a
mechanism is continuous and strategyproof iff it is `p ↦ med(p, α₀, α₁)` for some
`0 ≤ α₀ ≤ α₁ ≤ 1`. -/
theorem solution (U : Set (ℝ → ℝ)) (hU : IsSPDomain U) (f : Mechanism2 1) :
    (Continuous f ∧ IsSP2 U f) ↔
      ∃ α₀ α₁ : ℝ, 0 ≤ α₀ ∧ α₀ ≤ α₁ ∧ α₁ ≤ 1 ∧
        ∀ P : Profile2 1, (f P : ℝ) = genMedian ![α₀, α₁] P := by
          classical
          have hpeak : ∀ (u : ℝ → ℝ) (p q : unitInterval),
              IsSinglePeakedAt u p → (q : ℝ) ≠ p → u q < u p := by
            intro u p q hu hq
            obtain ⟨h₁, h₂⟩ := hu q hq (1 / 2) (by norm_num) (by norm_num)
            exact h₂.trans h₁
          have hbetter : ∀ (u : ℝ → ℝ) (p x y : unitInterval),
              IsSinglePeakedAt u p →
              ((x : ℝ) < y ∧ (y : ℝ) ≤ p ∨ (p : ℝ) ≤ y ∧ (y : ℝ) < x) →
              u x < u y := by
            intro u p x y hu hxy
            by_cases hyp : (y : ℝ) = p
            · rw [hyp]
              apply hpeak u p x hu
              rcases hxy with h | h <;> linarith
            rcases hxy with ⟨hxy, hyp'⟩ | ⟨hpy, hyx⟩
            · have hxp : (x : ℝ) < p := lt_of_lt_of_le hxy hyp'
              have hyt : (y : ℝ) < p := lt_of_le_of_ne hyp' hyp
              have ht0 : 0 < ((y : ℝ) - x) / ((p : ℝ) - x) :=
                div_pos (sub_pos.mpr hxy) (sub_pos.mpr hxp)
              have ht1 : ((y : ℝ) - x) / ((p : ℝ) - x) < 1 :=
                (div_lt_one (sub_pos.mpr hxp)).mpr (by linarith)
              have he : (((y : ℝ) - x) / ((p : ℝ) - x)) * p +
                  (1 - ((y : ℝ) - x) / ((p : ℝ) - x)) * x = y := by
                field_simp [ne_of_gt (sub_pos.mpr hxp)]
                <;> ring
              simpa only [he] using (hu x (ne_of_lt hxp) _ ht0 ht1).2
            · have hpx : (p : ℝ) < x := lt_of_le_of_lt hpy hyx
              have hpt : (p : ℝ) < y := lt_of_le_of_ne hpy (Ne.symm hyp)
              have ht0 : 0 < ((x : ℝ) - y) / ((x : ℝ) - p) :=
                div_pos (sub_pos.mpr hyx) (sub_pos.mpr hpx)
              have ht1 : ((x : ℝ) - y) / ((x : ℝ) - p) < 1 :=
                (div_lt_one (sub_pos.mpr hpx)).mpr (by linarith)
              have he : (((x : ℝ) - y) / ((x : ℝ) - p)) * p +
                  (1 - ((x : ℝ) - y) / ((x : ℝ) - p)) * x = y := by
                field_simp [ne_of_gt (sub_pos.mpr hpx)]
                <;> ring
              simpa only [he] using (hu x (ne_of_gt hpx) _ ht0 ht1).2
          have hweak : ∀ (u : ℝ → ℝ) (p x y : unitInterval),
              IsSinglePeakedAt u p →
              ((x : ℝ) ≤ y ∧ (y : ℝ) ≤ p ∨ (p : ℝ) ≤ y ∧ (y : ℝ) ≤ x) →
              u x ≤ u y := by
            intro u p x y hu hxy
            by_cases he : (x : ℝ) = y
            · simp [he]
            apply le_of_lt (hbetter u p x y hu ?_)
            rcases hxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
            · exact Or.inl ⟨lt_of_le_of_ne h₁ he, h₂⟩
            · exact Or.inr ⟨h₁, lt_of_le_of_ne h₂ (Ne.symm he)⟩
          have hmedian : ∀ (a b : ℝ), a ≤ b → ∀ P : Profile2 1,
              genMedian ![a, b] P = max a (min (P 0 : ℝ) b) := by
            intro a b hab P
            have he : (Finset.univ : Finset (Fin 1 ⊕ Fin 2)) =
                {Sum.inl 0, Sum.inr 0, Sum.inr 1} := by
              ext x
              rcases x with x | x <;> fin_cases x <;> simp
            have hm : Finset.univ.val.map (Sum.elim (fun i : Fin 1 => (P i : ℝ)) ![a, b]) =
                (P 0 : ℝ) ::ₘ a ::ₘ {b} := by
              simp [he, Finset.insert_val, Finset.singleton_val]
            have hs : ∀ x y z : ℝ, x ≤ y → y ≤ z →
                ((x ::ₘ y ::ₘ {z}).sort (· ≤ ·)).getD 1 0 = y := by
              intro x y z hxy hyz
              have hh : x ::ₘ y ::ₘ ({z} : Multiset ℝ) = ([x,y,z] : List ℝ) := rfl
              rw [hh, Multiset.coe_sort, List.mergeSort_eq_self]
              · rfl
              · simp [List.pairwise_cons, hxy, hyz, hxy.trans hyz]
            unfold genMedian med
            rw [hm]
            change (((P 0 : ℝ) ::ₘ a ::ₘ {b}).sort (· ≤ ·)).getD 1 0 = _
            by_cases hpa : (P 0 : ℝ) ≤ a
            · rw [hs _ _ _ hpa hab, min_eq_left (hpa.trans hab), max_eq_left hpa]
            by_cases hbp : b ≤ (P 0 : ℝ)
            · have hp : (P 0 : ℝ) ::ₘ a ::ₘ ({b} : Multiset ℝ) = a ::ₘ b ::ₘ {(P 0 : ℝ)} := by
                change (P 0 : ℝ) ::ₘ a ::ₘ b ::ₘ 0 = a ::ₘ b ::ₘ (P 0 : ℝ) ::ₘ 0
                rw [Multiset.cons_swap (P 0 : ℝ) a, Multiset.cons_swap (P 0 : ℝ) b]
              rw [hp, hs _ _ _ hab hbp, min_eq_right hbp, max_eq_right hab]
            · have hp : (P 0 : ℝ) ::ₘ a ::ₘ ({b} : Multiset ℝ) = a ::ₘ (P 0 : ℝ) ::ₘ {b} :=
                Multiset.cons_swap _ _ _
              rw [hp, hs _ _ _ (le_of_not_ge hpa) (le_of_not_ge hbp),
                min_eq_left (le_of_not_ge hbp), max_eq_right (le_of_not_ge hpa)]
          constructor
          · rintro ⟨hc, hsp⟩
            let g : unitInterval → unitInterval := fun p => f (fun _ => p)
            have hgc : Continuous (fun p : unitInterval => (g p : ℝ)) :=
              continuous_subtype_val.comp (hc.comp (continuous_pi fun _ => continuous_id))
            have hsingle : ∀ P : Profile2 1, P = fun _ => P 0 := by
              intro P
              funext i
              have hi : i = 0 := Subsingleton.elim _ _
              simp [hi]
            have hgs : ∀ (p q : unitInterval) (u : ℝ → ℝ), u ∈ U →
                IsSinglePeakedAt u p → u (g q) ≤ u (g p) := by
              intro p q u hu hup
              have he : Function.update (fun _ : Fin 1 => p) 0 q = fun _ => q := by
                funext i
                have hi : i = 0 := Subsingleton.elim _ _
                simp [hi]
              simpa only [g, he] using hsp 0 (fun _ => p) q u hu hup
            have hbds : ∀ p : unitInterval, (g 0 : ℝ) ≤ g p ∧ (g p : ℝ) ≤ g 1 := by
              intro p
              constructor
              · by_contra hn
                have hlt : (g p : ℝ) < g 0 := lt_of_not_ge hn
                obtain ⟨u, hu, hup⟩ := hU.2 0
                have hu' := hbetter u 0 (g 0) (g p) hup (Or.inr ⟨(g p).property.1, hlt⟩)
                exact (not_lt_of_ge (hgs 0 p u hu hup)) hu'
              · by_contra hn
                have hlt : (g 1 : ℝ) < g p := lt_of_not_ge hn
                obtain ⟨u, hu, hup⟩ := hU.2 1
                have hu' := hbetter u 1 (g 1) (g p) hup (Or.inl ⟨hlt, (g p).property.2⟩)
                exact (not_lt_of_ge (hgs 1 p u hu hup)) hu'
            have hab : (g 0 : ℝ) ≤ g 1 := (hbds 1).1
            have hclamp : ∀ p : unitInterval, (g p : ℝ) = max (g 0 : ℝ) (min (p : ℝ) (g 1 : ℝ)) := by
              intro p
              obtain ⟨u, hu, hup⟩ := hU.2 p
              by_cases hpa : (p : ℝ) ≤ g 0
              · rw [min_eq_left (hpa.trans hab), max_eq_left hpa]
                apply le_antisymm _ (hbds p).1
                by_contra hn
                have hlt : (g 0 : ℝ) < g p := lt_of_not_ge hn
                have hu' := hbetter u p (g p) (g 0) hup (Or.inr ⟨hpa, hlt⟩)
                exact (not_lt_of_ge (hgs p 0 u hu hup)) hu'
              by_cases hbp : (g 1 : ℝ) ≤ p
              · rw [min_eq_right hbp, max_eq_right hab]
                apply le_antisymm (hbds p).2
                by_contra hn
                have hlt : (g p : ℝ) < g 1 := lt_of_not_ge hn
                have hu' := hbetter u p (g p) (g 1) hup (Or.inl ⟨hlt, hbp⟩)
                exact (not_lt_of_ge (hgs p 1 u hu hup)) hu'
              · rw [min_eq_left (le_of_not_ge hbp), max_eq_right (le_of_not_ge hpa)]
                obtain ⟨q, hq⟩ := intermediate_value_univ (0 : unitInterval) 1 hgc
                  ⟨le_of_not_ge hpa, le_of_not_ge hbp⟩
                by_contra hn
                have hu' := hpeak u p (g p) hup hn
                have hs := hgs p q u hu hup
                change (g q : ℝ) = (p : ℝ) at hq
                rw [hq] at hs
                exact (not_lt_of_ge hs) hu'
            refine ⟨g 0, g 1, (g 0).property.1, hab, (g 1).property.2, ?_⟩
            intro P
            rw [hmedian _ _ hab]
            rw [hsingle P]
            exact hclamp (P 0)
          · rintro ⟨a, b, ha, hab, hb, hf⟩
            have hform : ∀ P : Profile2 1, (f P : ℝ) = max a (min (P 0 : ℝ) b) := by
              intro P
              rw [hf P, hmedian _ _ hab]
            have hfc : Continuous (fun P : Profile2 1 => (f P : ℝ)) := by
              simp_rw [hform]
              exact continuous_const.max ((continuous_subtype_val.comp (continuous_apply 0)).min continuous_const)
            refine ⟨continuous_induced_rng.mpr hfc, ?_⟩
            intro i P q u hu hup
            have hi : i = 0 := Subsingleton.elim _ _
            subst i
            have hr : a ≤ (f (Function.update P 0 q) : ℝ) ∧
                (f (Function.update P 0 q) : ℝ) ≤ b := by
              rw [hform]
              exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
            apply hweak u (P 0) (f (Function.update P 0 q)) (f P) hup
            by_cases hpa : (P 0 : ℝ) ≤ a
            · right
              rw [hform P, min_eq_left (hpa.trans hab), max_eq_left hpa]
              exact ⟨hpa, hr.1⟩
            by_cases hbp : b ≤ (P 0 : ℝ)
            · left
              rw [hform P, min_eq_right hbp, max_eq_right hab]
              exact ⟨hr.2, hbp⟩
            · rw [hform P, min_eq_left (le_of_not_ge hbp), max_eq_right (le_of_not_ge hpa)]
              exact le_total (f (Function.update P 0 q) : ℝ) (P 0) |>.elim
                (fun h => Or.inl ⟨h, le_rfl⟩) (fun h => Or.inr ⟨le_rfl, h⟩)
