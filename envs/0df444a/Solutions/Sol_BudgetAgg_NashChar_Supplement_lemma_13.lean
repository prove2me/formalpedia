-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:49.114335+00:00
-- url     : https://prove2.me/submissions/79cb24e8-6d73-4c5f-bc0a-615fa3792ea5

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

/-- Lemma 13, p. 37: for `m = 2` and any admissible domain `U ⊆ U_SP`, two continuous
strategyproof mechanisms that agree on all single-minded profiles agree everywhere. -/
theorem solution {n : ℕ} [NeZero n] (U : Set (ℝ → ℝ)) (hU : IsSPDomain U)
    (f g : Mechanism2 n) (hf_cont : Continuous f) (hg_cont : Continuous g)
    (hf_sp : IsSP2 U f) (hg_sp : IsSP2 U g)
    (hagree : ∀ P, IsSingleMinded2 P → f P = g P) :
    ∀ P, f P = g P := by
      classical
      have mono : ∀ (u : ℝ → ℝ) (p : unitInterval), IsSinglePeakedAt u p →
          ∀ (y : unitInterval) (z : ℝ), ((p:ℝ) ≤ z ∧ z < y) ∨ ((y:ℝ) < z ∧ z ≤ p) → u y < u z := by
        intro u p hu y z hz
        have hyp : (y:ℝ) ≠ p := by
          rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro h <;> linarith
        by_cases hzp : z = p
        · subst hzp
          have := hu y hyp (1/2) (by norm_num) (by norm_num)
          linarith [this.1, this.2]
        · have hne : (y:ℝ) - p ≠ 0 := sub_ne_zero.mpr hyp
          have ht0 : 0 < ((y:ℝ) - z) / ((y:ℝ) - p) := by
            rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · apply div_pos <;> linarith
            · apply div_pos_of_neg_of_neg <;> linarith
          have ht1 : ((y:ℝ) - z) / ((y:ℝ) - p) < 1 := by
            rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [div_lt_one (by linarith)]
              have : (p:ℝ) < z := lt_of_le_of_ne h1 (Ne.symm hzp)
              linarith
            · rw [div_lt_one_of_neg (by linarith)]
              have : z < (p:ℝ) := lt_of_le_of_ne h2 hzp
              linarith
          have heq : ((y:ℝ) - z) / ((y:ℝ) - p) * p + (1 - ((y:ℝ) - z) / ((y:ℝ) - p)) * y = z := by
            field_simp; ring
          have := (hu y hyp _ ht0 ht1).2
          rwa [heq] at this
      have key : ∀ F : Mechanism2 n, Continuous F → IsSP2 U F → ∀ (P : Profile2 n) (i : Fin n),
          (F P : ℝ) = max (F (Function.update P i 0) : ℝ)
            (min (P i : ℝ) (F (Function.update P i 1) : ℝ)) := by
        intro F hFc hFsp P i
        let h : unitInterval → ℝ := fun x => (F (Function.update P i x) : ℝ)
        have hcont : Continuous h :=
          continuous_subtype_val.comp (hFc.comp (continuous_const.update i continuous_id))
        have hsp : ∀ (p x : unitInterval) (u : ℝ → ℝ), u ∈ U → IsSinglePeakedAt u p →
            u (h x) ≤ u (h p) := by
          intro p x u hu hpk
          have := hFsp i (Function.update P i p) x u hu (by simpa using hpk)
          simpa [h, Function.update_idem] using this
        have mono' : ∀ (x : unitInterval) (z : ℝ) (p : unitInterval) (u : ℝ → ℝ),
            IsSinglePeakedAt u p → ((p:ℝ) ≤ z ∧ z < h x) ∨ (h x < z ∧ z ≤ p) → u (h x) < u z :=
          fun x z p u hpk hz => mono u p hpk (F (Function.update P i x)) z hz
        have hnn : ∀ x, 0 ≤ h x := fun x => unitInterval.nonneg _
        have hle1 : ∀ x, h x ≤ 1 := fun x => unitInterval.le_one _
        have hP : (F P : ℝ) = h (P i) := by simp [h]
        have h0 : (F (Function.update P i 0) : ℝ) = h 0 := rfl
        have h1 : (F (Function.update P i 1) : ℝ) = h 1 := rfl
        rw [hP, h0, h1]
        have hlo : ∀ x, h 0 ≤ h x := by
          intro x
          by_contra hlt
          push_neg at hlt
          obtain ⟨u, hu, hpk⟩ := hU.2 0
          have e1 := hsp 0 x u hu hpk
          have e2 := mono' 0 (h x) 0 u hpk (Or.inl ⟨by simpa using hnn x, hlt⟩)
          linarith
        have hhi : ∀ x, h x ≤ h 1 := by
          intro x
          by_contra hlt
          push_neg at hlt
          obtain ⟨u, hu, hpk⟩ := hU.2 1
          have e1 := hsp 1 x u hu hpk
          have e2 := mono' 1 (h x) 1 u hpk (Or.inr ⟨hlt, by simpa using hle1 x⟩)
          linarith
        obtain ⟨u, hu, hpk⟩ := hU.2 (P i)
        have hab := hlo 1
        by_cases hpa : (P i : ℝ) < h 0
        · have hc : h (P i) = h 0 := by
            by_contra hne
            have hgt : h 0 < h (P i) := lt_of_le_of_ne (hlo _) (Ne.symm hne)
            have e1 := hsp (P i) 0 u hu hpk
            have e2 := mono' (P i) (h 0) (P i) u hpk (Or.inl ⟨hpa.le, hgt⟩)
            linarith
          rw [hc]
          have : min (P i : ℝ) (h 1) ≤ h 0 := (min_le_left _ _).trans hpa.le
          exact (max_eq_left this).symm
        by_cases hpb : h 1 < (P i : ℝ)
        · have hc : h (P i) = h 1 := by
            by_contra hne
            have hlt : h (P i) < h 1 := lt_of_le_of_ne (hhi _) hne
            have e1 := hsp (P i) 1 u hu hpk
            have e2 := mono' (P i) (h 1) (P i) u hpk (Or.inr ⟨hlt, hpb.le⟩)
            linarith
          rw [hc, min_eq_right hpb.le, max_eq_right hab]
        push_neg at hpa hpb
        obtain ⟨x, hx⟩ := intermediate_value_univ 0 1 hcont ⟨hpa, hpb⟩
        have hc : h (P i) = (P i : ℝ) := by
          by_contra hne
          have e1 := hsp (P i) x u hu hpk
          rw [hx] at e1
          have e2 := mono' (P i) (P i : ℝ) (P i) u hpk (by
            rcases lt_or_gt_of_ne hne with hl | hl
            · exact Or.inr ⟨hl, le_rfl⟩
            · exact Or.inl ⟨le_rfl, hl⟩)
          linarith
        rw [hc, min_eq_left hpb, max_eq_right hpa]
      have ind : ∀ S : Finset (Fin n), ∀ P : Profile2 n,
          (∀ i ∉ S, (P i : ℝ) = 0 ∨ (P i : ℝ) = 1) → f P = g P := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro P hP; exact hagree P (fun i => hP i (Finset.notMem_empty i))
        | insert j S hjS ih =>
          intro P hP
          have hsub : ∀ v : unitInterval, ((v : ℝ) = 0 ∨ (v : ℝ) = 1) →
              f (Function.update P j v) = g (Function.update P j v) := by
            intro v hv
            apply ih
            intro i hi
            by_cases hij : i = j
            · subst hij; simpa using hv
            · rw [Function.update_of_ne hij]
              exact hP i (by simp [hij, hi])
          have e0 := hsub 0 (Or.inl (by simp))
          have e1 := hsub 1 (Or.inr (by simp))
          apply Subtype.ext
          rw [key f hf_cont hf_sp P j, key g hg_cont hg_sp P j, e0, e1]
      intro P
      exact ind Finset.univ P (fun i hi => absurd (Finset.mem_univ i) hi)
