-- Prove2me | solution 1 for CompanionTheory.D.LK.inj_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:24.104796+00:00
-- url     : https://prove2.me/submissions/421ee6bd-06d6-42c9-9442-f897620c379e

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
import Theorems.Thm_CompanionTheory_D_LK_filter_all
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Ft_apply
import Theorems.Thm_CompanionTheory_D_LK_differential_bounded_support
import Theorems.Thm_CompanionTheory_D_LK_differential_commutes_weight_operator
import Theorems.Thm_CompanionTheory_D_LK_sup_bd
import Theorems.Thm_CompanionTheory_D_LK_wt_om
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.LK
theorem _root_.solution (hV : VanK) (hP : WtProj) (hS : BdSq) : Inj := by
  intro n ε lam V _ _ E hl hgl hU hF hmin u y hu hy hb
  have hE : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hA : KRel (allT n) E := fun a b c d _ _ => hgl a b c d
  set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ
  have hc := differential_commutes_weight_operator n _ (allT n) V E (fun _ _ h => h) hA
  obtain ⟨-, -, -, s4⟩ := differential_bounded_support n ε V E
  have main : ∀ N (y : Cn n V), (∀ A, y A ≠ 0 → A.card = (om ε).card + 1 ∧ pot (A.filter fun i => ¬cpt ε i) < N) →
      Wt (allT n) E τ y → bd (allT n) E y = Pi.single (om ε) u → u = 0 := by
    intro N
    induction N with
    | zero =>
      intro y h _ hb
      obtain rfl : y = 0 := funext fun A => by by_contra h'; exact Nat.not_lt_zero _ (h A h').2
      simpa using (congrFun hb (om ε)).symm
    | succ N ih =>
      intro y h hw hb
      let r : Finset (Pos n) → Cn n V := fun B A => if (A.filter fun i => ¬cpt ε i) = B then y A else 0
      have hr : ∀ B, Sup ε B ((om ε).card + 1 - B.card) (r B) := fun B A hA => by
        obtain ⟨h1, h2⟩ : (A.filter fun i => ¬cpt ε i) = B ∧ y A ≠ 0 := by
          simp only [r] at hA
          split_ifs at hA with h1
          · exact ⟨h1, hA⟩
          · exact absurd rfl hA
        have := card_filter_add_card_filter_not (s := A) (cpt ε)
        have := (h A h2).1
        exact ⟨h1, by rw [← h1]; omega⟩
      have hsum : y = ∑ B, r B := funext fun A => by simp [r, Finset.sum_apply]
      have hrne : ∀ B A, r B A ≠ 0 → pot B < N + 1 ∧ B.Nonempty ∧ B.card ≤ (om ε).card + 1 := fun B A hA => by
        have h2 : y A ≠ 0 := fun h' => hA (by simp [r, h'])
        have h3 := (hr B A hA).1
        have h4 := h A h2
        refine ⟨h3 ▸ h4.2, nonempty_iff_ne_empty.2 fun hB => ?_, h4.1 ▸ h3 ▸ card_filter_le _ _⟩
        have : A ⊆ om ε := fun i hi => mem_filter.2 ⟨mem_univ _, by
          by_contra hc; exact notMem_empty i (hB ▸ h3 ▸ mem_filter.2 ⟨hi, hc⟩)⟩
        have := card_le_card this
        omega
      have hex : ∀ B, ∃ t : Cn n V, Wt (allT n) E τ t ∧ (pot B = N → bd ε E t = r B) ∧ (pot B ≠ N → t = 0) ∧
          (t = 0 ∨ (B.card ≤ (om ε).card + 1 ∧ Sup ε B ((om ε).card + 1 - B.card + 1) t)) := by
        intro B
        by_cases h0 : pot B = N ∧ r B ≠ 0
        · obtain ⟨A₀, hA₀⟩ := Function.ne_iff.1 h0.2
          obtain ⟨-, hBn, hBc⟩ := hrne B A₀ hA₀
          obtain ⟨t, t1, t2, t3⟩ := hV n ε lam V E hl hE hU hF hmin B _ (r B) hBn (hr B) (fun c => funext fun A => by
              have := congrFun (hw c) A
              simp only [Ft_apply, Pi.smul_apply, r] at this ⊢
              split_ifs
              · exact this
              · simp) (funext fun A => by
              by_contra hne
              have hAB := (sup_bd E (hr B) hne).1
              have e := congrFun hb A
              have hAo : A ≠ om ε := by
                rintro rfl
                obtain ⟨i, hi⟩ := hBn
                rw [← hAB] at hi
                exact (mem_filter.1 hi).2 (mem_filter.1 (mem_filter.1 hi).1).2
              rw [Pi.single_eq_of_ne hAo, hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single B] at e
              · apply hne
                by_contra h'
                have := (s4 B _ _ (hr B) A (by rw [Pi.sub_apply, e, zero_sub]; exact neg_ne_zero.2 hne)).1
                rw [hAB] at this
                exact lt_irrefl _ this
              · intro B' _ hB'
                by_cases h1 : r B' = 0
                · simp [h1]
                obtain ⟨A₁, hA₁⟩ := Function.ne_iff.1 h1
                have h2 := (hrne B' A₁ hA₁).1
                have h3 : bd ε E (r B') A = 0 := by
                  by_contra h3; exact hB' ((sup_bd E (hr B') h3).1.symm.trans hAB)
                by_contra h4
                have := (s4 B' _ _ (hr B') A (by rw [Pi.sub_apply, h3, sub_zero]; exact h4)).1
                rw [hAB] at this
                omega
              · simp)
          exact ⟨t, t2, fun _ => t3, fun h => absurd h0.1 h, Or.inr ⟨hBc, t1⟩⟩
        · refine ⟨0, fun c => by simp, fun h => ?_, fun _ => rfl, Or.inl rfl⟩
          rw [map_zero]
          by_contra h'
          exact h0 ⟨h, Ne.symm h'⟩
      choose t t1 t2 t3 t4 using hex
      refine ih (y - ∑ B, bd (allT n) E (t B)) (fun A hA => ?_) (fun c => ?_) ?_
      · have e : (y - ∑ B, bd (allT n) E (t B)) A =
            ∑ B, ((if pot B = N then 0 else r B A) - (bd (allT n) E (t B) - bd ε E (t B)) A) := by
          rw [Pi.sub_apply, congrFun hsum A, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun B _ => ?_
          split_ifs with h1
          · rw [Pi.sub_apply, t2 B h1]; abel
          · simp [t3 B h1]
        rw [e] at hA
        obtain ⟨B, -, hB⟩ := exists_ne_zero_of_sum_ne_zero hA
        by_cases h1 : pot B = N
        · rw [if_pos h1, zero_sub, neg_ne_zero] at hB
          rcases t4 B with h2 | h2
          · simp [h2] at hB
          · have := s4 B _ _ h2.2 A hB
            have := h2.1
            omega
        · rw [if_neg h1, t3 B h1] at hB
          have hB' : r B A ≠ 0 := by simpa using hB
          have h2 := (hrne B A hB').1
          have h3 := (hr B A hB').1
          exact ⟨(h A fun h' => hB' (by simp [r, h'])).1, by rw [h3]; omega⟩
      · rw [map_sub, map_sum, hw c, smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [← Module.End.mul_apply, (hc c).eq, Module.End.mul_apply, t1 B c, map_smul]
      · rw [map_sub, map_sum, hb, Finset.sum_eq_zero, sub_zero]
        exact fun B _ => LinearMap.congr_fun (hS n _ V E hA) _
  obtain ⟨y', y1, y2, y3⟩ := hP n (allT n) ε V E hE hU hF _ hc τ y (fun c => funext fun A => by
    rw [hb, Ft_apply, filter_all]
    by_cases e : A = om ε
    · subst e
      rw [Pi.smul_apply, Pi.single_eq_same, hu c, wt_om, ← add_smul, hτ]
      simp
    · simp [Pi.single_eq_of_ne e])
  refine main ((univ.sup fun A : Finset (Pos n) => pot A) + 1) y' (fun A hA => ⟨?_, ?_⟩) y1 (y2.trans hb)
  · have := (hy A fun h => hA (y3 A h)).2
    rwa [filter_all] at this
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := fun A : Finset (Pos n) => pot A) (mem_univ _))
end CompanionTheory.D.LK
