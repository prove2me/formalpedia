-- Prove2me | solution 1 for DynamicAssortment.Separation.separation_policy_regret_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:24:17.463943+00:00
-- url     : https://prove2.me/submissions/3e3daaaf-b0f6-47b6-91c0-2456ca5d11c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_History
import Definitions.Def_DynamicAssortment_Separation_SeparationPolicy
import Definitions.Def_DynamicAssortment_Separation_AssumptionOne
import Theorems.Thm_DynamicAssortment_Separation_step3_prob_nonoptimal_offer
import Theorems.Thm_DynamicAssortment_Separation_regret_le_sum_prob_nonoptimal
import Theorems.Thm_DynamicAssortment_Separation_choice_probabilities_sum_to_one

open DynamicAssortment.Separation

private theorem kernel_sum {α : Type} [Fintype α] :
    ∀ (T : ℕ) (q : (t : Fin T) → (Fin t.val → α) → α → ℝ),
    (∀ t pre, ∑ o, q t pre o = 1) →
    ∑ h : Fin T → α, ∏ t : Fin T, q t (fun u => h (Fin.castLE t.isLt.le u)) (h t) = 1 := by
  intro T
  induction T with
  | zero => intro q _; simp
  | succ T ih =>
    intro q hq
    rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have key : ∀ a : α, ∑ h' : Fin T → α, ∏ t : Fin T,
        q t.succ (fun u => (Fin.cons a h' : Fin (T+1) → α) (Fin.castLE t.succ.isLt.le u)) (h' t)
        = 1 := by
      intro a
      have := ih (fun t pre o => q t.succ (Fin.cons a pre) o) (fun t pre => hq _ _)
      rw [← this]
      refine Finset.sum_congr rfl fun h' _ => Finset.prod_congr rfl fun t _ => ?_
      congr 1
      funext u
      refine Fin.cases ?_ (fun v => ?_) u
      · rfl
      · rfl
    calc _ = ∑ a : α, q 0 (fun u => u.elim0) a * ∑ h' : Fin T → α, ∏ t : Fin T,
          q t.succ (fun u => (Fin.cons a h' : Fin (T+1) → α) (Fin.castLE t.succ.isLt.le u))
            (h' t) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h' _ => ?_
          congr 2
          funext u; exact u.elim0
      _ = 1 := by simp_rw [key, mul_one]; exact hq 0 _

private theorem noiseCDF_nonneg {f : ℝ → ℝ} (hf : IsNoiseDensity f) (x : ℝ) :
    0 ≤ noiseCDF f x :=
  MeasureTheory.setIntegral_nonneg measurableSet_Iic (fun y _ => (hf.pos y).le)

private theorem outcomeProb_nonneg {N : ℕ} {f : ℝ → ℝ} (hf : IsNoiseDensity f)
    (μ : Fin N → ℝ) (S : Finset (Fin N)) (o : Option (Fin N)) : 0 ≤ outcomeProb f μ S o := by
  cases o with
  | none =>
    exact MeasureTheory.integral_nonneg fun x =>
      mul_nonneg (Finset.prod_nonneg fun j _ => noiseCDF_nonneg hf _) (hf.pos x).le
  | some i =>
    show 0 ≤ choiceProb f μ S i
    unfold choiceProb
    split_ifs
    · exact MeasureTheory.integral_nonneg fun x =>
        mul_nonneg (mul_nonneg (Finset.prod_nonneg fun j _ => noiseCDF_nonneg hf _)
          (noiseCDF_nonneg hf _)) (hf.pos _).le
    · exact le_rfl

private theorem outcomeProb_sum {N : ℕ} {f : ℝ → ℝ} (hf : IsNoiseDensity f)
    (μ : Fin N → ℝ) (S : Finset (Fin N)) : ∑ o, outcomeProb f μ S o = 1 := by
  rw [Fintype.sum_option]
  have h1 := choice_probabilities_sum_to_one f hf μ S
  have h2 : ∑ i : Fin N, outcomeProb f μ S (some i) = ∑ i ∈ S, choiceProb f μ S i := by
    show ∑ i : Fin N, choiceProb f μ S i = _
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [choiceProb, hi]
  rw [h2]
  show noPurchaseProb f μ S + _ = 1
  linarith

private theorem prob_le_one {N T : ℕ} {f : ℝ → ℝ} (hf : IsNoiseDensity f)
    (μ : Fin N → ℝ) (π : Policy N T) (E : History N T → Prop) : prob f μ π E ≤ 1 := by
  classical
  have hsum : ∑ h : History N T, histProb f μ π h = 1 :=
    kernel_sum T (fun t pre o => outcomeProb f μ (π t pre) o) (fun t pre => outcomeProb_sum hf μ _)
  have hnn : ∀ h, 0 ≤ histProb f μ π h := fun h =>
    Finset.prod_nonneg fun t _ => outcomeProb_nonneg hf μ _ _
  unfold prob
  rw [← hsum]
  convert Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) =>
    (show (if E h then histProb f μ π h else 0) ≤ histProb f μ π h by
      split_ifs
      · exact le_rfl
      · exact hnn h))

private theorem testAssortment_card_le (N C j : ℕ) : (testAssortment N C j).card ≤ C := by
  have : ((testAssortment N C j).map ⟨Fin.val, Fin.val_injective⟩) ⊆
      Finset.Ico (j * C) ((j + 1) * C) := by
    intro x hx
    simp only [Finset.mem_map, testAssortment, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx
    obtain ⟨i, ⟨h1, h2⟩, rfl⟩ := hx
    simp [h1, h2]
  have := Finset.card_le_card this
  simp only [Finset.card_map, Nat.card_Ico] at this
  have e : (j + 1) * C - j * C = C := by rw [add_mul, one_mul, Nat.add_sub_cancel_left]
  omega

private theorem algorithm1_admissible {N C : ℕ} {f : ℝ → ℝ} {w : Fin N → ℝ}
    (opt : (Fin N → ℝ) → Finset (Fin N)) (hopt : IsOptimalSelection f w C opt)
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (κ₁ : ℝ) (T : ℕ) :
    IsAdmissible C (algorithm1 C opt eta κ₁ T) := by
  intro t pre
  unfold algorithm1
  rw [separationAssortment]
  split_ifs
  · exact testAssortment_card_le N C _
  · exact (Finset.mem_filter.mp (hopt.mem _)).2

theorem solution {N C : ℕ} (hC : 1 ≤ C) (hCN : C ≤ N)
    (f : ℝ → ℝ) (hf : IsNoiseDensity f) (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (μ : Fin N → ℝ) (opt : (Fin N → ℝ) → Finset (Fin N))
    (hopt : IsOptimalSelection f w C opt) (huniq : UniqueOptimum f w C μ (opt μ))
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) (hid : Identifiability f C eta) :
    ∃ Kbar₁ κbar₁ : ℝ, ∀ κ₁ : ℝ, 0 < κ₁ → κbar₁ < κ₁ → ∀ T : ℕ,
      regret f w μ (opt μ) (algorithm1 C opt eta κ₁ T) ≤
        κ₁ * (numTests N C : ℝ) * Real.log T + Kbar₁ := by
  obtain ⟨c, hc, hstep⟩ := step3_prob_nonoptimal_offer hC hCN f hf w hw μ opt hopt huniq eta hid
  set A : ℝ := ∑ j ∈ Finset.range (numTests N C), 2 * ((testAssortment N C j).card : ℝ)
    with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨(numTests N C : ℝ) + A, 1 / c, ?_⟩
  intro κ₁ hκ hκc T
  set π := algorithm1 C opt eta κ₁ T with hπ
  have hreg := regret_le_sum_prob_nonoptimal (T := T) hC hCN f hf w hw μ opt hopt π
    (algorithm1_admissible opt hopt eta κ₁ T)
  set E := numTests N C * ⌈κ₁ * Real.log T⌉₊ with hE
  set B : ℝ := ∑ j ∈ Finset.range (numTests N C),
    2 * ((testAssortment N C j).card : ℝ) * (T : ℝ) ^ (-(κ₁ * c)) with hB
  have hBA : B = A * (T : ℝ) ^ (-(κ₁ * c)) := by rw [hB, hA, Finset.sum_mul]
  have hB0 : 0 ≤ B := by rw [hBA]; exact mul_nonneg hA0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hP : ∀ t : Fin T, prob f μ π (fun h => offeredAt π h t ≠ opt μ) ≤
      (if t.val < E then (1 : ℝ) else 0) + B := by
    intro t
    by_cases ht : t.val < E
    · rw [if_pos ht]; linarith [prob_le_one hf μ π (fun h => offeredAt π h t ≠ opt μ)]
    · rw [if_neg ht, zero_add]
      have := hstep κ₁ hκ T t.val (by omega) t.isLt
      have e : (fun h => offeredSeq π h t.val ≠ opt μ) = (fun h => offeredAt π h t ≠ opt μ) := by
        funext h; simp [offeredSeq, t.isLt]
      rw [← e]; exact this
  have hsum1 : ∑ t : Fin T, (if t.val < E then (1 : ℝ) else 0) ≤ E := by
    rw [Fin.sum_univ_eq_sum_range (fun t => if t < E then (1 : ℝ) else 0) T, Finset.sum_boole]
    have : (Finset.range T).filter (fun t => t < E) ⊆ Finset.range E := by
      intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢; exact hx.2
    exact_mod_cast Finset.card_le_card this |>.trans (by simp)
  have hlog : 0 ≤ Real.log T := Real.log_natCast_nonneg T
  have hE' : (E : ℝ) ≤ numTests N C * (κ₁ * Real.log T + 1) := by
    rw [hE]; push_cast
    exact mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one (by positivity)).le (by positivity)
  have hTB : (T : ℝ) * B ≤ A := by
    rw [hBA]
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · simp [h0, hA0]
    · have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hpos
      have hexp : -(κ₁ * c) ≤ -1 := by
        have : 1 / c * c < κ₁ * c := mul_lt_mul_of_pos_right hκc hc
        rw [one_div, inv_mul_cancel₀ hc.ne'] at this
        linarith
      have h1 : (T : ℝ) ^ (-(κ₁ * c)) ≤ (T : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 hexp
      have h2 : (T : ℝ) * (T : ℝ) ^ (-1 : ℝ) = 1 := by
        rw [Real.rpow_neg_one]; field_simp
      calc (T : ℝ) * (A * (T : ℝ) ^ (-(κ₁ * c))) = A * ((T : ℝ) * (T : ℝ) ^ (-(κ₁ * c))) := by ring
        _ ≤ A * ((T : ℝ) * (T : ℝ) ^ (-1 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = A := by rw [h2, mul_one]
  calc regret f w μ (opt μ) π ≤ ∑ t : Fin T, prob f μ π (fun h => offeredAt π h t ≠ opt μ) := hreg
    _ ≤ ∑ t : Fin T, ((if t.val < E then (1 : ℝ) else 0) + B) := Finset.sum_le_sum fun t _ => hP t
    _ = ∑ t : Fin T, (if t.val < E then (1 : ℝ) else 0) + T * B := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ numTests N C * (κ₁ * Real.log T + 1) + A := by linarith
    _ = κ₁ * (numTests N C : ℝ) * Real.log T + ((numTests N C : ℝ) + A) := by ring
