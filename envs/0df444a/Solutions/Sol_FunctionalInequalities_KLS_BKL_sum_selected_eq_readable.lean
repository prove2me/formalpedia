-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.sum_selected_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:51.412359+00:00
-- url     : https://prove2.me/submissions/e62a6138-daf3-4d5d-a614-a780c7db7c1a

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S4Section6Pointwise
variable {n : ℕ}
section Masks
theorem FunctionalInequalities.KLS.BKL.selected_succ {E : Type*} {k : ℕ} (h : Fin (k+1) → E) (q : Fin (k+1) → Bool) :
    selected h q = if q 0 = true then h 0 :: selected (Fin.tail h) (Fin.tail q)
      else selected (Fin.tail h) (Fin.tail q) := by
  simp [selected]
theorem FunctionalInequalities.KLS.BKL.selected_zero {E : Type*} (h : Fin 0 → E) (q : Fin 0 → Bool) : selected h q = [] := by
  simp [selected]
theorem FunctionalInequalities.KLS.BKL.maskCount_succ {k : ℕ} (q : Fin (k+1) → Bool) :
    maskCount q = (if q 0 = true then 1 else 0) + maskCount (Fin.tail q) := by
  rw [maskCount, maskCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl
theorem FunctionalInequalities.KLS.BKL.maskCount_zero (q : Fin 0 → Bool) : maskCount q = 0 := by
  simp [maskCount]
theorem FunctionalInequalities.KLS.BKL.tail_not {k : ℕ} (q : Fin (k+1) → Bool) :
    Fin.tail (fun i => !(q i)) = fun i => !(Fin.tail q i) := rfl
theorem FunctionalInequalities.KLS.BKL.sum_cons_split {ι : Type*} [Fintype ι] {k : ℕ} (F : (Fin (k+1) → ι) → ℝ) :
    ∑ J : Fin (k+1) → ι, F J = ∑ j : ι, ∑ J' : Fin k → ι, F (Fin.cons j J') := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => ι)).sum_comp, Fintype.sum_prod_type]
  rfl
/-- Reindex a mask-selected sum as a double sum over the selected and the complementary slots. -/
theorem solution {E ι : Type*} [Fintype ι] (w : ι → E) :
    ∀ (k : ℕ) (q : Fin k → Bool) (G : List E → List E → ℝ) (c₁ c₂ : ℕ),
      FunctionalInequalities.KLS.BKL.maskCount q = c₁ → FunctionalInequalities.KLS.BKL.maskCount (fun i => !(q i)) = c₂ →
      ∑ J : Fin k → ι, G (FunctionalInequalities.Analysis.selected (fun i => w (J i)) q)
          (FunctionalInequalities.Analysis.selected (fun i => w (J i)) (fun i => !(q i))) =
        ∑ J₁ : Fin c₁ → ι, ∑ J₂ : Fin c₂ → ι,
          G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i)) := by
  intro k
  induction k with
  | zero =>
    intro q G c₁ c₂ h1 h2
    rw [FunctionalInequalities.KLS.BKL.maskCount_zero] at h1 h2
    subst h1
    subst h2
    simp [FunctionalInequalities.KLS.BKL.selected_zero, List.ofFn_zero]
  | succ k ih =>
    intro q G c₁ c₂ h1 h2
    rw [FunctionalInequalities.KLS.BKL.sum_cons_split]
    rw [FunctionalInequalities.KLS.BKL.maskCount_succ] at h1
    rw [FunctionalInequalities.KLS.BKL.maskCount_succ, FunctionalInequalities.KLS.BKL.tail_not] at h2
    have hsel : ∀ (j : ι) (J' : Fin k → ι) (p : Fin (k+1) → Bool),
        FunctionalInequalities.Analysis.selected (fun i => w ((Fin.cons j J' : Fin (k+1) → ι) i)) p =
          if p 0 = true then w j :: FunctionalInequalities.Analysis.selected (fun i => w (J' i)) (Fin.tail p)
            else FunctionalInequalities.Analysis.selected (fun i => w (J' i)) (Fin.tail p) := by
      intro j J' p
      have ht : Fin.tail (fun i => w ((Fin.cons j J' : Fin (k+1) → ι) i)) = fun i => w (J' i) := by
        funext i
        simp [Fin.tail]
      rw [FunctionalInequalities.KLS.BKL.selected_succ, ht]
      simp
    simp only [hsel, FunctionalInequalities.KLS.BKL.tail_not]
    cases hq : q 0 with
    | true =>
      simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2 ⊢
      rw [add_comm] at h1
      subst h1
      rw [FunctionalInequalities.KLS.BKL.sum_cons_split (k := FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ih (Fin.tail q) (fun l₁ l₂ => G (w j :: l₁) l₂) _ _ rfl h2]
      refine Finset.sum_congr rfl fun J₁ _ => ?_
      refine Finset.sum_congr rfl fun J₂ _ => ?_
      simp [List.ofFn_succ]
    | false =>
      simp only [hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte, zero_add] at h1 h2 ⊢
      rw [add_comm] at h2
      subst h1
      subst h2
      symm
      calc ∑ J₁ : Fin (FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q)) → ι,
            ∑ J₂ : Fin (FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i)) + 1) → ι,
              G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i))
          = ∑ J₁ : Fin (FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q)) → ι, ∑ j : ι,
            ∑ J₂ : Fin (FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i))) → ι,
              G (List.ofFn fun i => w (J₁ i)) (w j :: List.ofFn fun i => w (J₂ i)) := by
            refine Finset.sum_congr rfl fun J₁ _ => ?_
            rw [FunctionalInequalities.KLS.BKL.sum_cons_split]
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun J₂ _ => ?_
            simp [List.ofFn_succ]
        _ = ∑ j : ι, ∑ J₁ : Fin (FunctionalInequalities.KLS.BKL.maskCount (Fin.tail q)) → ι,
            ∑ J₂ : Fin (FunctionalInequalities.KLS.BKL.maskCount (fun i => !(Fin.tail q i))) → ι,
              G (List.ofFn fun i => w (J₁ i)) (w j :: List.ofFn fun i => w (J₂ i)) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [ih (Fin.tail q) (fun l₁ l₂ => G l₁ (w j :: l₂)) _ _ rfl rfl]
