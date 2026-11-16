-- Prove2me | solution 1 for CritWinSpin.p7b_lemma_7_1_from_theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T22:05:04.928354+00:00
-- url     : https://prove2.me/submissions/72c3d0fe-7b13-4e10-93dd-4c690caf8416

import Mathlib
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_BinarySource
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
open QAlgorithms.Complexity QuantumPRC
open scoped BigOperators

namespace CritWinSpin

/-- Split a function on `Fin T` at coordinate `i` into `(f i, f_{-i})`. -/
def L71_splitEquiv {T : ℕ} {α : Type} (i : Fin T) :
    (Fin T → α) ≃ α × ({t : Fin T // t ≠ i} → α) where
  toFun f := (f i, fun t => f t.1)
  invFun p t := if h : t = i then p.1 else p.2 ⟨t, h⟩
  left_inv f := by
    ext t
    by_cases h : t = i <;> simp [h]
  right_inv p := by
    rcases p with ⟨p1, p2⟩
    ext t
    · simp
    · simp [t.2]

lemma L71_prod_split {T : ℕ} {α : Type} (i : Fin T) (f : Fin T → α → ℝ) (x : Fin T → α) :
    (∏ t : Fin T, f t (x t)) = f i (x i) * ∏ t : {t : Fin T // t ≠ i}, f t.1 (x t.1) := by
  classical
  have h := Finset.prod_mul_prod_compl (s := ({i} : Finset (Fin T))) (f := fun t => f t (x t))
  rw [Finset.prod_singleton] at h
  rw [← h]
  congr 1
  refine Finset.prod_bij (fun (t : Fin T) (ht : t ∈ ({i} : Finset (Fin T))ᶜ) =>
      (⟨t, by simpa using ht⟩ : {t : Fin T // t ≠ i})) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro a _ b _ hab
    exact congrArg Subtype.val hab
  · intro b _
    exact ⟨b.1, by simpa using b.2, Subtype.ext rfl⟩
  · intro _ _
    rfl

lemma L71_finRange_split {T : ℕ} (i : Fin T) :
    List.finRange T = (List.finRange T).take i.1 ++ i :: (List.finRange T).drop (i.1 + 1) := by
  have hi : i.1 < (List.finRange T).length := by simp
  have htake : List.finRange T = (List.finRange T).take i.1 ++ (List.finRange T).drop i.1 :=
    (List.take_append_drop i.1 (List.finRange T)).symm
  have hdrop : (List.finRange T).drop i.1 =
      (List.finRange T)[i.1] :: (List.finRange T).drop (i.1 + 1) :=
    List.drop_eq_getElem_cons hi
  have hget : (List.finRange T)[i.1] = i := by simp
  conv_lhs => rw [htake, hdrop, hget]

lemma L71_mem_take_finRange_ne {T : ℕ} (i : Fin T) {t : Fin T}
    (ht : t ∈ (List.finRange T).take i.1) : t ≠ i := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
  have hklt : k < i.1 := by
    have hlen : ((List.finRange T).take i.1).length ≤ i.1 := List.length_take_le i.1 (List.finRange T)
    omega
  have hkT : k < (List.finRange T).length := by
    have hlenT : (List.finRange T).length = T := List.length_finRange
    have hiT : i.1 < T := i.2
    omega
  have hget : ((List.finRange T).take i.1)[k] = (List.finRange T)[k]'hkT :=
    List.getElem_take
  rw [hget]
  intro heq
  have hval := congrArg Fin.val heq
  simp at hval
  omega

lemma L71_mem_drop_finRange_ne {T : ℕ} (i : Fin T) {t : Fin T}
    (ht : t ∈ (List.finRange T).drop (i.1 + 1)) : t ≠ i := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
  have hlen : ((List.finRange T).drop (i.1 + 1)).length = (List.finRange T).length - (i.1 + 1) :=
    List.length_drop
  have hkT : i.1 + 1 + k < (List.finRange T).length := by omega
  have hget : ((List.finRange T).drop (i.1 + 1))[k] = (List.finRange T)[i.1 + 1 + k]'hkT :=
    List.getElem_drop
  rw [hget]
  intro heq
  have hval := congrArg Fin.val heq
  simp only [List.getElem_finRange] at hval
  have h1 : i.1 + 1 + k < T := by
    have hlenT : (List.finRange T).length = T := List.length_finRange
    omega
  simp only [Fin.val_cast] at hval
  omega

lemma L71_lhatRun_erase {α : Type} {T k : ℕ} (i : Fin T)
    (ω' : {t : Fin T // t ≠ i} → Option α) (o : Option α) (R : Fin k → Fin T × α)
    (hR : lhatRun k ((L71_splitEquiv i).symm (o, ω')) = some R)
    (hne : ∀ j : Fin k, (R j).1 ≠ i) :
    lhatRun k ((L71_splitEquiv i).symm (none, ω')) = some R := by
  cases o with
  | none => exact hR
  | some a =>
    let ω := (L71_splitEquiv i).symm (some a, ω')
    let ω0 := (L71_splitEquiv i).symm (none, ω')
    let f : (Fin T → Option α) → Fin T → Option (Fin T × α) :=
      fun w t => (w t).map fun b => (t, b)
    have htake_eq : ((List.finRange T).take i.1).filterMap (f ω) =
        ((List.finRange T).take i.1).filterMap (f ω0) := by
      apply List.filterMap_congr
      intro t ht
      have htne : t ≠ i := L71_mem_take_finRange_ne i ht
      simp [f, ω, ω0, L71_splitEquiv, htne]
    have hdrop_eq : ((List.finRange T).drop (i.1 + 1)).filterMap (f ω) =
        ((List.finRange T).drop (i.1 + 1)).filterMap (f ω0) := by
      apply List.filterMap_congr
      intro t ht
      have htne : t ≠ i := L71_mem_drop_finRange_ne i ht
      simp [f, ω, ω0, L71_splitEquiv, htne]
    let l₁ := ((List.finRange T).take i.1).filterMap (f ω0)
    let l₂ := ((List.finRange T).drop (i.1 + 1)).filterMap (f ω0)
    have hl : (List.finRange T).filterMap (f ω) = l₁ ++ (i, a) :: l₂ := by
      conv_lhs => rw [L71_finRange_split i]
      rw [List.filterMap_append, List.filterMap_cons]
      have hfi : f ω i = some (i, a) := by simp [f, ω, L71_splitEquiv]
      rw [hfi, htake_eq, hdrop_eq]
    have hl0 : (List.finRange T).filterMap (f ω0) = l₁ ++ l₂ := by
      conv_lhs => rw [L71_finRange_split i]
      rw [List.filterMap_append, List.filterMap_cons]
      have hfi : f ω0 i = none := by simp [f, ω0, L71_splitEquiv]
      rw [hfi]
    unfold lhatRun at hR ⊢
    change (if h : k ≤ ((List.finRange T).filterMap (f ω)).length then
        some fun (j : Fin k) => ((List.finRange T).filterMap (f ω)).get ⟨j.1, lt_of_lt_of_le j.2 h⟩
      else none) = some R at hR
    change (if h : k ≤ ((List.finRange T).filterMap (f ω0)).length then
        some fun (j : Fin k) => ((List.finRange T).filterMap (f ω0)).get ⟨j.1, lt_of_lt_of_le j.2 h⟩
      else none) = some R
    rw [hl] at hR
    rw [hl0]
    split_ifs at hR with hk
    · simp only [Option.some.injEq] at hR
      have hk1 : k ≤ l₁.length := by
        by_contra hlt
        have hlt' : l₁.length < k := lt_of_not_ge hlt
        let j0 : Fin k := ⟨l₁.length, hlt'⟩
        have hRj0 : R j0 = (l₁ ++ (i, a) :: l₂).get ⟨l₁.length, lt_of_lt_of_le j0.2 hk⟩ := by
          rw [← hR]
        have hget_ia : (l₁ ++ (i, a) :: l₂).get ⟨l₁.length, lt_of_lt_of_le j0.2 hk⟩ = (i, a) := by
          simp
        have hfst : (R j0).1 = i := by
          rw [hRj0, hget_ia]
        exact hne j0 hfst
      have hk0 : k ≤ (l₁ ++ l₂).length := by
        rw [List.length_append]
        omega
      rw [dif_pos hk0]
      congr 1
      funext j
      rw [← hR]
      have hj1 : j.1 < l₁.length := lt_of_lt_of_le j.2 hk1
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left hj1, List.getElem_append_left hj1]

lemma L71_omega_card_pos {n d : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (hΨ : ∀ m₀ : Fin d → Bool, ∑ y, unifOn Ω y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) :
    0 < Ω.card := by
  by_contra hc
  have hc0 : Ω.card = 0 := by omega
  let m₀ : Fin d → Bool := fun _ => false
  have hz : (∑ y, unifOn Ω y * (if Ψ y = m₀ then (1 : ℝ) else 0)) = (0 : ℝ) := by
    simp [unifOn, hc0]
  have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ d :=
    one_div_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) d)
  have heq := hΨ m₀
  rw [← heq] at hpos
  linarith

lemma L71_sum_unifOn_eq_one {α : Type} [Fintype α] [DecidableEq α] (Ω : Finset α)
    (hcard : 0 < Ω.card) :
    (∑ y : α, unifOn Ω y) = 1 := by
  simp [unifOn, hcard.ne']

lemma L71_unifOn_nonneg {α : Type} (Ω : Finset α) (y : α) : 0 ≤ unifOn Ω y := by
  classical
  unfold unifOn
  split_ifs
  · positivity
  · exact le_rfl

lemma L71_sum_Al_some_le_one {S : SpinLaw} {n r k : ℕ}
    (Al : (Fin k → Config S (Fin n × Fin r)) → Option (Fin (k + 1) → Config S (Fin n × Fin r)) → ℝ)
    (hAl₀ : ∀ X o, 0 ≤ Al X o) (hAl₁ : ∀ X, ∑ o, Al X o = 1)
    (X : Fin k → Config S (Fin n × Fin r)) :
    (∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al X (some X')) ≤ 1 := by
  have hsum : (∑ o : Option (Fin (k + 1) → Config S (Fin n × Fin r)), Al X o) =
      Al X none + ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al X (some X') :=
    Fintype.sum_option (fun o => Al X o)
  have h1 := hAl₁ X
  have h0 := hAl₀ X none
  linarith

lemma L71_prod_sum_one {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] (f : ι → α → ℝ)
    (hf : ∀ i, ∑ x : α, f i x = 1) :
    (∑ g : ι → α, ∏ i : ι, f i (g i)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun i x => f i x)]
  simp [hf]

open Classical in
lemma L71_main_proof (S : SpinLaw) {n r d k T : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (hΨ : ∀ m₀ : Fin d → Bool, ∑ y, unifOn Ω y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d)
    (κ : BinCfg n → Option (Config S (Fin n × Fin r)) → ℝ)
    (hκ₀ : ∀ y o, 0 ≤ κ y o) (hκ₁ : ∀ y, ∑ o, κ y o = 1)
    (Al : (Fin k → Config S (Fin n × Fin r)) → Option (Fin (k + 1) → Config S (Fin n × Fin r)) → ℝ)
    (hAl₀ : ∀ X o, 0 ≤ Al X o) (hAl₁ : ∀ X, ∑ o, Al X o = 1) (i : Fin T) :
    ∑ Fs : Fin T → BinCfg n, prodLaw (unifOn Ω) Fs *
      ∑ ω : Fin T → Option (Config S (Fin n × Fin r)), (∏ t, κ (Fs t) (ω t)) *
        (match lhatRun k ω with
         | none => 0
         | some R =>
            ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
              (if PassEv Ω Ψ X' ∧ (∀ j, (R j).1 ≠ i) ∧
                  mStar Ψ (fun j => (R j).2) X' = some (Ψ (Fs i)) then (1 : ℝ) else 0)) ≤
      1 / (2 : ℝ) ^ d := by
  classical
  let innerTerm : BinCfg n → (Fin T → Option (Config S (Fin n × Fin r))) → ℝ := fun yi ω =>
    match lhatRun k ω with
    | none => 0
    | some R =>
      ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
        (if PassEv Ω Ψ X' ∧ (∀ j, (R j).1 ≠ i) ∧
            mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)
  let boundTerm : BinCfg n → (Fin T → Option (Config S (Fin n × Fin r))) → ℝ := fun yi ω0 =>
    match lhatRun k ω0 with
    | none => 0
    | some R =>
      ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
        (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)
  have hbound_nonneg : ∀ yi ω0, 0 ≤ boundTerm yi ω0 := by
    intro yi ω0
    dsimp [boundTerm]
    cases lhatRun k ω0 with
    | none => exact le_rfl
    | some R =>
      apply Finset.sum_nonneg
      intro X' _
      apply mul_nonneg (hAl₀ _ _)
      split_ifs <;> norm_num
  have hpoint_le : ∀ (yi : BinCfg n) (ω' : {t : Fin T // t ≠ i} → Option (Config S (Fin n × Fin r)))
      (o : Option (Config S (Fin n × Fin r))),
      innerTerm yi ((L71_splitEquiv i).symm (o, ω')) ≤
        boundTerm yi ((L71_splitEquiv i).symm (none, ω')) := by
    intro yi ω' o
    dsimp [innerTerm]
    cases hRo : lhatRun k ((L71_splitEquiv i).symm (o, ω')) with
    | none => exact hbound_nonneg yi _
    | some R =>
      dsimp only
      by_cases hne : ∀ j, (R j).1 ≠ i
      · have hR0 := L71_lhatRun_erase i ω' o R hRo hne
        dsimp [boundTerm]
        rw [hR0]
        apply Finset.sum_le_sum
        intro X' _
        apply mul_le_mul_of_nonneg_left _ (hAl₀ _ _)
        split_ifs with h1 h2 h3
        · exact le_rfl
        · exfalso; exact h2 h1.2.2
        · norm_num
        · exact le_rfl
      · have hzero : (∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
            (if PassEv Ω Ψ X' ∧ (∀ j, (R j).1 ≠ i) ∧
                mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro X' _
          have hfalse : ¬ (PassEv Ω Ψ X' ∧ (∀ j, (R j).1 ≠ i) ∧
              mStar Ψ (fun j => (R j).2) X' = some (Ψ yi)) := fun h => hne h.2.1
          simp [hfalse]
        rw [hzero]
        exact hbound_nonneg yi _
  have hω_le : ∀ (Fs' : {t : Fin T // t ≠ i} → BinCfg n) (yi : BinCfg n),
      (∑ ω : Fin T → Option (Config S (Fin n × Fin r)),
          (∏ t, κ (((L71_splitEquiv i).symm (yi, Fs')) t) (ω t)) * innerTerm yi ω) ≤
        ∑ ω' : {t : Fin T // t ≠ i} → Option (Config S (Fin n × Fin r)),
          (∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) *
            boundTerm yi ((L71_splitEquiv i).symm (none, ω')) := by
    intro Fs' yi
    let Fs := (L71_splitEquiv i).symm (yi, Fs')
    rw [← Equiv.sum_comp (L71_splitEquiv i).symm]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro ω' _
    have hprod_eq : ∀ o : Option (Config S (Fin n × Fin r)),
        (∏ t : Fin T, κ (Fs t) (((L71_splitEquiv i).symm (o, ω')) t)) =
          κ yi o * ∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t) := by
      intro o
      rw [L71_prod_split i (fun t a => κ (Fs t) a)]
      congr 1
      · simp [Fs, L71_splitEquiv]
      · apply Finset.prod_congr rfl
        intro t _
        simp [Fs, L71_splitEquiv, t.2]
    calc
      ∑ o : Option (Config S (Fin n × Fin r)),
          (∏ t : Fin T, κ (Fs t) (((L71_splitEquiv i).symm (o, ω')) t)) *
            innerTerm yi ((L71_splitEquiv i).symm (o, ω'))
          = ∑ o, (κ yi o * ∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) *
              innerTerm yi ((L71_splitEquiv i).symm (o, ω')) := by
            apply Finset.sum_congr rfl; intro o _; rw [hprod_eq o]
      _ ≤ ∑ o, (κ yi o * ∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) *
              boundTerm yi ((L71_splitEquiv i).symm (none, ω')) := by
            apply Finset.sum_le_sum
            intro o _
            apply mul_le_mul_of_nonneg_left (hpoint_le yi ω' o)
            apply mul_nonneg (hκ₀ _ _)
            apply Finset.prod_nonneg
            intro t _
            exact hκ₀ _ _
      _ = (∑ o, κ yi o) *
            ((∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) *
              boundTerm yi ((L71_splitEquiv i).symm (none, ω'))) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro o _; ring
      _ = (∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) *
            boundTerm yi ((L71_splitEquiv i).symm (none, ω')) := by
            rw [hκ₁ yi, one_mul]
  have hyi_bound : ∀ ω0 : Fin T → Option (Config S (Fin n × Fin r)),
      (∑ yi : BinCfg n, unifOn Ω yi * boundTerm yi ω0) ≤ 1 / (2 : ℝ) ^ d := by
    intro ω0
    dsimp [boundTerm]
    cases hR0 : lhatRun k ω0 with
    | none =>
      simp only [mul_zero, Finset.sum_const_zero]
      positivity
    | some R =>
      have hswap : (∑ yi : BinCfg n, unifOn Ω yi *
            ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
              (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)) =
          ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
            (∑ yi : BinCfg n, unifOn Ω yi *
              (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)) := by
        calc
          ∑ yi : BinCfg n, unifOn Ω yi *
              ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
                (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)
              = ∑ yi : BinCfg n, ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r),
                  unifOn Ω yi * (Al (fun j => (R j).2) (some X') *
                    (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)) := by
                simp_rw [Finset.mul_sum]
          _ = ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), ∑ yi : BinCfg n,
                unifOn Ω yi * (Al (fun j => (R j).2) (some X') *
                  (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)) :=
                Finset.sum_comm
          _ = ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
                (∑ yi : BinCfg n, unifOn Ω yi *
                  (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)) := by
                apply Finset.sum_congr rfl
                intro X' _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro yi _
                ring
      rw [hswap]
      have hterm : ∀ X' : Fin (k + 1) → Config S (Fin n × Fin r),
          (∑ yi : BinCfg n, unifOn Ω yi *
              (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0)) ≤
            1 / (2 : ℝ) ^ d := by
        intro X'
        cases hm : mStar Ψ (fun j => (R j).2) X' with
        | none =>
          simp only [reduceCtorEq, ↓reduceIte, mul_zero, Finset.sum_const_zero]
          positivity
        | some m₀ =>
          have heq : (∑ yi : BinCfg n, unifOn Ω yi *
                (if some m₀ = some (Ψ yi) then (1 : ℝ) else 0)) =
              ∑ yi : BinCfg n, unifOn Ω yi * (if Ψ yi = m₀ then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro yi _
            congr 2
            simp [eq_comm]
          rw [heq, hΨ m₀]
      calc
        ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
            (∑ yi : BinCfg n, unifOn Ω yi *
              (if mStar Ψ (fun j => (R j).2) X' = some (Ψ yi) then (1 : ℝ) else 0))
            ≤ ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r),
                Al (fun j => (R j).2) (some X') * (1 / (2 : ℝ) ^ d) := by
              apply Finset.sum_le_sum
              intro X' _
              exact mul_le_mul_of_nonneg_left (hterm X') (hAl₀ _ _)
        _ = (∑ X' : Fin (k + 1) → Config S (Fin n × Fin r),
                Al (fun j => (R j).2) (some X')) * (1 / (2 : ℝ) ^ d) := by
              rw [← Finset.sum_mul]
        _ ≤ 1 * (1 / (2 : ℝ) ^ d) := by
              apply mul_le_mul_of_nonneg_right (L71_sum_Al_some_le_one Al hAl₀ hAl₁ _)
              positivity
        _ = 1 / (2 : ℝ) ^ d := one_mul _
  have hcard : 0 < Ω.card := L71_omega_card_pos Ω Ψ hΨ
  have hunif_sum : (∑ y : BinCfg n, unifOn Ω y) = 1 := L71_sum_unifOn_eq_one Ω hcard
  have hprod_unif : (∑ Fs' : {t : Fin T // t ≠ i} → BinCfg n,
      ∏ t : {t : Fin T // t ≠ i}, unifOn Ω (Fs' t)) = 1 :=
    L71_prod_sum_one _ (fun _ => hunif_sum)
  have hprod_kap : ∀ Fs' : {t : Fin T // t ≠ i} → BinCfg n,
      (∑ ω' : {t : Fin T // t ≠ i} → Option (Config S (Fin n × Fin r)),
        ∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) = 1 :=
    fun Fs' => L71_prod_sum_one _ (fun t => hκ₁ (Fs' t))
  calc
    ∑ Fs : Fin T → BinCfg n, prodLaw (unifOn Ω) Fs *
        ∑ ω : Fin T → Option (Config S (Fin n × Fin r)), (∏ t, κ (Fs t) (ω t)) * innerTerm (Fs i) ω
        = ∑ p : BinCfg n × ({t : Fin T // t ≠ i} → BinCfg n),
            (unifOn Ω p.1 * ∏ t : {t : Fin T // t ≠ i}, unifOn Ω (p.2 t)) *
              ∑ ω : Fin T → Option (Config S (Fin n × Fin r)),
                (∏ t, κ (((L71_splitEquiv i).symm p) t) (ω t)) * innerTerm p.1 ω := by
          rw [← Equiv.sum_comp (L71_splitEquiv (α := BinCfg n) i).symm]
          apply Finset.sum_congr rfl
          intro p _
          unfold prodLaw
          rw [L71_prod_split i (fun _ y => unifOn Ω y)]
          congr 1
          · congr 1
            · simp [L71_splitEquiv]
            · apply Finset.prod_congr rfl
              intro t _
              simp [L71_splitEquiv, t.2]
          · apply Finset.sum_congr rfl
            intro ω _
            simp [L71_splitEquiv]
    _ = ∑ Fs' : {t : Fin T // t ≠ i} → BinCfg n,
          (∏ t : {t : Fin T // t ≠ i}, unifOn Ω (Fs' t)) *
            ∑ yi : BinCfg n, unifOn Ω yi *
              ∑ ω : Fin T → Option (Config S (Fin n × Fin r)),
                (∏ t, κ (((L71_splitEquiv i).symm (yi, Fs')) t) (ω t)) * innerTerm yi ω := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro Fs' _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro yi _
          ring
    _ ≤ ∑ Fs' : {t : Fin T // t ≠ i} → BinCfg n,
          (∏ t : {t : Fin T // t ≠ i}, unifOn Ω (Fs' t)) *
            ∑ yi : BinCfg n, unifOn Ω yi *
              ∑ ω' : {t : Fin T // t ≠ i} → Option (Config S (Fin n × Fin r)),
                (∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) *
                  boundTerm yi ((L71_splitEquiv i).symm (none, ω')) := by
          apply Finset.sum_le_sum
          intro Fs' _
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => L71_unifOn_nonneg Ω _))
          apply Finset.sum_le_sum
          intro yi _
          exact mul_le_mul_of_nonneg_left (hω_le Fs' yi) (L71_unifOn_nonneg Ω yi)
    _ = ∑ Fs' : {t : Fin T // t ≠ i} → BinCfg n,
          (∏ t : {t : Fin T // t ≠ i}, unifOn Ω (Fs' t)) *
            ∑ ω' : {t : Fin T // t ≠ i} → Option (Config S (Fin n × Fin r)),
              (∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) *
                ∑ yi : BinCfg n, unifOn Ω yi *
                  boundTerm yi ((L71_splitEquiv i).symm (none, ω')) := by
          apply Finset.sum_congr rfl
          intro Fs' _
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ω' _
          apply Finset.sum_congr rfl
          intro yi _
          ring
    _ ≤ ∑ Fs' : {t : Fin T // t ≠ i} → BinCfg n,
          (∏ t : {t : Fin T // t ≠ i}, unifOn Ω (Fs' t)) *
            ∑ ω' : {t : Fin T // t ≠ i} → Option (Config S (Fin n × Fin r)),
              (∏ t : {t : Fin T // t ≠ i}, κ (Fs' t) (ω' t)) * (1 / (2 : ℝ) ^ d) := by
          apply Finset.sum_le_sum
          intro Fs' _
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => L71_unifOn_nonneg Ω _))
          apply Finset.sum_le_sum
          intro ω' _
          exact mul_le_mul_of_nonneg_left (hyi_bound _) (Finset.prod_nonneg (fun _ _ => hκ₀ _ _))
    _ = 1 / (2 : ℝ) ^ d := by
          simp_rw [← Finset.sum_mul, hprod_kap, one_mul, ← Finset.sum_mul, hprod_unif, one_mul]

end CritWinSpin

open CritWinSpin
open scoped BigOperators

open Classical in
/-- Bridge lemma for Lemma 7.1 (p.26, eq. (39)): the target conclusion given Theorem 5.1 (p.19, eqs. (26)–(27)). -/
theorem solution (S : SpinLaw) {n r d k T : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (hΨ : ∀ m₀ : Fin d → Bool, ∑ y, unifOn Ω y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d)
    (κ : BinCfg n → Option (Config S (Fin n × Fin r)) → ℝ)
    (hκ₀ : ∀ y o, 0 ≤ κ y o) (hκ₁ : ∀ y, ∑ o, κ y o = 1)
    (Al : (Fin k → Config S (Fin n × Fin r)) → Option (Fin (k + 1) → Config S (Fin n × Fin r)) → ℝ)
    (hAl₀ : ∀ X o, 0 ≤ Al X o) (hAl₁ : ∀ X, ∑ o, Al X o = 1) (i : Fin T) (hP : ∃ C : ℝ, 0 < C ∧ ∀ F : BilinearFamily, ∃ circ : WatersCircuit F,
      PolyBounded circ.n0 ∧ (∀ d, d ^ 2 ≤ circ.n0 d) ∧
      (∃ evalF : Str → Str, CookPvsNP.PolyTimeComputable evalF ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
          (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
          evalF (tupleCode [pkCode F d desc key, List.ofFn m, F.encG desc s₁, F.encG desc s₂]) =
            List.ofFn (circ.evalCfg d desc key m s₁ s₂)) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
        circ.psi d desc key (circ.evalCfg d desc key m s₁ s₂) = m) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (y : BinCfg (circ.n0 d)), circ.genLaw d desc key y = unifOn (circ.omega d desc key) y) ∧
      SourceProps F circ.toSource C ∧
      SourceProps F (hatSource circ.toSource) C ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (y : BinCfg (circ.n0 d + 1)),
        (1 / 2 : ℝ) * ∑ t : Bool, ∑ Y : BinCfg (circ.n0 d), unifOn (circ.omega d desc key) Y *
            (if (Fin.cons t (fun i => t == Y i) : BinCfg (circ.n0 d + 1)) = y then (1 : ℝ) else 0) =
          unifOn ((hatSource circ.toSource).omega d desc key) y)) :
    ∑ Fs : Fin T → BinCfg n, prodLaw (unifOn Ω) Fs *
      ∑ ω : Fin T → Option (Config S (Fin n × Fin r)), (∏ t, κ (Fs t) (ω t)) *
        (match lhatRun k ω with
         | none => 0
         | some R =>
            ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
              (if PassEv Ω Ψ X' ∧ (∀ j, (R j).1 ≠ i) ∧
                  mStar Ψ (fun j => (R j).2) X' = some (Ψ (Fs i)) then (1 : ℝ) else 0)) ≤
      1 / (2 : ℝ) ^ d :=
  L71_main_proof S Ω Ψ hΨ κ hκ₀ hκ₁ Al hAl₀ hAl₁ i
