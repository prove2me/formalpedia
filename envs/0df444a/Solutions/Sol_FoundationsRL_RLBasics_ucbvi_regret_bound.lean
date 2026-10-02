-- Prove2me | solution 1 for FoundationsRL.RLBasics.ucbvi_regret_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:05:24.073206+00:00
-- url     : https://prove2.me/submissions/78b00cb5-f81b-4db6-a262-3da03157539f

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI

set_option autoImplicit false

namespace UcbviCexF32

open FoundationsRL.RLBasics

/-- Rewards: layer 0 pays 1/2 for action `false`, 0 for `true`; layer 1 pays 1 in state `true`. -/
noncomputable def rr : ℕ → Bool → Bool → ℝ := fun h s a =>
  if h = 0 then (if a then 0 else 1/2) else if h = 1 then (if s then 1 else 0) else 0

/-- Deterministic MDP: the next state equals the action; start in state `false`. -/
noncomputable def MM : EpisodicMDP Bool Bool 2 where
  P := fun _ _ a s' => if s' = a then 1 else 0
  R := rr
  d1 := fun s => if s = false then 1 else 0
  P_nonneg := by intro h s a s'; split_ifs <;> norm_num
  P_sum_one := by intro h s a; simp
  d1_nonneg := by intro s; split_ifs <;> norm_num
  d1_sum_one := by simp

theorem rr_mem (h : ℕ) (s a : Bool) : rr h s a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold rr; constructor <;> split_ifs <;> norm_num

theorem V_one (π : Policy Bool Bool 2) (hπ : IsPolicy 2 π) (s : Bool) :
    V MM π 1 s = if s then 1 else 0 := by
  have hs := (hπ 1 (by norm_num) s).2
  simp only [Fintype.sum_bool] at hs
  simp [V, valueAux, MM, rr, Fintype.sum_bool]
  cases s <;> simp <;> linarith

theorem Q_zero (π : Policy Bool Bool 2) (hπ : IsPolicy 2 π) (s a : Bool) :
    Q MM π 0 s a = if a then 1 else 1/2 := by
  simp only [Q, show (0:ℕ) < 2 by norm_num, if_true]
  simp only [Fintype.sum_bool, V_one π hπ]
  cases a <;> simp [MM, rr]

theorem Vstar_eq (s : Bool) : Vstar MM 0 s = 1 := by
  have hne : Nonempty {π : Policy Bool Bool 2 // IsPolicy 2 π} :=
    ⟨⟨detPolicy (fun _ _ => true), by
      intro h _ s
      refine ⟨fun a => ?_, ?_⟩
      · unfold detPolicy; split_ifs <;> norm_num
      · simp [detPolicy, Fintype.sum_bool]⟩⟩
  have hQ : ∀ a, Qstar MM 0 s a = if a then 1 else 1/2 := by
    intro a
    unfold Qstar
    have : ∀ π : {π : Policy Bool Bool 2 // IsPolicy 2 π},
        Q MM π.1 0 s a = if a then 1 else 1/2 := fun π => Q_zero π.1 π.2 s a
    simp only [this, ciSup_const]
  unfold Vstar
  simp only [hQ]
  apply le_antisymm
  · apply ciSup_le; intro a; cases a <;> norm_num
  · exact le_ciSup_of_le (Finite.bddAbove_range _) true (by simp)

theorem ucbQ_two (δ : ℝ) (T : ℕ) (hist : List (Trajectory Bool Bool 2)) (s a : Bool) :
    ucbQ MM rr δ T hist 2 s a = 0 := by
  rw [ucbQ]; simp

theorem estExp_nonneg (hist : List (Trajectory Bool Bool 2)) (h : ℕ) (s a : Bool)
    (f : Bool → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ estExp hist h s a f := by
  unfold estExp
  simp only
  split_ifs
  · exact le_refl _
  · exact div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (Nat.cast_nonneg _) (hf x)))
      (Nat.cast_nonneg _)

theorem bonus_nonneg (δ : ℝ) (a b c d e : ℕ) : 0 ≤ bonus δ a b c d e := by
  unfold bonus; positivity

theorem ucbQ_one_nonneg (δ : ℝ) (T : ℕ) (hist : List (Trajectory Bool Bool 2)) (s a : Bool) :
    0 ≤ ucbQ MM rr δ T hist 1 s a := by
  rw [ucbQ]
  simp only [show (1:ℕ) < 2 by norm_num, dif_pos]
  apply le_min zero_le_one
  have h1 := (rr_mem 1 s a).1
  have h2 := estExp_nonneg hist 1 s a (fun s' => ⨆ a' : Bool, ucbQ MM rr δ T hist (1 + 1) s' a')
    (fun x => le_ciSup_of_le (Finite.bddAbove_range _) true (by rw [ucbQ_two]))
  have h3 := bonus_nonneg δ (Fintype.card Bool) (Fintype.card Bool) 2 T (countSA hist 1 s a)
  linarith

theorem ucbQ_ff_pos (δ : ℝ) (T : ℕ) (hist : List (Trajectory Bool Bool 2)) :
    0 < ucbQ MM rr δ T hist 0 false false := by
  rw [ucbQ]
  simp only [show (0:ℕ) < 2 by norm_num, dif_pos]
  apply lt_min zero_lt_one
  have h1 : rr 0 false false = 1/2 := by simp [rr]
  have h2 := estExp_nonneg hist 0 false false
    (fun s' => ⨆ a' : Bool, ucbQ MM rr δ T hist (0 + 1) s' a')
    (fun x => le_ciSup_of_le (Finite.bddAbove_range _) true (ucbQ_one_nonneg δ T hist x true))
  have h3 := bonus_nonneg δ (Fintype.card Bool) (Fintype.card Bool) 2 T
    (countSA hist 0 false false)
  linarith

theorem count_ft (hist : List (Trajectory Bool Bool 2))
    (hh : ∀ τ ∈ hist, actionAt τ 0 = false) : countSA hist 0 false true = 0 := by
  unfold countSA
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro τ hτ
  simp [hh τ hτ]

theorem ucbQ_ft (δ : ℝ) (T : ℕ) (hist : List (Trajectory Bool Bool 2))
    (hh : ∀ τ ∈ hist, actionAt τ 0 = false) : ucbQ MM rr δ T hist 0 false true = 0 := by
  rw [ucbQ]
  simp only [show (0:ℕ) < 2 by norm_num, dif_pos]
  have hc := count_ft hist hh
  simp [estExp, bonus, hc, rr]

theorem greedy_ff (δ : ℝ) (T : ℕ) (hist : List (Trajectory Bool Bool 2))
    (hh : ∀ τ ∈ hist, actionAt τ 0 = false) : ucbGreedy MM rr δ T hist 0 false = false := by
  have hlt : ucbQ MM rr δ T hist 0 false true < ucbQ MM rr δ T hist 0 false false := by
    rw [ucbQ_ft δ T hist hh]; exact ucbQ_ff_pos δ T hist
  unfold ucbGreedy
  cases hm : (Finset.univ : Finset Bool).toList.argmax (ucbQ MM rr δ T hist 0 false) with
  | none =>
    rw [List.argmax_eq_none] at hm
    have : false ∈ (Finset.univ : Finset Bool).toList := by simp
    rw [hm] at this; simp at this
  | some m =>
    have hle := List.le_of_mem_argmax (f := ucbQ MM rr δ T hist 0 false)
      (show false ∈ (Finset.univ : Finset Bool).toList by simp) hm
    cases m
    · rfl
    · exact absurd hle (not_le.mpr hlt)

theorem V_learner (δ : ℝ) (T : ℕ) (hist : List (Trajectory Bool Bool 2))
    (hh : ∀ τ ∈ hist, actionAt τ 0 = false) :
    V MM (ucbviLearner MM rr δ T hist) 0 false = 1/2 := by
  have hg := greedy_ff δ T hist hh
  have hp0f : ucbviLearner MM rr δ T hist 0 false false = 1 := by
    simp [ucbviLearner, detPolicy, hg]
  have hp0t : ucbviLearner MM rr δ T hist 0 false true = 0 := by
    simp [ucbviLearner, detPolicy, hg]
  generalize ucbviLearner MM rr δ T hist = π at hp0f hp0t ⊢
  simp [V, valueAux, MM, rr, hp0f, hp0t]

theorem good_of_prob (δ : ℝ) (T : ℕ) (histT : Fin T → Trajectory Bool Bool 2)
    (hp : historyProb MM (ucbviLearner MM rr δ T) histT ≠ 0) :
    ∀ t : Fin T, actionAt (histT t) 0 = false := by
  unfold historyProb at hp
  rw [Finset.prod_ne_zero_iff] at hp
  have key : ∀ n : ℕ, ∀ t : Fin T, t.1 = n → actionAt (histT t) 0 = false := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht
      have hpre : ∀ τ ∈ (List.ofFn histT).take t.1, actionAt τ 0 = false := by
        intro τ hτ
        rw [List.mem_iff_getElem] at hτ
        obtain ⟨i, hi, rfl⟩ := hτ
        have hit : i < t.1 := by simp at hi; omega
        have hiT : i < T := by simp at hi; omega
        rw [List.getElem_take, List.getElem_ofFn]
        exact ih i (by omega) ⟨i, hiT⟩ rfl
      have hg := greedy_ff δ T _ hpre
      have hf := hp t (Finset.mem_univ _)
      unfold trajProb at hf
      rw [Fin.prod_univ_two] at hf
      have hd : (histT t).1 = false := by
        by_contra hc
        apply hf
        simp [MM, hc]
      by_contra hc
      apply hf
      have : stateAt (histT t) 0 = false := hd
      simp only [Fin.val_zero, this, ucbviLearner, detPolicy, hg, hc, if_false]
      simp
  exact fun t => key t.1 t rfl

theorem regret_eq (δ : ℝ) (T : ℕ) (histT : Fin T → Trajectory Bool Bool 2)
    (hp : historyProb MM (ucbviLearner MM rr δ T) histT ≠ 0) :
    regret MM rr δ T histT = (T : ℝ) / 2 := by
  have hgood := good_of_prob δ T histT hp
  have hterm : ∀ t : Fin T,
      ((∑ s : Bool, MM.d1 s * Vstar MM 0 s) -
        ∑ s : Bool, MM.d1 s * V MM (ucbviLearner MM rr δ T ((List.ofFn histT).take t.1)) 0 s)
        = 1/2 := by
    intro t
    have hpre : ∀ τ ∈ (List.ofFn histT).take t.1, actionAt τ 0 = false := by
      intro τ hτ
      have := List.mem_of_mem_take hτ
      rw [List.mem_ofFn] at this
      obtain ⟨i, rfl⟩ := this
      exact hgood i
    have hv := V_learner δ T _ hpre
    simp only [Fintype.sum_bool, Vstar_eq, hv]
    simp [MM]
    norm_num
  unfold regret
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem bound_lt (C x : ℝ) (hC : 0 < C) (hx1 : 1 ≤ x) (hx : 64 * C < x) :
    C * 2 * 2 * Real.sqrt (2 * x ^ 8) * Real.sqrt (Real.log (2 * 2 * 2 * x ^ 8 / (1/2)))
      < x ^ 8 / 2 := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.sqrt (2 * x ^ 8) ≤ 2 * x ^ 4 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [pow_pos hx0 8]
  have hlog : Real.log (2 * 2 * 2 * x ^ 8 / (1/2)) ≤ 16 * x ^ 2 := by
    have he : (2 * 2 * 2 * x ^ 8 / (1/2) : ℝ) = 16 * x ^ 8 := by ring
    rw [he, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have a1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 16 by norm_num)
    have a2 := Real.log_le_sub_one_of_pos hx0
    push_cast
    nlinarith
  have h2 : Real.sqrt (Real.log (2 * 2 * 2 * x ^ 8 / (1/2))) ≤ 4 * x := by
    calc Real.sqrt (Real.log (2 * 2 * 2 * x ^ 8 / (1/2))) ≤ Real.sqrt (16 * x ^ 2) :=
          Real.sqrt_le_sqrt hlog
      _ = 4 * x := by
          rw [show (16 * x ^ 2 : ℝ) = (4 * x) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have h3 : C * 2 * 2 * Real.sqrt (2 * x ^ 8) * Real.sqrt (Real.log (2 * 2 * 2 * x ^ 8 / (1/2)))
      ≤ C * 2 * 2 * (2 * x ^ 4) * (4 * x) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (Real.sqrt_nonneg _)
    positivity
  have hx3 : x ≤ x ^ 3 := by nlinarith
  have h5 : 0 < x ^ 5 := by positivity
  have h4 : C * 2 * 2 * (2 * x ^ 4) * (4 * x) < x ^ 8 / 2 := by
    have : x ^ 8 = x ^ 3 * x ^ 5 := by ring
    rw [this]
    have e : C * 2 * 2 * (2 * x ^ 4) * (4 * x) = 32 * C * x ^ 5 := by ring
    rw [e]
    nlinarith
  linarith

end UcbviCexF32

open FoundationsRL.RLBasics in
theorem solution : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ),
        (∀ h, h < H → ∀ s a, r h s a ∈ Set.Icc (0 : ℝ) 1) →
        (∀ h, h < H → ∀ s a, M.R h s a = r h s a) →
        (∀ s : S, Vstar M 0 s ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (T : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
        probEvent M (ucbviLearner M r δ T) T
            (fun histT => regret M r δ T histT ≤
              C * (H : ℝ) * (Fintype.card S : ℝ) * Real.sqrt ((Fintype.card A : ℝ) * T) *
                Real.sqrt (Real.log ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H * T / δ)))
          ≥ 1 - δ) := by
  rintro ⟨C, hC, h⟩
  set L : ℕ := ⌈64 * C⌉₊ + 1 with hL
  have hLx : 64 * C < (L : ℝ) := by
    rw [hL]; push_cast; linarith [Nat.le_ceil (64 * C)]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by rw [hL]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈64 * C⌉₊]
  have hmain := @h Bool Bool _ _ _ _ _ 2 UcbviCexF32.MM UcbviCexF32.rr
    (fun h _ s a => UcbviCexF32.rr_mem h s a) (fun _ _ _ _ => rfl)
    (fun s => by rw [UcbviCexF32.Vstar_eq]; norm_num) (L ^ 8) (1/2) (by norm_num) (by norm_num)
  have hzero : probEvent UcbviCexF32.MM (ucbviLearner UcbviCexF32.MM UcbviCexF32.rr (1/2) (L ^ 8))
      (L ^ 8) (fun histT => regret UcbviCexF32.MM UcbviCexF32.rr (1/2) (L ^ 8) histT ≤
              C * ((2 : ℕ) : ℝ) * (Fintype.card Bool : ℝ) *
                Real.sqrt ((Fintype.card Bool : ℝ) * ((L ^ 8 : ℕ) : ℝ)) *
                Real.sqrt (Real.log ((Fintype.card Bool : ℝ) * (Fintype.card Bool : ℝ) *
                  ((2 : ℕ) : ℝ) * ((L ^ 8 : ℕ) : ℝ) / (1/2)))) = 0 := by
    unfold probEvent
    apply Finset.sum_eq_zero
    intro histT _
    split_ifs with hE
    · by_contra hne
      simp only [UcbviCexF32.regret_eq _ _ _ hne, Fintype.card_bool, Nat.cast_pow,
        Nat.cast_ofNat] at hE
      have := UcbviCexF32.bound_lt C (L : ℝ) hC hL1 hLx
      linarith
    · rfl
  rw [hzero] at hmain
  norm_num at hmain
