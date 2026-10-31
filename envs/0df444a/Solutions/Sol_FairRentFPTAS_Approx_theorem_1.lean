-- Prove2me | solution 1 for FairRentFPTAS.Approx.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:28:18.330585+00:00
-- url     : https://prove2.me/submissions/fc6052c3-9f2b-4f4b-a8cf-85e3f9cdea6c

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model
import Theorems.Thm_FairRentFPTAS_Approx_lemma_3
import Theorems.Thm_FairRentFPTAS_Approx_lemma_5
import Theorems.Thm_FairRentFPTAS_Approx_ineq_3
import Theorems.Thm_FairRentFPTAS_Approx_lemma_16

open FairRentFPTAS.Approx

namespace FRFT1Aux

/-- `drop` vanishes at a point below every start of a sorted list. -/
lemma drop_eq_zero (x : ℝ) : ∀ (l : List (ℝ × ℝ)), (l.map Prod.fst).Pairwise (· < ·) →
    (∀ e ∈ l, x ≤ e.1) → PLFun.drop l x = 0 := by
  intro l
  induction l with
  | nil => intro _ _; simp [PLFun.drop]
  | cons e t ih =>
    intro hs hx
    cases t with
    | nil =>
      have := hx e (by simp)
      simp [PLFun.drop, max_eq_right this]
    | cons e' t' =>
      have hs' : ((e' :: t').map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
      have hee' : e.1 < e'.1 := (List.pairwise_cons.mp hs).1 e'.1 (by simp)
      have := hx e (by simp)
      simp only [PLFun.drop]
      rw [ih hs' (fun y hy => hx y (List.mem_cons_of_mem _ hy)), max_eq_right this,
        min_eq_left hee'.le]
      ring

lemma starts_nonneg (f : PLFun) (hf : f.WF) : ∀ e ∈ f.pieces, 0 ≤ e.1 := by
  obtain ⟨hne, hhead, hsort, _⟩ := hf
  cases h : f.pieces with
  | nil => exact absurd h hne
  | cons e t =>
    rw [h] at hhead hsort
    simp at hhead
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [hhead]
    · have := (List.pairwise_cons.mp (by simpa using hsort)).1 y.1 (List.mem_map_of_mem hy)
      rw [hhead] at this; exact this.le

lemma eval_zero (f : PLFun) (hf : f.WF) : f.eval 0 = f.base := by
  unfold PLFun.eval
  simp only [lt_irrefl, if_false]
  rw [drop_eq_zero 0 _ hf.2.2.1 (starts_nonneg f hf)]; ring

lemma firstSlope_pos (f : PLFun) (hf : f.WF) : 0 < f.firstSlope := by
  unfold PLFun.firstSlope
  cases h : f.pieces with
  | nil => exact absurd h hf.1
  | cons e t =>
    simp only [List.headD_cons]
    exact hf.2.2.2 e (by rw [h]; simp)

lemma M_pos {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (hJ : Standing J) (M : ℝ)
    (hM : IsThreshold J M) : 0 < M := by
  have a0 : Fin n := ⟨0, by omega⟩
  have h := hM a0 a0 a0
  rw [eval_zero _ (hJ a0 a0)] at h
  by_contra hle
  push_neg at hle
  rcases hle.lt_or_eq with hlt | heq
  · unfold PLFun.eval at h
    rw [if_pos hlt] at h
    have := firstSlope_pos _ (hJ a0 a0)
    nlinarith
  · subst heq
    rw [eval_zero _ (hJ a0 a0)] at h
    exact lt_irrefl _ h

/-- above `M` the extension has slope one. -/
lemma drop_append_M (M x : ℝ) (hx : M ≤ x) : ∀ l : List (ℝ × ℝ), (∀ e ∈ l, e.1 ≤ M) →
    PLFun.drop (l ++ [(M, 1)]) x = PLFun.drop (l ++ [(M, 1)]) M + (x - M) := by
  intro l
  induction l with
  | nil => intro _; simp [PLFun.drop, max_eq_left hx]
  | cons e t ih =>
    intro hl
    have he := hl e (by simp)
    cases t with
    | nil =>
      simp only [List.cons_append, List.nil_append, PLFun.drop]
      rw [max_eq_left (le_trans he hx), min_eq_right hx, max_eq_left he, min_self,
        max_eq_left hx, max_self]
      ring
    | cons e' t' =>
      have he' := hl e' (by simp)
      have IH := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      simp only [List.cons_append] at IH ⊢
      simp only [PLFun.drop]
      rw [IH, max_eq_left (le_trans he hx), max_eq_left he, min_eq_right (le_trans he' hx),
        min_eq_right he']
      ring

lemma eval_hat_above (M : ℝ) (hM : 0 < M) (f : PLFun) (x : ℝ) (hx : M ≤ x) :
    (extendQL M f).eval x = (extendQL M f).eval M - (x - M) := by
  unfold PLFun.eval extendQL
  simp only [not_lt.mpr (le_trans hM.le hx), not_lt.mpr hM.le, if_false]
  rw [drop_append_M M x hx]
  · ring
  · intro e he
    have := (List.mem_filter.mp he).2
    simp at this; exact this.le

/-- below `M` the extension coincides with the original function. -/
lemma drop_filter_append (M x : ℝ) (hxM : x ≤ M) : ∀ l : List (ℝ × ℝ),
    (l.map Prod.fst).Pairwise (· < ·) →
    PLFun.drop (l.filter (fun e => decide (e.1 < M)) ++ [(M, 1)]) x = PLFun.drop l x := by
  intro l
  induction l with
  | nil => intro _; simp [PLFun.drop, max_eq_right hxM]
  | cons e t ih =>
    intro hs
    have hs' : (t.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
    have hlt : ∀ y ∈ t, e.1 < y.1 := fun y hy =>
      (List.pairwise_cons.mp hs).1 y.1 (List.mem_map_of_mem hy)
    by_cases heM : e.1 < M
    · rw [List.filter_cons_of_pos (by simpa using heM)]
      cases ht : t with
      | nil =>
        simp [PLFun.drop]
        rw [min_eq_left (max_le hxM heM.le), max_eq_right hxM]
        ring
      | cons e' t' =>
        rw [ht] at ih hs' hlt
        have hee' : e.1 < e'.1 := hlt e' (by simp)
        by_cases he'M : e'.1 < M
        · rw [List.filter_cons_of_pos (by simpa using he'M)]
          rw [List.filter_cons_of_pos (by simpa using he'M)] at ih
          have IH := ih hs'
          simp only [List.cons_append] at IH ⊢
          simp only [PLFun.drop] at IH ⊢
          rw [IH]
        · push_neg at he'M
          have hfil : (e' :: t').filter (fun e => decide (e.1 < M)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro y hy
            simp only [decide_eq_true_eq, not_lt]
            rcases List.mem_cons.mp hy with rfl | hy
            · exact he'M
            · have := (List.pairwise_cons.mp hs').1 y.1 (List.mem_map_of_mem hy)
              linarith
          rw [hfil]
          simp only [List.nil_append, List.cons_append, PLFun.drop]
          rw [drop_eq_zero x (e' :: t') hs']
          · rw [min_eq_left (max_le hxM heM.le), min_eq_left (max_le (le_trans hxM he'M) hee'.le),
              max_eq_right hxM]
            ring
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · linarith
            · have := (List.pairwise_cons.mp hs').1 y.1 (List.mem_map_of_mem hy)
              linarith
    · push_neg at heM
      have hfil : (e :: t).filter (fun e => decide (e.1 < M)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        simp only [decide_eq_true_eq, not_lt]
        rcases List.mem_cons.mp hy with rfl | hy
        · exact heM
        · linarith [hlt y hy]
      rw [hfil]
      rw [drop_eq_zero x (e :: t) hs]
      · simp [PLFun.drop, max_eq_right hxM]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · linarith
        · linarith [hlt y hy]

lemma eval_hat_below (M : ℝ) (f : PLFun) (hf : f.WF) (x : ℝ) (hx0 : 0 ≤ x) (hxM : x ≤ M) :
    (extendQL M f).eval x = f.eval x := by
  unfold PLFun.eval extendQL
  simp only [not_lt.mpr hx0, if_false]
  rw [drop_filter_append M x hxM f.pieces hf.2.2.1]

/-- Reducing `ε ≥ 1` to some `ε' ∈ [1/3, 1)` with `1 + ε = (1 + ε')^m`. -/
lemma eps_reduce (ε : ℝ) (hε : 1 ≤ ε) :
    ∃ ε' : ℝ, 1 / 3 ≤ ε' ∧ ε' < 1 ∧ ∃ m : ℕ, (1 + ε') ^ m = 1 + ε := by
  set L := ⌊Real.logb 2 (1 + ε)⌋₊ with hL
  set m := L + 1 with hm
  have hm0 : m ≠ 0 := by omega
  have h1e : (0 : ℝ) ≤ 1 + ε := by linarith
  set y := (1 + ε) ^ ((m : ℝ)⁻¹) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg h1e _
  have hym : y ^ m = 1 + ε := Real.rpow_inv_natCast_pow h1e hm0
  have hlog1 : 1 ≤ Real.logb 2 (1 + ε) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; linarith
  have hL1 : 1 ≤ L := by
    rw [hL]; exact Nat.le_floor (by exact_mod_cast hlog1)
  have hup : 1 + ε < 2 ^ m := by
    have := Nat.lt_floor_add_one (Real.logb 2 (1 + ε))
    rw [← hL] at this
    have h2 := (Real.logb_lt_iff_lt_rpow (b := 2) (by norm_num) (by linarith)).mp this
    rw [hm]; push_cast
    calc 1 + ε < (2 : ℝ) ^ ((L : ℝ) + 1) := h2
      _ = 2 ^ (L + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
  have hlow : (2 : ℝ) ^ L ≤ 1 + ε := by
    have h := Nat.floor_le (show 0 ≤ Real.logb 2 (1 + ε) by linarith)
    rw [← hL] at h
    have := (Real.le_logb_iff_rpow_le (b := 2) (by norm_num) (by linarith)).mp h
    rwa [Real.rpow_natCast] at this
  have h43 : (4 / 3 : ℝ) ^ m ≤ 2 ^ L := by
    rw [hm, pow_succ]
    have e : (2 : ℝ) ^ L = (3 / 2) ^ L * (4 / 3) ^ L := by
      rw [← mul_pow]; norm_num
    rw [e]
    have : (3 / 2 : ℝ) ≤ (3 / 2) ^ L := le_self_pow₀ (by norm_num) (by omega)
    have h0 : (0 : ℝ) ≤ (4 / 3) ^ L := by positivity
    nlinarith
  refine ⟨y - 1, ?_, ?_, m, by rw [show 1 + (y - 1) = y by ring, hym]⟩
  · by_contra hcon
    push_neg at hcon
    have : y < 4 / 3 := by linarith
    have := pow_lt_pow_left₀ this hy0 hm0
    rw [hym] at this
    linarith
  · by_contra hcon
    push_neg at hcon
    have : (2 : ℝ) ≤ y := by linarith
    have := pow_le_pow_left₀ (by norm_num) this m
    rw [hym] at this
    linarith

lemma powers_reduce {n : ℕ} (J : Instance n) (ε ε' : ℝ) (m : ℕ) (hm : (1 + ε') ^ m = 1 + ε)
    (hpow : PowersProp ε J) : PowersProp ε' J := by
  intro a r e he
  obtain ⟨k, hk⟩ := hpow a r e he
  refine ⟨m * k, ?_⟩
  rw [hk, ← hm, zpow_mul]
  simp

/-- the potential function: number of boundary points below the price. -/
noncomputable def Phi {n : ℕ} (S : Fin n → Finset ℝ) (q : Fin n → ℝ) : ℕ :=
  ∑ r, ((S r).filter (fun b => b < q r)).card

lemma Phi_mono {n : ℕ} (S : Fin n → Finset ℝ) (q q' : Fin n → ℝ) (h : ∀ r, q r ≤ q' r) :
    Phi S q ≤ Phi S q' := by
  unfold Phi
  apply Finset.sum_le_sum
  intro r _
  apply Finset.card_le_card
  intro b hb
  simp only [Finset.mem_filter] at hb ⊢
  exact ⟨hb.1, lt_of_lt_of_le hb.2 (h r)⟩

lemma dom_eq_of_filter_eq {n : ℕ} (J : Instance n) (q q' : Fin n → ℝ)
    (h : ∀ r, ((bd J r).filter (fun b => b < q r)) = ((bd J r).filter (fun b => b < q' r))) :
    domL J q = domL J q' ∧ domU J q = domU J q' := by
  constructor
  · funext r; unfold domL; rw [h r]
  · funext r; unfold domU
    congr 1
    ext b
    simp only [Finset.mem_filter]
    have := congrArg (fun s => b ∈ s) (h r)
    simp only [Finset.mem_filter, eq_iff_iff] at this
    constructor
    · rintro ⟨hb, hle⟩
      refine ⟨hb, ?_⟩
      by_contra hc; push_neg at hc
      have := (this.mpr ⟨hb, hc⟩).2; linarith
    · rintro ⟨hb, hle⟩
      refine ⟨hb, ?_⟩
      by_contra hc; push_neg at hc
      have := (this.mp ⟨hb, hc⟩).2; linarith

lemma Phi_strict {n : ℕ} (J : Instance n) (q q' : Fin n → ℝ) (h : ∀ r, q r ≤ q' r)
    (hne : ¬ (domL J q = domL J q' ∧ domU J q = domU J q')) :
    Phi (bd J) q < Phi (bd J) q' := by
  unfold Phi
  have hsub : ∀ r, ((bd J r).filter (fun b => b < q r)) ⊆ ((bd J r).filter (fun b => b < q' r)) := by
    intro r b hb
    simp only [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, lt_of_lt_of_le hb.2 (h r)⟩
  apply Finset.sum_lt_sum
  · intro r _; exact Finset.card_le_card (hsub r)
  · by_contra hc
    push_neg at hc
    apply hne
    apply dom_eq_of_filter_eq
    intro r
    exact Finset.eq_of_subset_of_card_le (hsub r) (hc r (Finset.mem_univ _))

lemma kinks_length (f : PLFun) : f.kinks.length ≤ f.pieces.length := by
  unfold PLFun.kinks
  refine le_trans (List.length_filterMap_le _ _) ?_
  rw [List.length_zip]; exact min_le_left _ _

lemma bd_card {n : ℕ} (J : Instance n) (r : Fin n) :
    (bd J r).card ≤ 1 + ∑ a, (J.v a r).pieces.length := by
  unfold bd
  refine le_trans (Finset.card_insert_le _ _) ?_
  rw [add_comm]
  apply Nat.add_le_add_left
  refine le_trans Finset.card_biUnion_le ?_
  apply Finset.sum_le_sum
  intro a _
  exact le_trans (List.toFinset_card_le _) (kinks_length _)

end FRFT1Aux

open FRFT1Aux in
theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (J : Instance n) (ε β M : ℝ),
    1 ≤ n → Standing J → 0 < ε → PowersProp ε J →
    (∀ a r, ∀ e ∈ (J.v a r).pieces, |Real.log e.2| ≤ β) →
    IsThreshold J M →
    (∃ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ),
        IsRun J M T π p ∧ Halted p T) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun J M T π p →
        (T : ℝ) ≤ c * ((n : ℝ) + totalPieces J + β + 1 / ε + 1) ^ c) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun J M T π p →
        Halted p T → (∀ r, 0 ≤ p T r) ∧ IsEF J (π T) (p T)) := by
  classical
  refine ⟨50, ?_⟩
  intro n J ε β M hn hJ hε hpow hβ hM
  have hM0 : 0 < M := M_pos hn J hJ M hM
  set Ĵ := hatInst M J with hĴ
  have hĴv : ∀ a r, Ĵ.v a r = extendQL M (J.v a r) := fun a r => rfl
  have hβ0 : 0 ≤ β := by
    have a0 : Fin n := ⟨0, by omega⟩
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hJ a0 a0).1
    exact le_trans (abs_nonneg _) (hβ a0 a0 e he)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (n : ℝ) + totalPieces J + β + 1 / ε + 1 := ⟨_, rfl⟩
  rw [← hX]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hε' : 0 < 1 / ε := by positivity
  have hℓ0 : (0 : ℝ) ≤ totalPieces J := by positivity
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  -- stretch bound
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = if ε < 1 then 6 * β * n / ε else 18 * β * n := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; split_ifs <;> positivity
  have hstretch : ∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ),
      IsRun J M T π p → ∀ i j : ℕ, 1 ≤ i → i ≤ j → j + 1 ≤ T →
      (∀ k, i ≤ k → k ≤ j → domL Ĵ (p k) = domL Ĵ (p (i - 1)) ∧
        domU Ĵ (p k) = domU Ĵ (p (i - 1))) → ((j + 1 - i : ℕ) : ℝ) ≤ D := by
    intro T π p hrun i j hi hij hjT hdom
    by_cases hε1 : ε < 1
    · rw [hD, if_pos hε1]
      exact ineq_3 hn J ε β M hJ hε hε1 hpow hβ hM T π p hrun i j hi hij hjT hdom
    · push_neg at hε1
      obtain ⟨ε', h13, hε'1, m, hm⟩ := eps_reduce ε hε1
      have h := ineq_3 hn J ε' β M hJ (by linarith) hε'1 (powers_reduce J ε ε' m hm hpow) hβ hM
        T π p hrun i j hi hij hjT hdom
      rw [hD, if_neg (by linarith)]
      refine le_trans h ?_
      rw [div_le_iff₀ (by linarith)]
      have : (0 : ℝ) ≤ β * n := by positivity
      nlinarith
  -- boundary count
  obtain ⟨Bd, hBdDef⟩ : ∃ Bd : ℕ, Bd = ∑ r, (bd Ĵ r).card := ⟨_, rfl⟩
  have hBd : (Bd : ℝ) ≤ n + totalPieces J + n * n := by
    have h1 : Bd ≤ ∑ r : Fin n, (1 + ∑ a, ((J.v a r).pieces.length + 1)) := by
      rw [hBdDef]
      apply Finset.sum_le_sum
      intro r _
      refine le_trans (bd_card Ĵ r) ?_
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro a _
      show (extendQL M (J.v a r)).pieces.length ≤ _
      unfold extendQL
      simp only [List.length_append, List.length_singleton]
      have := List.length_filter_le (fun e : ℝ × ℝ => decide (e.1 < M)) (J.v a r).pieces
      omega
    have h2 : ∑ r : Fin n, (1 + ∑ a, ((J.v a r).pieces.length + 1)) = n + totalPieces J + n * n := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
      unfold totalPieces
      rw [Finset.sum_comm]
      ring
    have := le_trans h1 (le_of_eq h2)
    exact_mod_cast this
  -- the bound
  have hbound : ∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ),
      IsRun J M T π p → (T : ℝ) ≤ 50 * X ^ 50 := by
    intro T π p hrun
    have mono : ∀ s k, s ≤ k → k ≤ T → ∀ r, p k r ≤ p s r := by
      intro s k hsk hkT
      induction k, hsk using Nat.le_induction with
      | base => intro r; exact le_refl _
      | succ k hsk ih =>
        intro r
        have h5 := lemma_5 J M hJ hM T π p hrun (k + 1) (by omega) hkT r
        simp only [Nat.add_sub_cancel] at h5
        exact le_trans h5 (ih (by omega) r)
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊D⌋₊ := ⟨_, rfl⟩
    have hKD : (D : ℝ) < K + 1 := by rw [hK]; exact Nat.lt_floor_add_one D
    have claim : ∀ m : ℕ, m * (K + 1) + 1 ≤ T → Phi (bd Ĵ) (p (m * (K + 1))) + m ≤ Phi (bd Ĵ) (p 0) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hmT
        have ih' := ih (by nlinarith)
        set s := m * (K + 1) with hs
        have hj : (m + 1) * (K + 1) = s + K + 1 := by rw [hs]; ring
        rw [hj] at hmT ⊢
        have hex : ∃ k, s + 1 ≤ k ∧ k ≤ s + K + 1 ∧
            ¬ (domL Ĵ (p k) = domL Ĵ (p s) ∧ domU Ĵ (p k) = domU Ĵ (p s)) := by
          by_contra hcon
          push_neg at hcon
          have := hstretch T π p hrun (s + 1) (s + K + 1) (by omega) (by omega) (by omega)
            (fun k hk1 hk2 => by
              have := hcon k hk1 hk2
              simp only [Nat.add_sub_cancel]
              exact ⟨this.1, this.2⟩)
          have e : (s + K + 1 + 1 - (s + 1) : ℕ) = K + 1 := by omega
          rw [e] at this
          push_cast at this
          linarith
        obtain ⟨k, hk1, hk2, hk3⟩ := hex
        have hlt := Phi_strict Ĵ (p k) (p s) (mono s k (by omega) (by omega)) hk3
        have hle := Phi_mono (bd Ĵ) (p (s + K + 1)) (p k) (mono k (s + K + 1) hk2 (by omega))
        omega
    have hP0 : Phi (bd Ĵ) (p 0) ≤ Bd := by
      unfold Phi; rw [hBdDef]
      apply Finset.sum_le_sum; intro r _
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hT : T ≤ (Bd + 1) * (K + 1) := by
      by_contra hcon
      push_neg at hcon
      have := claim (Bd + 1) (by nlinarith)
      omega
    have hKle : (K : ℝ) ≤ D := by rw [hK]; exact Nat.floor_le hD0
    have hTr : (T : ℝ) ≤ ((Bd : ℝ) + 1) * (D + 1) := by
      have : (T : ℝ) ≤ ((Bd : ℝ) + 1) * ((K : ℝ) + 1) := by exact_mod_cast hT
      refine le_trans this ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have hB1 : (Bd : ℝ) + 1 ≤ 2 * X ^ 2 := by
      have : (n : ℝ) ≤ X := by rw [hX]; linarith
      have : (n : ℝ) * n ≤ X * X := by nlinarith
      have : (totalPieces J : ℝ) ≤ X := by rw [hX]; linarith
      nlinarith
    have hD1 : D + 1 ≤ 25 * X ^ 3 := by
      have hbX : β ≤ X := by rw [hX]; linarith
      have hnX : (n : ℝ) ≤ X := by rw [hX]; linarith
      have heX : 1 / ε ≤ X := by rw [hX]; linarith
      have hbn : β * n ≤ X * X := mul_le_mul hbX hnX (by positivity) (by linarith)
      have hDle : D ≤ 24 * X ^ 3 := by
        rw [hD]
        split_ifs with h
        · have : 6 * β * n / ε = 6 * (β * n) * (1 / ε) := by ring
          rw [this]
          have : β * n * (1 / ε) ≤ X * X * X :=
            mul_le_mul hbn heX (by positivity) (by positivity)
          nlinarith
        · have : X * X ≤ X * X * X := by nlinarith
          nlinarith
      have : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
      linarith
    calc (T : ℝ) ≤ ((Bd : ℝ) + 1) * (D + 1) := hTr
      _ ≤ (2 * X ^ 2) * (25 * X ^ 3) := by
          apply mul_le_mul hB1 hD1 (by linarith) (by positivity)
      _ = 50 * X ^ 5 := by ring
      _ ≤ 50 * X ^ 50 := by
          have := pow_le_pow_right₀ hX1 (show 5 ≤ 50 by norm_num)
          linarith
  -- Part 3 helper: output of a halted run
  have hout : ∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun J M T π p →
      Halted p T → (∀ r, 0 ≤ p T r) ∧ IsEF J (π T) (p T) := by
    intro T π p hrun hhalt
    obtain ⟨hEF0, hM0', hstep⟩ := hrun
    obtain ⟨r0, hr0⟩ := hhalt
    cases T with
    | zero =>
      exfalso; have := hM0' r0; linarith
    | succ k =>
      obtain ⟨_, _, hLP⟩ := hstep k (by omega)
      obtain ⟨⟨_, _, hEF, hnn⟩, _⟩ := hLP
      have hr00 : p (k + 1) r0 = 0 := le_antisymm hr0 (hnn r0)
      have hleM : ∀ r, p (k + 1) r ≤ M := by
        intro r'
        by_contra hgt
        push_neg at hgt
        set α := (π (k + 1)).symm r'
        have hαr : π (k + 1) α = r' := by simp [α]
        have h1 := hEF α r0
        rw [hαr] at h1
        have e1 : (Ĵ.v α r').eval (p (k + 1) r') =
            (Ĵ.v α r').eval M - (p (k + 1) r' - M) := eval_hat_above M hM0 _ _ hgt.le
        have e2 : (Ĵ.v α r').eval M = (J.v α r').eval M :=
          eval_hat_below M _ (hJ α r') M hM0.le le_rfl
        have e3 : (Ĵ.v α r0).eval (p (k + 1) r0) = (J.v α r0).eval 0 := by
          rw [hr00]; exact eval_hat_below M _ (hJ α r0) 0 le_rfl hM0.le
        have h4 := hM α r' r0
        change (Ĵ.v α r0).eval (p (k + 1) r0) ≤ (Ĵ.v α r').eval (p (k + 1) r') at h1
        linarith
      refine ⟨hnn, ?_⟩
      intro a r
      have h1 := hEF a r
      change (Ĵ.v a r).eval (p (k + 1) r) ≤ (Ĵ.v a (π (k + 1) a)).eval (p (k + 1) (π (k + 1) a))
        at h1
      rw [hĴv, hĴv] at h1
      rw [eval_hat_below M _ (hJ a r) _ (hnn r) (hleM r),
        eval_hat_below M _ (hJ a _) _ (hnn _) (hleM _)] at h1
      exact h1
  refine ⟨?_, fun T π p hrun => hbound T π p hrun, hout⟩
  -- Part 1: existence of a halting run.
  -- Step 2: an envy-free solution of `Ĵ` with all prices at least `M`.
  set B : Fin n → Fin n → ℝ := fun a r => (Ĵ.v a r).eval M with hB
  obtain ⟨π0, -, hπ0⟩ := Finset.exists_max_image (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun σ => ∑ a, B a (σ a)) ⟨1, Finset.mem_univ _⟩
  obtain ⟨q, hq⟩ := (lemma_16 B π0).mpr (fun σ => hπ0 σ (Finset.mem_univ _))
  set S0 : ℝ := ∑ r, |q r| with hS0
  have hqS : ∀ r, -S0 ≤ q r := by
    intro r
    have : |q r| ≤ S0 := Finset.single_le_sum (f := fun r => |q r|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ r)
    linarith [neg_abs_le (q r)]
  set p0 : Fin n → ℝ := fun r => q r + S0 + M with hp0
  have hp0M : ∀ r, M ≤ p0 r := fun r => by simp only [hp0]; linarith [hqS r]
  have hEF0 : IsEF Ĵ π0 p0 := by
    intro a r
    show (Ĵ.v a r).eval (p0 r) ≤ (Ĵ.v a (π0 a)).eval (p0 (π0 a))
    rw [hĴv, hĴv]
    rw [eval_hat_above M hM0 _ _ (hp0M r), eval_hat_above M hM0 _ _ (hp0M _)]
    have := hq a r
    simp only [hB] at this
    simp only [hp0]
    change (Ĵ.v a r).eval M - (q r + S0 + M - M) ≤
      (Ĵ.v a (π0 a)).eval M - (q (π0 a) + S0 + M - M)
    linarith
  -- the step function
  have hstepEx : ∀ (x : Fin n → ℝ), ∃ y : Equiv.Perm (Fin n) × (Fin n → ℝ),
      (∃ σ z, IsMaxWeightPM Ĵ x σ ∧ IsLPOpt Ĵ (domL Ĵ x) (domU Ĵ x) σ z) →
        IsMaxWeightPM Ĵ x y.1 ∧ IsLPOpt Ĵ (domL Ĵ x) (domU Ĵ x) y.1 y.2 := by
    intro x
    by_cases h : ∃ σ z, IsMaxWeightPM Ĵ x σ ∧ IsLPOpt Ĵ (domL Ĵ x) (domU Ĵ x) σ z
    · obtain ⟨σ, z, h1, h2⟩ := h
      exact ⟨(σ, z), fun _ => ⟨h1, h2⟩⟩
    · exact ⟨(1, x), fun h' => absurd h' h⟩
  choose nxt hnxt using hstepEx
  let seq : ℕ → Equiv.Perm (Fin n) × (Fin n → ℝ) := fun k =>
    Nat.rec (π0, p0) (fun _ st => nxt st.2) k
  set πs : ℕ → Equiv.Perm (Fin n) := fun k => (seq k).1 with hπs
  set ps : ℕ → Fin n → ℝ := fun k => (seq k).2 with hps
  have hseq : ∀ k, seq (k + 1) = nxt (ps k) := fun k => rfl
  have hrunT : ∀ T, (∀ i < T, ∀ r, 0 < ps i r) → IsRun J M T πs ps := by
    intro T
    induction T with
    | zero =>
      intro _
      refine ⟨hEF0, hp0M, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ T ih =>
      intro hpos
      have hrun := ih (fun i hi => hpos i (by omega))
      obtain ⟨_, hmax, hlp⟩ := (lemma_3 J M hJ hM T πs ps hrun) T le_rfl
      obtain ⟨σ, hσ⟩ := hmax
      obtain ⟨z, hz⟩ := hlp σ hσ
      have hn := hnxt (ps T) ⟨σ, z, hσ, hz⟩
      refine ⟨hrun.1, hrun.2.1, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact hrun.2.2 i hi
      · subst hi
        refine ⟨hpos i (by omega), ?_, ?_⟩
        · show IsMaxWeightPM Ĵ (ps i) (seq (i + 1)).1
          rw [hseq]; exact hn.1
        · show IsLPOpt Ĵ (domL Ĵ (ps i)) (domU Ĵ (ps i)) (seq (i + 1)).1 (seq (i + 1)).2
          rw [hseq]; exact hn.2
  have hex : ∃ T, Halted ps T := by
    by_contra hcon
    push_neg at hcon
    have hpos : ∀ i r, 0 < ps i r := by
      intro i r
      have := hcon i
      unfold Halted at this
      push_neg at this
      exact this r
    set N := ⌈(50 : ℝ) * X ^ 50⌉₊ + 1
    have := hbound N πs ps (hrunT N (fun i _ r => hpos i r))
    have h2 : (50 : ℝ) * X ^ 50 ≤ ⌈(50 : ℝ) * X ^ 50⌉₊ := Nat.le_ceil _
    have h3 : (N : ℝ) = ⌈(50 : ℝ) * X ^ 50⌉₊ + 1 := by simp [N]
    linarith
  refine ⟨Nat.find hex, πs, ps, ?_, Nat.find_spec hex⟩
  apply hrunT
  intro i hi r
  have := Nat.find_min hex hi
  unfold Halted at this
  push_neg at this
  exact this r
