-- Prove2me | solution 2 for FakeUserRanking.FORC.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:14:39.208985+00:00
-- url     : https://prove2.me/submissions/bf3dd680-7ff0-4d5a-8274-417ec402af9c

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent
import Theorems.Thm_FakeUserRanking_FORC_lemma_1
import Theorems.Thm_FakeUserRanking_FORC_lemma_9
import Theorems.Thm_FakeUserRanking_FORC_lemma_10_goodEvent

set_option autoImplicit false

open FakeUserRanking.FORC

namespace SolTheorem3

variable {n L T : ℕ}

lemma S_eq (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) =
    ∑ i ∈ Finset.range (L - 1), (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + i + 1 = i + 2 by ring, pow_add]
  norm_num
  ring

lemma S_le (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 2 := by
  rw [S_eq, ← Finset.mul_sum]
  have := sum_geometric_two_le (L - 1)
  linarith

lemma levelW_nonneg (L : ℕ) (k : Fin L) : 0 ≤ levelW L k := by
  unfold levelW
  split_ifs
  · linarith [S_le L]
  · positivity

lemma levelW_sum (L : ℕ) (hL : 1 ≤ L) : ∑ k : Fin L, levelW L k = 1 := by
  unfold levelW
  rw [Fin.sum_univ_eq_sum_range (fun m => if m = 0 then 1 - ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1)
    else (1 / 2 : ℝ) ^ (m + 1)) L]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, if_true]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have : ∀ i ∈ Finset.range L', (1 / 2 : ℝ) ^ (1 + i + 1) = (1 / 2 : ℝ) ^ (i + 1 + 1) := by
    intro i _; rw [show 1 + i + 1 = i + 1 + 1 by ring]
  rw [Finset.sum_congr rfl this]
  ring

def DepBelow (m : ℕ) {β : Type*} (f : (Fin T → Step n L) → β) : Prop :=
  ∀ τ τ' : Fin T → Step n L, (∀ i : Fin T, (i : ℕ) < m → τ i = τ' i) → f τ = f τ'

lemma algHist_dep (s : ℕ) : DepBelow (T := T) (n := n) (L := L) s (fun τ => algHist τ s) := by
  intro τ τ' h
  beta_reduce
  unfold algHist
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp at h1; simp; omega

lemma ranking_dep (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => ranking A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold ranking
  have e := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  beta_reduce at e
  rw [e, h s (by omega)]

lemma pubHist_dep (A : Alg n L) (s : ℕ) : DepBelow (T := T) s (fun τ => pubHist A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold pubHist
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp at h1
    have e := ranking_dep A ⟨i, by omega⟩ τ τ' (fun j hj => h j (by simp at hj; omega))
    beta_reduce at e
    rw [e, h ⟨i, by omega⟩ (by simp; omega)]

lemma stepW_dep (inst : Instance n) (P : Adversary n) (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => stepW inst P A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold stepW
  have e1 := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  have e2 := pubHist_dep A s τ τ' (fun i hi => h i (by omega))
  have e3 := ranking_dep A s τ τ' h
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, h s (by omega)]

lemma update_agree (τ : Fin T → Step n L) (m : Fin T) (x : Step n L) :
    ∀ i : Fin T, (i : ℕ) < m → Function.update τ m x i = τ i := by
  intro i hi
  exact Function.update_of_ne (by intro h; rw [h] at hi; exact lt_irrefl _ hi) _ _

noncomputable def Wm (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (τ : Fin T → Step n L) : ℝ :=
  ∏ s : Fin T, if (s : ℕ) < m then stepW inst P A τ s else (Fintype.card (Step n L) : ℝ)⁻¹

noncomputable def Em (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (g : (Fin T → Step n L) → ℝ) : ℝ :=
  ∑ τ, Wm inst P A m τ * g τ

lemma sum_update_eq {α : Type*} [Fintype α] [DecidableEq α] (F : (Fin T → α) → ℝ) (m : Fin T) :
    ∑ τ, ∑ x, F (Function.update τ m x) = (Fintype.card α : ℝ) * ∑ τ, F τ := by
  let Φ : (Fin T → α) × α → (Fin T → α) × α := fun p => (Function.update p.1 m p.2, p.1 m)
  have hΦ : Function.Involutive Φ := by
    intro p; simp [Φ]
  calc ∑ τ, ∑ x, F (Function.update τ m x) = ∑ p : (Fin T → α) × α, F (Φ p).1 := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : (Fin T → α) × α, F p.1 :=
        Fintype.sum_equiv (hΦ.toPerm Φ) _ _ (fun p => rfl)
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [Finset.sum_const, Finset.mul_sum]

lemma Wm_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Wm inst P A (m + 1) (Function.update τ m x) =
      (Fintype.card (Step n L) : ℝ) * Wm inst P A m τ * stepW inst P A (Function.update τ m x) m := by
  unfold Wm
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase Finset.univ (fun s : Fin T => if (s : ℕ) < m then stepW inst P A τ s
      else (Fintype.card (Step n L) : ℝ)⁻¹) (Finset.mem_univ m)]
  simp only [lt_add_iff_pos_right, lt_irrefl, if_false, Nat.lt_succ_self, if_true]
  have hrest : ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < (m : ℕ) + 1 then
      stepW inst P A (Function.update τ m x) s else (Fintype.card (Step n L) : ℝ)⁻¹) =
      ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < m then stepW inst P A τ s
        else (Fintype.card (Step n L) : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro s hs
    have hsm : s ≠ m := Finset.ne_of_mem_erase hs
    have hsm' : (s : ℕ) ≠ m := fun h => hsm (Fin.ext h)
    by_cases hlt : (s : ℕ) < m
    · rw [if_pos (by omega), if_pos hlt]
      have e := stepW_dep inst P A s _ _ (fun i hi => update_agree τ m x i (by omega))
      beta_reduce at e
      exact e
    · rw [if_neg (by omega), if_neg hlt]
  rw [hrest]
  field_simp

lemma Em_step (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (g : (Fin T → Step n L) → ℝ) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (m + 1) g = Em inst P A m (fun τ => ∑ x, stepW inst P A (Function.update τ m x) m *
      g (Function.update τ m x)) := by
  unfold Em
  have := sum_update_eq (fun τ => Wm inst P A (m + 1) τ * g τ) m
  have e : ∑ τ, Wm inst P A (m + 1) τ * g τ =
      (Fintype.card (Step n L) : ℝ)⁻¹ * ∑ τ, ∑ x, Wm inst P A (m + 1) (Function.update τ m x) *
        g (Function.update τ m x) := by
    rw [this]; field_simp
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Wm_update inst P A m τ x hN]
  field_simp

lemma stepW_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) :
    stepW inst P A (Function.update τ m x) m = A.w (algHist τ m) x.1 *
      (P (pubHist A τ m) x.2.1).toReal * obsW inst (A.rank (algHist τ m) x.1) x.2.1 x.2.2 := by
  unfold stepW ranking
  have e1 := algHist_dep (n := n) (L := L) m _ τ (update_agree τ m x)
  have e2 := pubHist_dep A m _ τ (update_agree τ m x)
  beta_reduce at e1 e2
  rw [Function.update_self, e1, e2]

lemma Em_zero_const (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) (c : ℝ) :
    Em inst P A (T := T) 0 (fun _ => c) = c := by
  unfold Em Wm
  simp only [Nat.not_lt_zero, if_false, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hN.ne', one_pow, one_mul]

lemma expect_eq_Em_T (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (g : (Fin T → Step n L) → ℝ) :
    expect inst P A T g = Em inst P A T g := by
  unfold expect Em trajW Wm
  apply Finset.sum_congr rfl
  intro τ _
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  rw [if_pos s.isLt]

def pubHist1 {n T : ℕ} (u : Fin T → Action n × Obs n) (t : ℕ) : List (PubStep n) :=
  (List.ofFn (fun s : Fin T => ((1 : Equiv.Perm (Fin n)), (u s).1.isSome, (u s).2))).take t

lemma pubHist_eq_pubHist1 (A : Alg n L) (hrank : ∀ h k, A.rank h k = 1)
    (τ : Fin T → Step n L) (t : ℕ) :
    pubHist A τ t = pubHist1 (fun s => (τ s).2) t := by
  unfold pubHist pubHist1 ranking
  simp [hrank]

lemma pubHist1_dep {n T : ℕ} (t : ℕ) (u u' : Fin T → Action n × Obs n)
    (h : ∀ i : Fin T, (i : ℕ) < t → u i = u' i) :
    pubHist1 u t = pubHist1 u' t := by
  unfold pubHist1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp at h1
    rw [h ⟨i, by omega⟩ (by simp; omega)]

lemma snd_update (τ : Fin T → Step n L) (m : Fin T) (k : Fin L) (y : Action n × Obs n) :
    (fun s => (Function.update τ m (k, y) s).2) = Function.update (fun s => (τ s).2) m y := by
  funext s
  by_cases h : s = m
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma stepW_sum_rank_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hrank : ∀ h k, A.rank h k = 1)
    (m : Fin T) (τ : Fin T → Step n L) (G : (Fin T → Action n × Obs n) → ℝ) :
    (∑ x : Step n L, stepW inst P A (Function.update τ m x) m *
      G (fun s => (Function.update τ m x s).2)) =
    ∑ y : Action n × Obs n, (P (pubHist1 (fun s => (τ s).2) m) y.1).toReal *
      obsW inst 1 y.1 y.2 * G (Function.update (fun s => (τ s).2) m y) := by
  rw [Fintype.sum_prod_type]
  simp only [stepW_update, hrank, pubHist_eq_pubHist1 A hrank, snd_update]
  have hfactor : ∀ k : Fin L,
      (∑ y : Action n × Obs n, A.w (algHist τ m) k *
        (P (pubHist1 (fun s => (τ s).2) m) y.1).toReal * obsW inst 1 y.1 y.2 *
        G (Function.update (fun s => (τ s).2) m y)) =
      A.w (algHist τ m) k * ∑ y : Action n × Obs n,
        (P (pubHist1 (fun s => (τ s).2) m) y.1).toReal * obsW inst 1 y.1 y.2 *
        G (Function.update (fun s => (τ s).2) m y) := by
    intro k
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _; ring
  simp only [hfactor, ← Finset.sum_mul, hw_sum, one_mul]

lemma Em_eq_optAlg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hrank : ∀ h k, A.rank h k = 1)
    (hn : 1 ≤ n) (hL : 1 ≤ L) :
    ∀ m ≤ T, ∀ (G : (Fin T → Action n × Obs n) → ℝ),
      (∀ u u' : Fin T → Action n × Obs n, (∀ i : Fin T, (i : ℕ) < m → u i = u' i) → G u = G u') →
      Em inst P A m (fun τ => G (fun s => (τ s).2)) =
        Em inst P (optAlg n) m (fun σ => G (fun s => (σ s).2)) := by
  have hN : (0 : ℝ) < Fintype.card (Step n L) := by
    have : Nonempty (Step n L) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hN1 : (0 : ℝ) < Fintype.card (Step n 1) := by
    have : Nonempty (Step n 1) := ⟨(⟨0, by norm_num⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hOw : ∀ h, ∑ k, (optAlg n).w h k = 1 := by intro h; simp [optAlg]
  have hOr : ∀ h k, (optAlg n).rank h k = 1 := by intro h k; rfl
  let u0 : Fin T → Action n × Obs n := fun _ => (none, (⟨0, hn⟩, true))
  intro m
  induction m with
  | zero =>
    intro _ G hG
    have h1 : (fun τ : Fin T → Step n L => G (fun s => (τ s).2)) = fun _ => G u0 := by
      funext τ; exact hG _ _ (fun i hi => absurd hi (Nat.not_lt_zero _))
    have h2 : (fun σ : Fin T → Step n 1 => G (fun s => (σ s).2)) = fun _ => G u0 := by
      funext σ; exact hG _ _ (fun i hi => absurd hi (Nat.not_lt_zero _))
    rw [h1, h2, Em_zero_const inst P A hN, Em_zero_const inst P (optAlg n) hN1]
  | succ m ih =>
    intro hm G hG
    let m' : Fin T := ⟨m, by omega⟩
    have hstepA := Em_step inst P A m' (fun τ => G (fun s => (τ s).2)) hN
    have hstepO := Em_step inst P (optAlg n) m' (fun σ => G (fun s => (σ s).2)) hN1
    change Em inst P A (m + 1) _ = Em inst P (optAlg n) (m + 1) _
    rw [hstepA, hstepO]
    simp only [stepW_sum_rank_one inst P A hw_sum hrank m',
      stepW_sum_rank_one inst P (optAlg n) hOw hOr m']
    refine ih (by omega) (fun u => ∑ y : Action n × Obs n,
      (P (pubHist1 u m) y.1).toReal * obsW inst 1 y.1 y.2 * G (Function.update u m' y)) ?_
    intro u u' hu
    have hp : pubHist1 u m = pubHist1 u' m := pubHist1_dep m u u' hu
    rw [hp]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply hG
    intro i hi
    by_cases him : i = m'
    · subst him; simp
    · have hlt : (i : ℕ) < m := by
        have : (i : ℕ) ≠ m := fun h => him (Fin.ext h)
        omega
      rw [Function.update_of_ne him, Function.update_of_ne him, hu i hlt]

lemma regret_eq_zero_of_rank_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hrank : ∀ h k, A.rank h k = 1)
    (hn : 1 ≤ n) (hL : 1 ≤ L) :
    regret inst P A T = 0 := by
  unfold regret
  rw [expect_eq_Em_T, expect_eq_Em_T]
  let G_rew : (Fin T → Action n × Obs n) → ℝ :=
    fun u => ∑ s : Fin T, if (u s).1 = none ∧ (u s).2.2 = true then 1 else 0
  have hrewA : (reward : (Fin T → Step n L) → ℝ) = fun τ => G_rew (fun s => (τ s).2) := rfl
  have hrewO : (reward : (Fin T → Step n 1) → ℝ) = fun σ => G_rew (fun s => (σ s).2) := rfl
  rw [hrewA, hrewO, Em_eq_optAlg inst P A hw_sum hrank hn hL T le_rfl G_rew]
  · ring
  · intro u u' hu
    unfold G_rew
    apply Finset.sum_congr rfl
    intro s _
    rw [hu s s.isLt]

open Classical in
lemma sum_prob_feedback_eq (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (E : (Fin T → Step n L) → Prop) :
    (∑ t : Fin T, ∑ j : Fin n, ∑ i ∈ Finset.Ioi j,
      gap inst j i * prob inst P A T (fun τ => feedbackEvent A τ t j i)) =
    expect inst P A T (fun τ => (if E τ then 1 else 0) *
      ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
        ∑ t : Fin T, (if feedbackEvent A τ t j i then 1 else 0)) +
    expect inst P A T (fun τ => (if E τ then 0 else 1) *
      ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
        ∑ t : Fin T, (if feedbackEvent A τ t j i then 1 else 0)) := by
  have h1 : (∑ t : Fin T, ∑ j : Fin n, ∑ i ∈ Finset.Ioi j,
      gap inst j i * prob inst P A T (fun τ => feedbackEvent A τ t j i)) =
    expect inst P A T (fun τ =>
      ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
        ∑ t : Fin T, (if feedbackEvent A τ t j i then 1 else 0)) := by
    unfold prob expect
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro τ _
    apply Finset.sum_congr rfl; intro t _
    ring
  rw [h1]
  unfold expect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  dsimp only
  by_cases hE : E τ <;> simp [hE]

lemma rhs_ge_one (n T : ℕ) (hn : 2 ≤ n) (hT : 2 ≤ T) (inst : Instance n) (hμ : StrictAnti inst.μ) :
    1 ≤ ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 1 ≤ Real.log ((n : ℝ) * T) := by
    have hexp_half : Real.exp (1 / 2) ≤ 2 := by
      have h1 := Real.add_one_le_exp (-(1 / 2 : ℝ))
      have h2 : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have hexp : Real.exp 1 ≤ (n : ℝ) * T := by
      have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log ((n : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) hexp
  have hnn : ∀ j : Fin n, ∀ i ∈ Finset.Ioi j,
      0 ≤ Real.log ((n : ℝ) * T) / gap inst j i := by
    intro j i hi
    have hji : j < i := Finset.mem_Ioi.mp hi
    have hgap : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
    exact div_nonneg (by linarith) hgap.le
  let j0 : Fin n := ⟨0, by omega⟩
  let i0 : Fin n := ⟨1, by omega⟩
  have hi0 : i0 ∈ Finset.Ioi j0 := by
    simp [Finset.mem_Ioi, j0, i0, Fin.lt_def]
  have hgap0_pos : 0 < gap inst j0 i0 := by
    unfold gap; have := hμ (Finset.mem_Ioi.mp hi0); linarith
  have hgap0_le : gap inst j0 i0 ≤ 1 := by
    unfold gap; linarith [(inst.μ_mem j0).2, (inst.μ_mem i0).1]
  have hterm : 1 ≤ Real.log ((n : ℝ) * T) / gap inst j0 i0 := by
    rw [one_le_div hgap0_pos]
    linarith
  have hrow : Real.log ((n : ℝ) * T) / gap inst j0 i0 ≤
      ∑ i ∈ Finset.Ioi j0, Real.log ((n : ℝ) * T) / gap inst j0 i :=
    Finset.single_le_sum (fun i hi => hnn j0 i hi) hi0
  have htot : (∑ i ∈ Finset.Ioi j0, Real.log ((n : ℝ) * T) / gap inst j0 i) ≤
      ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i :=
    Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun i hi => hnn j i hi)) (Finset.mem_univ j0)
  linarith

lemma f_plus_inv_le (n T F : ℕ) (hn : 2 ≤ n) (hT : 2 ≤ T) :
    (F : ℝ) + 1 / (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * F + Real.log T := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hF : (F : ℝ) ≤ (n : ℝ) ^ 2 * F := by
    have : (0 : ℝ) ≤ F := Nat.cast_nonneg F
    nlinarith
  have hinv : 1 / (n : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(1 / 2 : ℝ))
    have h2 : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hlogT : (1 / 2 : ℝ) ≤ Real.log T := by
    calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) (by linarith)
  linarith

end SolTheorem3

open Classical in
theorem solution :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
        regret inst P (forc n T tb fb) T ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by
  obtain ⟨C0, hC0⟩ := lemma_10_goodEvent
  refine ⟨max C0 0 + 1, fun n T F hn hT inst hμ P hP tb htb fb => ?_⟩
  set A := forc n T tb fb
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => SolTheorem3.levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun _ => SolTheorem3.levelW_sum _ hL
  rcases eq_or_lt_of_le hn with rfl | hn2
  · have hrank : ∀ h k, A.rank h k = 1 := fun h k => Subsingleton.elim _ _
    rw [SolTheorem3.regret_eq_zero_of_rank_one inst P A hw_sum hrank le_rfl hL]
    have hEmpty : ∀ j : Fin 1, (Finset.Ioi j : Finset (Fin 1)) = ∅ := by
      intro j; ext i; simp [Fin.lt_def]
    simp [hEmpty]
  · have hn2' : 2 ≤ n := hn2
    have hreg := lemma_1 T F A hw_nonneg hw_sum inst hμ P hP
    have hsplit := SolTheorem3.sum_prob_feedback_eq inst P A (goodEvent inst F tb fb)
    have h9 := lemma_9 n T F hn hT inst hμ P hP tb htb fb
    have h10 := hC0 n T F hn hT inst hμ P hP tb htb fb
    set S := ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i
    set B := ((n : ℝ) ^ 2 * F + Real.log T) * S
    have hS1 : 1 ≤ S := SolTheorem3.rhs_ge_one n T hn2' hT inst hμ
    have hFB : (F : ℝ) + 1 / (n : ℝ) ^ 2 ≤ B := by
      have h1 := SolTheorem3.f_plus_inv_le n T F hn2' hT
      have h2 : 0 ≤ (F : ℝ) + 1 / (n : ℝ) ^ 2 := by positivity
      have h3 : 0 ≤ (n : ℝ) ^ 2 * F + Real.log T := by linarith
      calc (F : ℝ) + 1 / (n : ℝ) ^ 2 ≤ ((n : ℝ) ^ 2 * F + Real.log T) * 1 := by linarith
        _ ≤ ((n : ℝ) ^ 2 * F + Real.log T) * S := mul_le_mul_of_nonneg_left hS1 h3
    have hB0 : 0 ≤ B := by
      have : 0 ≤ (F : ℝ) + 1 / (n : ℝ) ^ 2 := by positivity
      linarith
    have hC0_le : C0 * B ≤ max C0 0 * B :=
      mul_le_mul_of_nonneg_right (le_max_left C0 0) hB0
    linarith
