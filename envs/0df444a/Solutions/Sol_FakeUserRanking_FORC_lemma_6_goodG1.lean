-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_6_goodG1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:28:02.917331+00:00
-- url     : https://prove2.me/submissions/070bb086-9836-461b-8c5f-97d9d8c55d20

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent
import Theorems.Thm_FakeUserRanking_FORC_prob_goodG2_quarter
import Theorems.Thm_FakeUserRanking_FORC_goodG1_step_on_goodG2

set_option autoImplicit false

open FakeUserRanking.FORC

namespace SolProbGoodG1

open Classical

variable {n L T : ℕ}

lemma reach_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    0 ≤ reach inst π j := by
  unfold reach
  apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r _
  · linarith [(inst.q_mem r).2]
  · linarith [(inst.μ_mem (π r)).2]

lemma realW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (o : Obs n) :
    0 ≤ realW inst π o := by
  rcases o with ⟨j, b⟩
  have h1 := reach_nonneg inst π j
  have h2 := (inst.μ_mem (π j)).1
  have h3 := (inst.μ_mem (π j)).2
  have h4 := (inst.q_mem j).1
  cases b
  · simp only [realW]
    apply mul_nonneg (mul_nonneg h1 (by linarith))
    split_ifs <;> linarith
  · simp only [realW]; exact mul_nonneg h1 h2

noncomputable def rho (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  if h : m < n then reach inst π ⟨m, h⟩ else 0

lemma reach_succ (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) (h : m + 1 < n) :
    reach inst π ⟨m + 1, h⟩ = reach inst π ⟨m, by omega⟩ *
      ((1 - inst.q ⟨m, by omega⟩) * (1 - inst.μ (π ⟨m, by omega⟩))) := by
  unfold reach
  have hI : Finset.Iio (⟨m + 1, h⟩ : Fin n) = insert ⟨m, by omega⟩ (Finset.Iio ⟨m, by omega⟩) := by
    ext r; simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]; omega
  rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  ring

lemma reach_zero (inst : Instance n) (π : Equiv.Perm (Fin n)) (h : 0 < n) :
    reach inst π ⟨0, h⟩ = 1 := by
  unfold reach
  have hI : Finset.Iio (⟨0, h⟩ : Fin n) = ∅ := by
    ext r; simp [Fin.lt_def]
  simp [hI]

lemma realW_pair (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    realW inst π (j, true) + realW inst π (j, false) = rho inst π j - rho inst π (j + 1) := by
  simp only [realW, rho, dif_pos j.isLt]
  by_cases h : (j : ℕ) + 1 < n
  · rw [dif_pos h, if_pos h, reach_succ inst π j h]
    ring
  · rw [dif_neg h, if_neg h]; ring

lemma realW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (hn : 1 ≤ n) :
    ∑ o, realW inst π o = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp only [realW_pair]
  rw [Fin.sum_univ_eq_sum_range (fun m => rho inst π m - rho inst π (m + 1)) n]
  rw [Finset.sum_range_sub']
  simp [rho, dif_pos (show 0 < n by omega), reach_zero inst π (show 0 < n by omega)]

def DepBelow (m : ℕ) {β : Type*} (f : (Fin T → Step n L) → β) : Prop :=
  ∀ τ τ' : Fin T → Step n L, (∀ i : Fin T, (i : ℕ) < m → τ i = τ' i) → f τ = f τ'

lemma DepBelow.mono {m m' : ℕ} {β : Type*} {f : (Fin T → Step n L) → β} (h : DepBelow m f)
    (hm : m ≤ m') : DepBelow m' f :=
  fun τ τ' hτ => h τ τ' (fun i hi => hτ i (lt_of_lt_of_le hi hm))

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

lemma obsW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (hn : 1 ≤ n) :
    ∑ o, obsW inst π a o = 1 := by
  cases a with
  | none => exact realW_sum inst π hn
  | some a => simp [obsW]

lemma obsW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (o : Obs n) :
    0 ≤ obsW inst π a o := by
  cases a with
  | none => exact realW_nonneg inst π o
  | some a => simp only [obsW]; split_ifs <;> norm_num

lemma pmf_sum (p : PMF (Action n)) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]; simp

lemma stepW_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x, stepW inst P A (Function.update τ m x) m = 1 := by
  simp only [stepW_update]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (hw_sum (algHist τ m))
  rw [Fintype.sum_prod_type]
  simp only
  simp only [mul_assoc, ← Finset.mul_sum, obsW_sum inst _ _ hn, mul_one]
  rw [pmf_sum, mul_one]

lemma stepW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) (s : Fin T) :
    0 ≤ stepW inst P A τ s := by
  unfold stepW
  exact mul_nonneg (mul_nonneg (hw_nonneg _ _) ENNReal.toReal_nonneg) (obsW_nonneg _ _ _ _)

lemma Em_drop (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : Fin T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    Em inst P A (m + 1) g = Em inst P A m g := by
  rw [Em_step inst P A m g hN]
  congr 1
  funext τ
  have : ∀ x, g (Function.update τ m x) = g τ := fun x => hg _ _ (update_agree τ m x)
  simp only [this, ← Finset.sum_mul, stepW_sum inst P A hw_sum hn m τ, one_mul]

lemma expect_eq_Em (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : ℕ) (hm : m ≤ T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    expect inst P A T g = Em inst P A m g := by
  have hT : expect inst P A T g = Em inst P A T g := by
    unfold expect Em trajW Wm
    apply Finset.sum_congr rfl
    intro τ _
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    rw [if_pos s.isLt]
  rw [hT]
  have key : ∀ d, m + d ≤ T → Em inst P A (m + d) g = Em inst P A m g := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have := Em_drop inst P A hw_sum hn hN ⟨m + d, by omega⟩ g (hg.mono (by simp))
      simp only at this
      rw [← add_assoc, this, ih (by omega)]
  have := key (T - m) (by omega)
  rwa [show m + (T - m) = T by omega] at this

lemma Em_zero_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (T := T) 0 (fun _ => 1) = 1 := by
  unfold Em Wm
  simp only [Nat.not_lt_zero, if_false, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow]
  rw [← mul_pow, mul_inv_cancel₀ hN.ne', one_pow]

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

lemma prob_compl (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (E : (Fin T → Step n L) → Prop) :
    prob inst P A T E = 1 - prob inst P A T (fun τ => ¬ E τ) := by
  have hE1 : expect inst P A T (fun _ => 1) = 1 := by
    rw [expect_eq_Em inst P A hw_sum hn hN 0 (Nat.zero_le _) _ (fun _ _ _ => rfl),
      Em_zero_one inst P A hN]
  rw [← hE1]
  unfold prob expect
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  by_cases h : E τ <;> simp [h]

lemma union_pt {ι : Type*} [Fintype ι] (E : Prop) (Ek : ι → Prop) (h : E → ∃ k, Ek k) :
    (if E then (1 : ℝ) else 0) ≤ ∑ k, if Ek k then (1 : ℝ) else 0 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), (0 : ℝ) ≤ if Ek j then (1 : ℝ) else 0 := by
    intro j _; split_ifs <;> norm_num
  by_cases hE' : E
  · rw [if_pos hE']
    obtain ⟨k, hk'⟩ := h hE'
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ k))
    rw [if_pos hk']
  · rw [if_neg hE']
    exact Finset.sum_nonneg hnn

noncomputable def BadStep (n T F : ℕ) (inst : Instance n)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (p : Fin T × Fin (numLevels T) × Fin n)
    (τ : Fin T → Step n (numLevels T)) : Prop :=
  goodG2 F τ ∧ F ≤ 2 ^ ((p.2.1 : ℕ) + 1) ∧ ¬ (
    rHat (stateAt tb fb τ ((p.1 : ℕ) + 1)) p.2.1 p.2.2 -
      window21 n T (stateAt tb fb τ ((p.1 : ℕ) + 1)) p.2.1 p.2.2 ≤ inst.μ p.2.2 ∧
    inst.μ p.2.2 ≤
      rHat (stateAt tb fb τ ((p.1 : ℕ) + 1)) p.2.1 p.2.2 +
        window21 n T (stateAt tb fb τ ((p.1 : ℕ) + 1)) p.2.1 p.2.2)

end SolProbGoodG1

open Classical in
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)) :
    1 - delta n T / 2 ≤ prob inst P (forc n T tb fb) T (goodG1 inst F tb fb) := by
  set A := forc n T tb fb
  set δ := delta n T with hδ
  have hL : 0 < numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hN : (0 : ℝ) < Fintype.card (Step n (numLevels T)) := by
    have : Nonempty (Step n (numLevels T)) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => SolProbGoodG1.levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun _ => SolProbGoodG1.levelW_sum _ hL
  have hδ0 : 0 < δ := by rw [hδ]; unfold delta; positivity
  have hp_bound : ∀ p : Fin T × Fin (numLevels T) × Fin n,
      prob inst P A T (SolProbGoodG1.BadStep n T F inst tb fb p) ≤
        δ / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) := by
    rintro ⟨s, k, i⟩
    by_cases hk : F ≤ 2 ^ ((k : ℕ) + 1)
    · have e : SolProbGoodG1.BadStep n T F inst tb fb (s, k, i) =
          fun τ => goodG2 F τ ∧ ¬ (
            rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i -
              window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i ≤ inst.μ i ∧
            inst.μ i ≤
              rHat (stateAt tb fb τ ((s : ℕ) + 1)) k i +
                window21 n T (stateAt tb fb τ ((s : ℕ) + 1)) k i) := by
        funext τ; simp [SolProbGoodG1.BadStep, hk]
      rw [e]
      exact goodG1_step_on_goodG2 n T F hn hT inst hμ P hP tb htb fb s k hk i
    · have hz : prob inst P A T (SolProbGoodG1.BadStep n T F inst tb fb (s, k, i)) = 0 := by
        unfold prob expect SolProbGoodG1.BadStep
        simp [hk]
      rw [hz]; positivity
  have hunion : prob inst P A T (fun τ => ¬ goodG1 inst F tb fb τ) ≤
      prob inst P A T (fun τ => ¬ goodG2 F τ) +
        ∑ p : Fin T × Fin (numLevels T) × Fin n,
          prob inst P A T (SolProbGoodG1.BadStep n T F inst tb fb p) := by
    unfold prob expect
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro τ _
    beta_reduce
    rw [← Finset.mul_sum, ← mul_add]
    have hW : 0 ≤ trajW inst P A T τ :=
      Finset.prod_nonneg (fun s _ => SolProbGoodG1.stepW_nonneg inst P A hw_nonneg τ s)
    apply mul_le_mul_of_nonneg_left _ hW
    by_cases hg2 : goodG2 F τ
    · simp only [hg2, not_true_eq_false, if_false, zero_add]
      refine SolProbGoodG1.union_pt (E := ¬ goodG1 inst F tb fb τ)
        (Ek := fun p => SolProbGoodG1.BadStep n T F inst tb fb p τ) ?_
      intro hnot1
      by_contra hno
      apply hnot1
      intro t ht1 htT k hk i
      by_contra hfail
      apply hno
      let s : Fin T := ⟨t - 1, by omega⟩
      have hs : (s : ℕ) + 1 = t := by dsimp [s]; omega
      exact ⟨(s, k, i), hg2, hk, by rwa [hs]⟩
    · simp only [hg2, not_false_eq_true, if_true]
      by_cases h1 : goodG1 inst F tb fb τ
      · simp [h1]; positivity
      · simp [h1]
  have hsum : (∑ p : Fin T × Fin (numLevels T) × Fin n,
      prob inst P A T (SolProbGoodG1.BadStep n T F inst tb fb p)) ≤ δ / 4 := by
    calc _ ≤ ∑ _p : Fin T × Fin (numLevels T) × Fin n,
            δ / (4 * (T : ℝ) * (numLevels T : ℝ) * (n : ℝ)) :=
          Finset.sum_le_sum (fun p _ => hp_bound p)
      _ = δ / 4 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul]
          have hT0 : (T : ℝ) ≠ 0 := by positivity
          have hL0 : (numLevels T : ℝ) ≠ 0 := by positivity
          have hn0 : (n : ℝ) ≠ 0 := by positivity
          field_simp
  have hg2_q := prob_goodG2_quarter n T F hn hT inst hμ P hP tb htb fb
  rw [SolProbGoodG1.prob_compl inst P A hw_sum hn hN] at hg2_q ⊢
  linarith
