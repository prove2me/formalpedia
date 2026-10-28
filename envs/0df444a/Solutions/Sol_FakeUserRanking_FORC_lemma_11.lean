-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:10:04.7071+00:00
-- url     : https://prove2.me/submissions/6776f5e5-5af3-4f26-85a7-b50754f41e1a

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

open FakeUserRanking.FORC

namespace L1Aux

variable {n : ℕ}

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

/-- reach extended to ℕ, zero from `n` on. -/
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

lemma tele (f : ℕ → ℝ) (j N : ℕ) (h : j ≤ N) :
    ∑ m ∈ Finset.range N, (if j ≤ m then f m - f (m + 1) else 0) = f j - f N := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]; · ring
    intro m hm; simp at hm; rw [if_neg (by omega)]
  | succ N hle ih =>
    rw [Finset.sum_range_succ, ih, if_pos hle]; ring

lemma realW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (hn : 1 ≤ n) :
    ∑ o, realW inst π o = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp only [realW_pair]
  rw [Fin.sum_univ_eq_sum_range (fun m => rho inst π m - rho inst π (m + 1)) n]
  rw [Finset.sum_range_sub']
  simp [rho, dif_pos (show 0 < n by omega), reach_zero inst π (show 0 < n by omega)]

noncomputable def SS (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) : ℝ :=
  ∑ o, realW inst π o * (if j ≤ o.1 then 1 else 0)

lemma SS_eq (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    SS inst π j = reach inst π j := by
  unfold SS
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have : ∀ j' : Fin n, realW inst π (j', true) * (if j ≤ (j', true).1 then 1 else 0) +
      realW inst π (j', false) * (if j ≤ (j', false).1 then 1 else 0) =
      (if (j : ℕ) ≤ (j' : ℕ) then rho inst π j' - rho inst π (j' + 1) else 0) := by
    intro j'
    rw [← realW_pair]
    simp only [Fin.le_def]
    split_ifs <;> ring
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun m => if (j : ℕ) ≤ m then rho inst π m - rho inst π (m + 1)
    else 0) n]
  rw [tele _ _ _ j.isLt.le]
  simp [rho, j.isLt]

noncomputable def rr (inst : Instance n) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ o, realW inst π o * (if o.2 = true then 1 else 0)

lemma rr_eq (inst : Instance n) (π : Equiv.Perm (Fin n)) :
    rr inst π = ∑ j : Fin n, reach inst π j * inst.μ (π j) := by
  unfold rr
  rw [Fintype.sum_prod_type]
  simp [realW]

/-! hybrid argument in ℕ-indexing -/

noncomputable def aP (inst : Instance n) (π : Equiv.Perm (Fin n)) (r : ℕ) : ℝ :=
  if h : r < n then (1 - inst.q ⟨r, h⟩) * (1 - inst.μ (π ⟨r, h⟩)) else 1

noncomputable def RR (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, aP inst π r

lemma reach_eq_RR (inst : Instance n) (π : Equiv.Perm (Fin n)) :
    ∀ m (h : m < n), reach inst π ⟨m, h⟩ = RR inst π m := by
  intro m
  induction m with
  | zero => intro h; rw [reach_zero]; simp [RR]
  | succ m ih =>
    intro h
    rw [reach_succ inst π m h, ih (by omega)]
    show _ = ∏ r ∈ Finset.range (m + 1), aP inst π r
    rw [Finset.prod_range_succ, aP, dif_pos (by omega)]
    rfl

lemma aP_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (r : ℕ) : 0 ≤ aP inst π r := by
  unfold aP; split_ifs with h
  · apply mul_nonneg
    · linarith [(inst.q_mem ⟨r, h⟩).2]
    · linarith [(inst.μ_mem (π ⟨r, h⟩)).2]
  · norm_num

lemma RR_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) : 0 ≤ RR inst π m :=
  Finset.prod_nonneg (fun r _ => aP_nonneg inst π r)

noncomputable def mE (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : ℕ) : ℝ :=
  if h : j < n then inst.μ (π ⟨j, h⟩) else 0

noncomputable def Wv (inst : Instance n) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico m n, (∏ r ∈ Finset.Ico m j, aP inst 1 r) * mE inst 1 j

lemma Wv_succ (inst : Instance n) (m : ℕ) (hm : m < n) :
    Wv inst m = mE inst 1 m + aP inst 1 m * Wv inst (m + 1) := by
  unfold Wv
  rw [Finset.sum_eq_sum_Ico_succ_bot hm, Finset.mul_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro j hj
    simp at hj
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    ring

lemma Wv_n (inst : Instance n) : Wv inst n = 0 := by simp [Wv]

lemma Wv_bounds (inst : Instance n) : ∀ d m, m + d = n → 0 ≤ Wv inst m ∧ Wv inst m ≤ 1 := by
  intro d
  induction d with
  | zero => intro m hm; subst hm; simp [Wv_n]
  | succ d ih =>
    intro m hm
    have hlt : m < n := by omega
    obtain ⟨h0, h1⟩ := ih (m + 1) (by omega)
    rw [Wv_succ inst m hlt]
    simp only [mE, aP, dif_pos hlt, Equiv.Perm.one_apply]
    have a1 := (inst.μ_mem ⟨m, hlt⟩).1
    have a2 := (inst.μ_mem ⟨m, hlt⟩).2
    have b1 := (inst.q_mem ⟨m, hlt⟩).1
    have b2 := (inst.q_mem ⟨m, hlt⟩).2
    have c0 : 0 ≤ (1 - inst.q ⟨m, hlt⟩) * (1 - inst.μ ⟨m, hlt⟩) := mul_nonneg (by linarith) (by linarith)
    constructor
    · nlinarith
    · have : (1 - inst.q ⟨m, hlt⟩) * (1 - inst.μ ⟨m, hlt⟩) ≤ 1 - inst.μ ⟨m, hlt⟩ := by nlinarith
      nlinarith

noncomputable def HH (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, RR inst π j * mE inst π j + RR inst π m * Wv inst m

lemma HH_diff (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) (hm : m < n) :
    HH inst π m - HH inst π (m + 1) = RR inst π m * (mE inst 1 m - mE inst π m) *
      (1 - (1 - inst.q ⟨m, hm⟩) * Wv inst (m + 1)) := by
  unfold HH
  rw [Finset.sum_range_succ, Wv_succ inst m hm]
  have hR : RR inst π (m + 1) = RR inst π m * aP inst π m := by
    unfold RR; rw [Finset.prod_range_succ]
  rw [hR]
  simp only [aP, mE, dif_pos hm, Equiv.Perm.one_apply]
  ring

lemma comb (inst : Instance n) (hμ : StrictAnti inst.μ) (π : Equiv.Perm (Fin n)) :
    rr inst 1 - rr inst π ≤ ∑ j : Fin n, ∑ i ∈ Finset.Ioi j,
      gap inst j i * (if π j = i then SS inst π j else 0) := by
  have h0 : HH inst π 0 = rr inst 1 := by
    unfold HH
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    rw [rr_eq, RR, Finset.prod_range_zero, one_mul, Wv]
    rw [← Finset.range_eq_Ico]
    rw [← Fin.sum_univ_eq_sum_range (fun j => (∏ r ∈ Finset.Ico 0 j, aP inst 1 r) * mE inst 1 j) n]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.range_eq_Ico, ← RR, ← reach_eq_RR inst 1 j j.isLt]
    simp [mE, j.isLt]
  have hN : HH inst π n = rr inst π := by
    unfold HH
    rw [Wv_n, mul_zero, add_zero, rr_eq]
    rw [← Fin.sum_univ_eq_sum_range (fun j => RR inst π j * mE inst π j) n]
    apply Finset.sum_congr rfl
    intro j _
    rw [← reach_eq_RR inst π j j.isLt]
    simp [mE, j.isLt]
  rw [← h0, ← hN, ← Finset.sum_range_sub' (HH inst π) n]
  rw [← Fin.sum_univ_eq_sum_range (fun m => HH inst π m - HH inst π (m + 1)) n]
  apply Finset.sum_le_sum
  intro j _
  rw [HH_diff inst π j j.isLt]
  simp only [SS_eq, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  have hR := RR_nonneg inst π j
  have hRj : reach inst π j = RR inst π j := reach_eq_RR inst π j j.isLt
  obtain ⟨w0, w1⟩ := Wv_bounds inst (n - (j + 1)) (j + 1) (by omega)
  have q0 := (inst.q_mem j).1
  have q1 := (inst.q_mem j).2
  have c0 : 0 ≤ 1 - (1 - inst.q ⟨j, j.isLt⟩) * Wv inst (j + 1) := by
    have : (1 - inst.q ⟨j, j.isLt⟩) * Wv inst (j + 1) ≤ 1 := by
      have : (1 - inst.q ⟨j, j.isLt⟩) ≤ 1 := by linarith
      nlinarith
    linarith
  have c1 : 1 - (1 - inst.q ⟨j, j.isLt⟩) * Wv inst (j + 1) ≤ 1 := by
    have : 0 ≤ (1 - inst.q ⟨j, j.isLt⟩) * Wv inst (j + 1) := mul_nonneg (by linarith) w0
    linarith
  have hm1 : mE inst 1 j = inst.μ j := by simp [mE, j.isLt]
  have hmp : mE inst π j = inst.μ (π j) := by simp [mE, j.isLt]
  rw [hm1, hmp, hRj]
  split_ifs with hmem
  · -- j < π j
    simp only [Finset.mem_Ioi] at hmem
    have hg : gap inst j (π j) = inst.μ j - inst.μ (π j) := rfl
    have hpos : 0 ≤ inst.μ j - inst.μ (π j) := by have := hμ hmem; linarith
    rw [hg]
    have := mul_nonneg hR hpos
    nlinarith
  · simp only [Finset.mem_Ioi, not_lt] at hmem
    have : inst.μ j ≤ inst.μ (π j) := hμ.antitone hmem
    have : RR inst π j * (inst.μ j - inst.μ (π j)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hR (by linarith)
    nlinarith

end L1Aux

namespace L1Aux

variable {n L T : ℕ}

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
  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, lt_irrefl, if_false, Nat.lt_succ_self, if_true]
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

lemma Wm_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (m : ℕ) (τ : Fin T → Step n L) : 0 ≤ Wm inst P A m τ := by
  unfold Wm
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact stepW_nonneg inst P A hw_nonneg τ s
  · positivity

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

end L1Aux

namespace L1Aux

variable {n L T : ℕ}

lemma expect_step (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (t : Fin T) (Ψ : List (Fin L × Obs n) → Step n L → ℝ) :
    expect inst P A T (fun τ => Ψ (algHist τ t) (τ t)) =
      Em (T := T) inst P A t (fun τ => ∑ x : Step n L, A.w (algHist τ t) x.1 *
        (P (pubHist A τ t) x.2.1).toReal * obsW inst (A.rank (algHist τ t) x.1) x.2.1 x.2.2 *
          Ψ (algHist τ t) x) := by
  have hdep : DepBelow (t + 1) (fun τ : Fin T → Step n L => Ψ (algHist τ t) (τ t)) := by
    intro τ τ' h
    beta_reduce
    have e := algHist_dep (n := n) (L := L) t τ τ' (fun i hi => h i (by omega))
    beta_reduce at e
    rw [e, h t (by omega)]
  rw [expect_eq_Em (T := T) inst P A hw_sum hn hN (t + 1) t.isLt _ hdep]
  rw [Em_step inst P A t _ hN]
  congr 1
  funext τ
  apply Finset.sum_congr rfl
  intro x _
  have e := algHist_dep (n := n) (L := L) t _ τ (update_agree τ t x)
  beta_reduce at e
  rw [stepW_update, Function.update_self, e]

lemma inner_none (inst : Instance n) (A : Alg n L) (h : List (Fin L × Obs n))
    (p : PMF (Action n)) (Ψ : Step n L → ℝ) (hΨ : ∀ k a o, Ψ (k, some a, o) = 0) :
    ∑ x : Step n L, A.w h x.1 * (p x.2.1).toReal * obsW inst (A.rank h x.1) x.2.1 x.2.2 * Ψ x =
      ∑ k, A.w h k * (p none).toReal * ∑ o, realW inst (A.rank h k) o * Ψ (k, none, o) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp [hΨ, obsW, Finset.mul_sum, mul_assoc]

lemma click_step (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (t : Fin T) :
    expect inst P A T (fun τ => realClick (τ t)) =
      Em (T := T) inst P A t (fun τ => ∑ k, A.w (algHist τ t) k * (P (pubHist A τ t) none).toReal *
        rr inst (A.rank (algHist τ t) k)) := by
  rw [expect_step inst P A hw_sum hn hN t (fun _ x => realClick x)]
  congr 1
  funext τ
  rw [inner_none inst A _ _ _ (fun k a o => by simp [realClick])]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  unfold rr
  apply Finset.sum_congr rfl
  intro o _
  simp [realClick]

lemma real_step (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (t : Fin T) :
    expect inst P A T (fun τ => if (τ t).2.1 = none then 1 else 0) =
      Em (T := T) inst P A t (fun τ => (P (pubHist A τ t) none).toReal) := by
  rw [expect_step inst P A hw_sum hn hN t (fun _ x => if x.2.1 = none then 1 else 0)]
  congr 1
  funext τ
  rw [inner_none inst A _ _ _ (fun k a o => by simp)]
  simp only [if_true, mul_one, realW_sum inst _ hn]
  rw [← Finset.sum_mul, hw_sum, one_mul]

open Classical in
lemma fb_step (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (t : Fin T) (j i : Fin n) :
    prob inst P A T (fun τ => feedbackEvent A τ t j i) =
      Em (T := T) inst P A t (fun τ => ∑ k, A.w (algHist τ t) k * (P (pubHist A τ t) none).toReal *
        (if A.rank (algHist τ t) k j = i then SS inst (A.rank (algHist τ t) k) j else 0)) := by
  have e : (fun τ : Fin T → Step n L => if feedbackEvent A τ t j i then (1 : ℝ) else 0) =
      fun τ => (fun h (x : Step n L) => if A.rank h x.1 j = i ∧ x.2.1 = none ∧ j ≤ x.2.2.1
        then (1 : ℝ) else 0) (algHist τ t) (τ t) := by
    funext τ
    beta_reduce
    by_cases hf : feedbackEvent A τ t j i
    · have hf' : A.rank (algHist τ t) (τ t).1 j = i ∧ (τ t).2.1 = none ∧ j ≤ (τ t).2.2.1 := hf
      rw [if_pos hf, if_pos hf']
    · have hf' : ¬ (A.rank (algHist τ t) (τ t).1 j = i ∧ (τ t).2.1 = none ∧ j ≤ (τ t).2.2.1) := hf
      rw [if_neg hf, if_neg hf']
  unfold prob
  rw [e]
  refine (expect_step inst P A hw_sum hn hN t (fun h (x : Step n L) =>
    if A.rank h x.1 j = i ∧ x.2.1 = none ∧ j ≤ x.2.2.1 then (1 : ℝ) else 0)).trans ?_
  congr 1
  funext τ
  beta_reduce
  rw [inner_none inst A _ _ _ (fun k a o => by simp)]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  by_cases hr : A.rank (algHist τ t) k j = i
  · simp [hr, SS]
  · simp [hr]

lemma expect_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (f : Fin T → (Fin T → Step n L) → ℝ) :
    expect inst P A T (fun τ => ∑ t, f t τ) = ∑ t, expect inst P A T (f t) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma Em_mono (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (m : ℕ) (f g : (Fin T → Step n L) → ℝ)
    (hfg : ∀ τ, f τ ≤ g τ) : Em (T := T) inst P A m f ≤ Em (T := T) inst P A m g := by
  unfold Em
  apply Finset.sum_le_sum
  intro τ _
  exact mul_le_mul_of_nonneg_left (hfg τ) (Wm_nonneg inst P A hw_nonneg m τ)

lemma Em_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : ℕ) (hm : m ≤ T) : Em (T := T) inst P A m (fun _ => 1) = 1 := by
  have h1 := expect_eq_Em (T := T) inst P A hw_sum hn hN m hm (fun _ => 1) (fun _ _ _ => rfl)
  have h2 := expect_eq_Em (T := T) inst P A hw_sum hn hN 0 (Nat.zero_le _) (fun _ => 1) (fun _ _ _ => rfl)
  rw [← h1, h2, Em_zero_one inst P A hN]

lemma Em_combo (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ) (a : ℝ)
    (f : (Fin T → Step n L) → ℝ) (c : Fin n → Fin n → ℝ)
    (g : Fin n → Fin n → (Fin T → Step n L) → ℝ) :
    Em (T := T) inst P A m (fun τ => a * f τ - ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, c j i * g j i τ) =
      a * Em (T := T) inst P A m f - ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, c j i * Em (T := T) inst P A m (g j i) := by
  unfold Em
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro τ _; ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro τ _
    ring

lemma pubHist_succ (A : Alg n L) (τ : Fin T → Step n L) (t : ℕ) (ht : t < T) :
    pubHist A τ (t + 1) = pubHist A τ t ++
      [(ranking A τ ⟨t, ht⟩, (τ ⟨t, ht⟩).2.1.isSome, (τ ⟨t, ht⟩).2.2)] := by
  unfold pubHist
  rw [List.take_add_one]
  simp [ht]

lemma budget_path (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∀ s, s ≤ T → ((pubHist A τ s).filter (fun s => s.2.1)).length ≤ F ∧
      (((pubHist A τ s).filter (fun s => s.2.1)).length : ℝ) =
        ∑ t ∈ Finset.range s, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
  intro s
  induction s with
  | zero => intro _; simp [pubHist]
  | succ s ih =>
    intro hs
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [pubHist_succ A τ s (by omega), List.filter_append, List.length_append,
      Finset.sum_range_succ, dif_pos (show s < T by omega), ← ih2]
    have hstep := hτ ⟨s, by omega⟩
    by_cases hF : F ≤ ((pubHist A τ s).filter (fun s => s.2.1)).length
    · have hPn := hP _ hF
      have hnone : (τ ⟨s, by omega⟩).2.1 = none := by
        by_contra hc
        apply hstep
        unfold stepW
        rw [hPn, PMF.pure_apply, if_neg hc]
        simp
      simp [hnone]
      omega
    · constructor
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h] <;> omega
      · cases h : (τ ⟨s, by omega⟩).2.1.isSome <;> simp [h]


noncomputable def fac (k : Fin L) (c : ℝ) (x : Step n L) : ℝ :=
  Real.exp ((if x.2.1.isSome then 1 else 0) * ((if x.1 = k then 1 else 0) - c))

noncomputable def Mt (k : Fin L) (c : ℝ) (t : ℕ) (τ : Fin T → Step n L) : ℝ :=
  ∏ s : Fin T, if (s : ℕ) < t then fac k c (τ s) else 1

lemma Mt_update (k : Fin L) (c : ℝ) (m : Fin T) (τ : Fin T → Step n L) (x : Step n L) :
    Mt k c (m + 1) (Function.update τ m x) = Mt k c m τ * fac k c x := by
  unfold Mt
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase Finset.univ (fun s : Fin T => if (s : ℕ) < m then fac k c (τ s)
      else 1) (Finset.mem_univ m)]
  simp only [lt_irrefl, if_false, Nat.lt_succ_self, if_true, Function.update_self, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  have hsm : s ≠ m := Finset.ne_of_mem_erase hs
  have hsm' : (s : ℕ) ≠ m := fun h => hsm (Fin.ext h)
  by_cases hlt : (s : ℕ) < m
  · rw [if_pos (by omega), if_pos hlt, Function.update_of_ne hsm]
  · rw [if_neg (by omega), if_neg hlt]

lemma Mt_dep (k : Fin L) (c : ℝ) (t : ℕ) : DepBelow (T := T) (n := n) t (Mt k c t) := by
  intro τ τ' h
  unfold Mt
  apply Finset.prod_congr rfl
  intro s _
  split_ifs with hs
  · rw [h s hs]
  · rfl

lemma Mt_nonneg (k : Fin L) (c : ℝ) (t : ℕ) (τ : Fin T → Step n L) : 0 ≤ Mt k c t τ := by
  unfold Mt
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact (Real.exp_pos _).le
  · norm_num

lemma fac_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (k : Fin L) (p : ℝ) (hwk : ∀ h, A.w h k ≤ p)
    (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x, stepW inst P A (Function.update τ m x) m * fac k ((Real.exp 1 - 1) * p) x ≤ 1 := by
  simp only [stepW_update]
  set h := algHist τ m
  set q := P (pubHist A τ m)
  have e1 : ∑ x : Step n L, A.w h x.1 * (q x.2.1).toReal * obsW inst (A.rank h x.1) x.2.1 x.2.2 *
      fac k ((Real.exp 1 - 1) * p) x =
      ∑ a : Action n, (q a).toReal * ∑ l : Fin L, A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true)) := by
    rw [Fintype.sum_prod_type]
    calc _ = ∑ l : Fin L, ∑ a : Action n, (q a).toReal *
          (A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true))) := by
          apply Finset.sum_congr rfl; intro l _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro a _
          dsimp only
          have : ∀ o : Obs n, fac k ((Real.exp 1 - 1) * p) (l, a, o) =
              fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true)) := fun o => rfl
          simp only [this]
          rw [← Finset.sum_mul, ← Finset.mul_sum, obsW_sum inst _ _ hn]; ring
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  rw [e1]
  have hinner : ∀ a : Action n, ∑ l : Fin L, A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true)) ≤ 1 := by
    intro a
    cases a with
    | none => simp [fac, hw_sum]
    | some a =>
      simp only [fac, Option.isSome_some, if_true, one_mul]
      have hsplit : ∀ l : Fin L, A.w h l * Real.exp ((if l = k then 1 else 0) - (Real.exp 1 - 1) * p) =
          Real.exp (-((Real.exp 1 - 1) * p)) * (A.w h l + (if l = k then A.w h l * (Real.exp 1 - 1) else 0)) := by
        intro l
        split_ifs
        · rw [show (1 : ℝ) - (Real.exp 1 - 1) * p = 1 + -((Real.exp 1 - 1) * p) by ring, Real.exp_add]; ring
        · simp only [zero_sub, add_zero]; ring
      simp only [hsplit]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hw_sum, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hb : 1 + A.w h k * (Real.exp 1 - 1) ≤ Real.exp ((Real.exp 1 - 1) * p) := by
        have := Real.add_one_le_exp ((Real.exp 1 - 1) * p)
        have := mul_le_mul_of_nonneg_right (hwk h) he1
        nlinarith
      calc Real.exp (-((Real.exp 1 - 1) * p)) * (1 + A.w h k * (Real.exp 1 - 1))
          ≤ Real.exp (-((Real.exp 1 - 1) * p)) * Real.exp ((Real.exp 1 - 1) * p) :=
            mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
  calc ∑ a : Action n, (q a).toReal * ∑ l : Fin L, A.w h l * fac k ((Real.exp 1 - 1) * p) (l, a, (⟨0, hn⟩, true))
      ≤ ∑ a : Action n, (q a).toReal * 1 :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hinner a) ENNReal.toReal_nonneg)
    _ = 1 := by simp only [mul_one]; exact pmf_sum q

lemma E_Mt_le (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L))
    (k : Fin L) (p : ℝ) (hwk : ∀ h, A.w h k ≤ p) :
    ∀ t, t ≤ T → expect inst P A T (Mt k ((Real.exp 1 - 1) * p) t) ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    have : Mt (T := T) (n := n) k ((Real.exp 1 - 1) * p) 0 = fun _ => 1 := by
      funext τ; simp [Mt]
    rw [this, expect_eq_Em inst P A hw_sum hn hN 0 (Nat.zero_le _) _ (fun _ _ _ => rfl),
      Em_zero_one inst P A hN]
  | succ t ih =>
    intro ht
    rw [expect_eq_Em inst P A hw_sum hn hN (t + 1) ht _ (Mt_dep k _ (t + 1))]
    have := Em_step inst P A (⟨t, by omega⟩ : Fin T) (Mt k ((Real.exp 1 - 1) * p) (t + 1)) hN
    rw [this]
    calc _ ≤ Em (T := T) inst P A t (Mt k ((Real.exp 1 - 1) * p) t) := by
          apply Em_mono inst P A hw_nonneg
          intro τ
          have hu : ∀ x, Mt k ((Real.exp 1 - 1) * p) (t + 1) (Function.update τ (⟨t, by omega⟩ : Fin T) x) =
              Mt k ((Real.exp 1 - 1) * p) t τ * fac k ((Real.exp 1 - 1) * p) x :=
            fun x => Mt_update k _ (⟨t, by omega⟩ : Fin T) τ x
          simp only [hu]
          have hs := fac_sum inst P A hw_nonneg hw_sum hn k p hwk (⟨t, by omega⟩ : Fin T) τ
          have hM := Mt_nonneg k ((Real.exp 1 - 1) * p) t τ
          calc ∑ x, stepW inst P A (Function.update τ ⟨t, by omega⟩ x) ⟨t, by omega⟩ *
                (Mt k ((Real.exp 1 - 1) * p) t τ * fac k ((Real.exp 1 - 1) * p) x)
              = Mt k ((Real.exp 1 - 1) * p) t τ * ∑ x, stepW inst P A (Function.update τ ⟨t, by omega⟩ x) ⟨t, by omega⟩ *
                fac k ((Real.exp 1 - 1) * p) x := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
            _ ≤ Mt k ((Real.exp 1 - 1) * p) t τ * 1 := mul_le_mul_of_nonneg_left hs hM
            _ = _ := mul_one _
      _ = expect inst P A T (Mt k ((Real.exp 1 - 1) * p) t) :=
          (expect_eq_Em inst P A hw_sum hn hN t (by omega) _ (Mt_dep k _ t)).symm
      _ ≤ 1 := ih (by omega)

lemma exposure_real (k : Fin L) (τ : Fin T → Step n L) :
    (exposure k τ : ℝ) = ∑ s : Fin T, (if (τ s).2.1.isSome then 1 else 0) * (if (τ s).1 = k then 1 else 0) := by
  unfold exposure
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  by_cases h1 : (τ s).1 = k <;> by_cases h2 : (τ s).2.1.isSome <;> simp [h1, h2]

lemma Mt_T (k : Fin L) (c : ℝ) (τ : Fin T → Step n L) :
    Mt k c T τ = Real.exp ((exposure k τ : ℝ) - c * ∑ s : Fin T, (if (τ s).2.1.isSome then 1 else 0)) := by
  unfold Mt
  simp only [Fin.is_lt, if_true]
  rw [exposure_real, Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro s _
  unfold fac
  congr 1
  ring

lemma fake_count_le (inst : Instance n) (P : Adversary n) (A : Alg n L) (F : ℕ)
    (hP : WithinBudget F P) (τ : Fin T → Step n L) (hτ : ∀ s, stepW inst P A τ s ≠ 0) :
    ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) ≤ F := by
  obtain ⟨b1, b2⟩ := budget_path inst P A F hP τ hτ T le_rfl
  have : ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) =
      ∑ t ∈ Finset.range T, (if h : t < T then (if (τ ⟨t, h⟩).2.1.isSome then 1 else 0) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => if h : t < T then
      (if (τ ⟨t, h⟩).2.1.isSome then (1 : ℝ) else 0) else 0) T]
    apply Finset.sum_congr rfl
    intro s _
    rw [dif_pos s.isLt]
  rw [this, ← b2]
  exact_mod_cast b1

lemma exposure_le_fake (k : Fin L) (τ : Fin T → Step n L) :
    (exposure k τ : ℝ) ≤ ∑ s : Fin T, (if (τ s).2.1.isSome then (1 : ℝ) else 0) := by
  rw [exposure_real]
  apply Finset.sum_le_sum
  intro s _
  split_ifs <;> norm_num

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

lemma tail_bound (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) (F : ℕ) (hP : WithinBudget F P)
    (k : Fin L) (p : ℝ) (hp0 : 0 ≤ p) (hwk : ∀ h, A.w h k ≤ p) (hFp : (F : ℝ) * p ≤ 1) (a : ℝ) :
    prob inst P A T (fun τ => ¬ (exposure k τ : ℝ) ≤ a) ≤ Real.exp (Real.exp 1 - 1 - a) := by
  set c := (Real.exp 1 - 1) * p with hc
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc0 : 0 ≤ c := mul_nonneg he1 hp0
  have hcF : c * F ≤ Real.exp 1 - 1 := by
    rw [hc]; nlinarith
  have hM := E_Mt_le inst P A hw_nonneg hw_sum hn hN k p hwk T le_rfl
  calc prob inst P A T (fun τ => ¬ (exposure k τ : ℝ) ≤ a)
      ≤ expect inst P A T (fun τ => Real.exp (c * F - a) * Mt k c T τ) := by
        unfold prob expect
        apply Finset.sum_le_sum
        intro τ _
        by_cases h0 : trajW inst P A T τ = 0
        · rw [h0]; simp
        have hτ : ∀ s, stepW inst P A τ s ≠ 0 := by
          intro s hs; apply h0; unfold trajW
          exact Finset.prod_eq_zero (Finset.mem_univ s) hs
        have hW : 0 ≤ trajW inst P A T τ :=
          Finset.prod_nonneg (fun s _ => stepW_nonneg inst P A hw_nonneg τ s)
        apply mul_le_mul_of_nonneg_left _ hW
        have hY := fake_count_le inst P A F hP τ hτ
        beta_reduce
        by_cases hx : (exposure k τ : ℝ) ≤ a
        · simp only [hx, not_true_eq_false, if_false]
          exact mul_nonneg (Real.exp_pos _).le (Mt_nonneg k c T τ)
        · simp only [hx, not_false_eq_true, if_true]
          push_neg at hx
          rw [Mt_T, ← Real.exp_add]
          apply Real.one_le_exp
          have := mul_le_mul_of_nonneg_left hY hc0
          linarith
    _ = Real.exp (c * F - a) * expect inst P A T (Mt k c T) := by
        unfold expect; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro τ _; ring
    _ ≤ Real.exp (c * F - a) * 1 := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ ≤ Real.exp (Real.exp 1 - 1 - a) := by
        rw [mul_one]; apply Real.exp_le_exp.mpr; linarith

lemma pathwise_bound (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) (F : ℕ) (hP : WithinBudget F P)
    (k : Fin L) (a : ℝ) (hFa : (F : ℝ) ≤ a) :
    prob inst P A T (fun τ => ¬ (exposure k τ : ℝ) ≤ a) = 0 := by
  unfold prob expect
  apply Finset.sum_eq_zero
  intro τ _
  by_cases h0 : trajW inst P A T τ = 0
  · rw [h0]; simp
  have hτ : ∀ s, stepW inst P A τ s ≠ 0 := by
    intro s hs; apply h0; unfold trajW
    exact Finset.prod_eq_zero (Finset.mem_univ s) hs
  have h1 := fake_count_le inst P A F hP τ hτ
  have h2 := exposure_le_fake k τ
  beta_reduce
  rw [if_neg (by push_neg; linarith)]
  simp


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

lemma core_bound (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    prob inst P (forc n T tb fb) T
        (fun τ => ¬ (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / δ) + 3)
      ≤ δ / (2 * (numLevels T : ℝ)) := by
  set A := forc n T tb fb
  have hL : 0 < numLevels T := Fin.pos k
  have hL' : (1 : ℝ) ≤ numLevels T := by exact_mod_cast hL
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun h k => levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun h => levelW_sum _ hL
  have hN : (0 : ℝ) < Fintype.card (Step n (numLevels T)) := by
    have : Nonempty (Step n (numLevels T)) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hx : 1 < 2 * (numLevels T : ℝ) / δ := by
    rw [lt_div_iff₀ hδ0]; linarith
  have hlog : 0 ≤ Real.log (2 * (numLevels T : ℝ) / δ) := Real.log_nonneg hx.le
  have hpos : 0 ≤ δ / (2 * (numLevels T : ℝ)) := by positivity
  by_cases hk0 : (k : ℕ) = 0
  · rw [pathwise_bound inst P A hw_nonneg hw_sum hn hN F hP k _ ?_]
    · exact hpos
    · rw [hk0] at hk
      have : (F : ℝ) ≤ 2 := by exact_mod_cast hk
      linarith
  · have hwk : ∀ h, A.w h k ≤ (1 / 2 : ℝ) ^ ((k : ℕ) + 1) := by
      intro h
      show levelW _ k ≤ _
      unfold levelW; rw [if_neg hk0]
    have hFp : (F : ℝ) * (1 / 2 : ℝ) ^ ((k : ℕ) + 1) ≤ 1 := by
      have : (F : ℝ) ≤ 2 ^ ((k : ℕ) + 1) := by exact_mod_cast hk
      rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
      exact this
    refine le_trans (tail_bound inst P A hw_nonneg hw_sum hn hN F hP k _ (by positivity) hwk hFp _) ?_
    have he : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
    calc Real.exp (Real.exp 1 - 1 - (Real.log (2 * (numLevels T : ℝ) / δ) + 3))
        ≤ Real.exp (-Real.log (2 * (numLevels T : ℝ) / δ)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = δ / (2 * (numLevels T : ℝ)) := by
          rw [Real.exp_neg, Real.exp_log (by linarith)]
          field_simp

end L1Aux

open L1Aux in
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    1 - δ / (2 * (numLevels T : ℝ)) ≤
      prob inst P (forc n T tb fb) T
        (fun τ => (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / δ) + 3) := by
  have hL : 0 < numLevels T := Fin.pos k
  have hN : (0 : ℝ) < Fintype.card (Step n (numLevels T)) := by
    have : Nonempty (Step n (numLevels T)) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  rw [prob_compl inst P (forc n T tb fb) (fun h => levelW_sum _ hL) hn hN]
  have := core_bound n T F hn hT inst P hP tb fb δ hδ0 hδ1 k hk
  linarith
