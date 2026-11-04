-- Prove2me | solution 1 for BlindProphetSec.Blind.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:21:49.188569+00:00
-- url     : https://prove2.me/submissions/91981ccc-7a69-422e-8259-ca68350a6843

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

open MeasureTheory

namespace BPSLem41

open BlindProphetSec.Blind

/-- Independence: the probability that `V_{σ j} ≤ τ j` for all `j ∈ J` is `∏_{j ∈ J} F_{σ j}(τ j)`. -/
lemma box_prob {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    ((Measure.pi μ) {v | ∀ j ∈ J, v (σ j) ≤ τ j}).toReal =
      ∏ j ∈ J, (μ (σ j) (Set.Iic (τ j))).toReal := by
  classical
  have hset : {v : Fin n → ℝ | ∀ j ∈ J, v (σ j) ≤ τ j} =
      Set.univ.pi (fun p => if σ.symm p ∈ J then Set.Iic (τ (σ.symm p)) else Set.univ) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h p
      split_ifs with hp
      · have := h _ hp
        simpa using this
      · trivial
    · intro h j hj
      have := h (σ j)
      simp only [Equiv.symm_apply_apply, hj, if_true, Set.mem_Iic] at this
      exact this
  rw [hset, Measure.pi_pi, ENNReal.toReal_prod]
  conv_lhs => rw [← Equiv.prod_comp σ]
  have e : ∀ j, ((μ (σ j)) (if σ.symm (σ j) ∈ J then Set.Iic (τ (σ.symm (σ j))) else Set.univ)).toReal
      = if j ∈ J then (μ (σ j) (Set.Iic (τ j))).toReal else 1 := by
    intro j
    simp only [Equiv.symm_apply_apply]
    split_ifs <;> simp
  simp_rw [e]
  rw [Finset.prod_ite_mem]
  simp

lemma F_mono {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (p : Fin n)
    {x y : ℝ} (h : x ≤ y) : (μ p (Set.Iic x)).toReal ≤ (μ p (Set.Iic y)).toReal :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr h))

lemma F_le_one {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (p : Fin n)
    (x : ℝ) : (μ p (Set.Iic x)).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

end BPSLem41

open BlindProphetSec.Blind BPSLem41 in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Fin n → ℝ) (hτ : Antitone τ) (i k : Fin n) :
    probVS μ (fun v σ => ¬ stopLE (ttaAcc τ v σ) (k.val + 1)) ≤
      ((n : ℝ) * probVS μ (fun v σ => stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i)) *
        (1 - ((k.val : ℝ) + 1) / n +
          (1 / (n : ℝ)) * ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val ≤ k.val),
            (μ i (Set.Iic (τ l))).toReal) := by
  classical
  -- notation
  set K := k.val with hK
  let F : Fin n → ℝ → ℝ := fun p x => (μ p (Set.Iic x)).toReal
  have hF0 : ∀ p x, 0 ≤ F p x := fun p x => ENNReal.toReal_nonneg
  set P : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val < K) with hP
  set Q : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val ≤ K) with hQ
  let A : Equiv.Perm (Fin n) → ℝ := fun σ => ∏ j ∈ Q, F (σ j) (τ j)
  let B : Equiv.Perm (Fin n) → ℝ := fun σ => ∏ j ∈ P, F (σ j) (τ j)
  let w : Fin n → ℝ := fun l => if l.val ≤ K then F i (τ l) else 1
  have hB0 : ∀ σ, 0 ≤ B σ := fun σ => Finset.prod_nonneg fun j _ => hF0 _ _
  have hkP : k ∉ P := by
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hQP : Q = insert k P := by
    ext j
    simp only [hQ, hP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.lt_or_eq_of_le h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (h | h)
      · rw [h]
      · omega
  have hAB : ∀ σ, A σ = F (σ k) (τ k) * B σ := by
    intro σ
    show ∏ j ∈ Q, F (σ j) (τ j) = F (σ k) (τ k) * ∏ j ∈ P, F (σ j) (τ j)
    rw [hQP, Finset.prod_insert hkP]
  -- events as boxes
  have hLHS : ∀ σ : Equiv.Perm (Fin n),
      ((Measure.pi μ) {v | ¬ stopLE (ttaAcc τ v σ) (K + 1)}).toReal = A σ := by
    intro σ
    have : {v : Fin n → ℝ | ¬ stopLE (ttaAcc τ v σ) (K + 1)} = {v | ∀ j ∈ Q, v (σ j) ≤ τ j} := by
      ext v
      simp only [stopLE, ttaAcc, Set.mem_ofPred_eq, not_exists, not_and, not_lt, hQ,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h j hj; exact h j (by omega)
      · intro h j hj; exact h j (by omega)
    rw [this, box_prob]
  have hRHS : ∀ σ : Equiv.Perm (Fin n),
      ((Measure.pi μ) {v | stopGE (ttaAcc τ v σ) (K + 1) ∧ σ k = i}).toReal =
        if σ k = i then B σ else 0 := by
    intro σ
    split_ifs with hσ
    · have : {v : Fin n → ℝ | stopGE (ttaAcc τ v σ) (K + 1) ∧ σ k = i} =
          {v | ∀ j ∈ P, v (σ j) ≤ τ j} := by
        ext v
        simp only [stopGE, ttaAcc, Set.mem_ofPred_eq, not_lt, hσ, and_true, hP,
          Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h j hj; exact h j (by omega)
        · intro h j hj; exact h j (by omega)
      rw [this, box_prob]
    · have : {v : Fin n → ℝ | stopGE (ttaAcc τ v σ) (K + 1) ∧ σ k = i} = ∅ := by
        ext v; simp [hσ]
      rw [this]; simp
  -- pointwise swap bound
  have hpt : ∀ (σ : Equiv.Perm (Fin n)) (l : Fin n), σ l = i →
      A σ ≤ w l * B (σ * Equiv.swap l k) := by
    intro σ l hl
    rw [hAB]
    by_cases hlK : l.val ≤ K
    · have hw : w l = F i (τ l) := by simp [w, hlK]
      rw [hw]
      rcases Nat.lt_or_eq_of_le hlK with hlt | heq
      · -- l < k
        have hlP : l ∈ P := by simp [hP, hlt]
        have hlk : l ≠ k := fun h => by rw [h] at hlt; omega
        have hB' : B (σ * Equiv.swap l k) =
            F (σ k) (τ l) * ∏ j ∈ P.erase l, F (σ j) (τ j) := by
          show ∏ j ∈ P, F ((σ * Equiv.swap l k) j) (τ j) = _
          rw [← Finset.mul_prod_erase P _ hlP]
          congr 1
          · simp [Equiv.swap_apply_left]
          · apply Finset.prod_congr rfl
            intro j hj
            have hjl : j ≠ l := Finset.ne_of_mem_erase hj
            have hjk : j ≠ k := fun h => hkP (h ▸ Finset.mem_of_mem_erase hj)
            simp [Equiv.swap_apply_of_ne_of_ne hjl hjk]
        have hBσ : B σ = F (σ l) (τ l) * ∏ j ∈ P.erase l, F (σ j) (τ j) := by
          show ∏ j ∈ P, F (σ j) (τ j) = _
          rw [← Finset.mul_prod_erase P _ hlP]
        rw [hB', hBσ, hl]
        have hR : 0 ≤ ∏ j ∈ P.erase l, F (σ j) (τ j) := Finset.prod_nonneg fun j _ => hF0 _ _
        have hτkl : τ k ≤ τ l := hτ (Fin.le_def.mpr hlK)
        have hmono : F (σ k) (τ k) ≤ F (σ k) (τ l) := F_mono μ (σ k) hτkl
        have h1 := hF0 (σ k) (τ k)
        have h2 := hF0 i (τ l)
        calc F (σ k) (τ k) * (F i (τ l) * ∏ j ∈ P.erase l, F (σ j) (τ j))
            = F i (τ l) * (F (σ k) (τ k) * ∏ j ∈ P.erase l, F (σ j) (τ j)) := by ring
          _ ≤ F i (τ l) * (F (σ k) (τ l) * ∏ j ∈ P.erase l, F (σ j) (τ j)) := by
            apply mul_le_mul_of_nonneg_left _ h2
            exact mul_le_mul_of_nonneg_right hmono hR
      · -- l = k
        have hlk : l = k := Fin.ext heq
        subst hlk
        rw [Equiv.swap_self, Equiv.Perm.mul_def, Equiv.refl_trans, hl]
    · have hw : w l = 1 := by simp [w, hlK]
      rw [hw, one_mul]
      have hBeq : B (σ * Equiv.swap l k) = B σ := by
        show ∏ j ∈ P, F ((σ * Equiv.swap l k) j) (τ j) = ∏ j ∈ P, F (σ j) (τ j)
        apply Finset.prod_congr rfl
        intro j hj
        have hj' : j.val < K := by simpa [hP] using hj
        have hjl : j ≠ l := fun h => by rw [h] at hj'; omega
        have hjk : j ≠ k := fun h => by rw [h] at hj'; omega
        simp [Equiv.swap_apply_of_ne_of_ne hjl hjk]
      rw [hBeq]
      calc F (σ k) (τ k) * B σ ≤ 1 * B σ :=
            mul_le_mul_of_nonneg_right (F_le_one μ _ _) (hB0 σ)
        _ = B σ := one_mul _
  -- summing
  set S : ℝ := ∑ σ : Equiv.Perm (Fin n), if σ k = i then B σ else 0 with hS
  have hsplit : ∑ σ : Equiv.Perm (Fin n), A σ =
      ∑ l : Fin n, ∑ σ : Equiv.Perm (Fin n), if σ l = i then A σ else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    have : ∀ l, (if σ l = i then A σ else 0) = if σ.symm i = l then A σ else 0 := by
      intro l
      congr 1
      apply propext
      rw [Equiv.symm_apply_eq]
      exact eq_comm
    simp_rw [this]
    simp
  have hl_bound : ∀ l : Fin n,
      (∑ σ : Equiv.Perm (Fin n), if σ l = i then A σ else 0) ≤ w l * S := by
    intro l
    calc (∑ σ : Equiv.Perm (Fin n), if σ l = i then A σ else 0)
        ≤ ∑ σ : Equiv.Perm (Fin n),
            (if (σ * Equiv.swap l k) k = i then w l * B (σ * Equiv.swap l k) else 0) := by
          apply Finset.sum_le_sum
          intro σ _
          have hsw : (σ * Equiv.swap l k) k = σ l := by simp [Equiv.swap_apply_right]
          rw [hsw]
          split_ifs with h
          · exact hpt σ l h
          · exact le_rfl
      _ = ∑ σ : Equiv.Perm (Fin n), (if σ k = i then w l * B σ else 0) :=
          Equiv.sum_comp (Equiv.mulRight (Equiv.swap l k))
            (fun σ => if σ k = i then w l * B σ else 0)
      _ = w l * S := by
          rw [hS, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          split_ifs <;> simp
  have hmain : ∑ σ : Equiv.Perm (Fin n), A σ ≤ S * ∑ l : Fin n, w l := by
    rw [hsplit, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    rw [mul_comm]
    exact hl_bound l
  -- the weights
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact k.elim0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcardQ : Q.card = K + 1 := by
    have : Q = Finset.univ.filter (fun j : Fin n => j.val < K + 1) := by
      ext j; simp [hQ]
    rw [this, Fin.card_filter_val_lt]
    have := k.isLt
    omega
  have hw_sum : ∑ l : Fin n, w l =
      (n : ℝ) - (K + 1) + ∑ l ∈ Q, F i (τ l) := by
    show ∑ l : Fin n, (if l.val ≤ K then F i (τ l) else 1) = _
    rw [Finset.sum_ite]
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun l : Fin n => l.val ≤ K)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc' : ((Finset.univ.filter (fun l : Fin n => ¬ l.val ≤ K)).card : ℝ) = n - (K + 1) := by
      have : (Finset.univ.filter (fun l : Fin n => ¬ l.val ≤ K)).card = n - (K + 1) := by
        rw [← hQ, hcardQ] at hc; omega
      rw [this, Nat.cast_sub (by have := k.isLt; omega)]
      push_cast; ring
    rw [hc']
    ring
  -- assemble
  unfold probVS
  rw [Finset.sum_congr rfl (fun σ _ => hLHS σ), Finset.sum_congr rfl (fun σ _ => hRHS σ)]
  rw [← hS]
  have hfac : (0 : ℝ) ≤ 1 / (n.factorial : ℝ) := by positivity
  have key : (n : ℝ) * (1 - ((K : ℝ) + 1) / n + 1 / (n : ℝ) * ∑ l ∈ Q, F i (τ l)) =
      ∑ l : Fin n, w l := by
    rw [hw_sum]
    field_simp
  calc 1 / (n.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin n), A σ
      ≤ 1 / (n.factorial : ℝ) * (S * ∑ l : Fin n, w l) :=
        mul_le_mul_of_nonneg_left hmain hfac
    _ = (n * (1 / (n.factorial : ℝ) * S)) *
          (1 - ((K : ℝ) + 1) / n + 1 / (n : ℝ) * ∑ l ∈ Q, F i (τ l)) := by
        rw [← key]; ring
