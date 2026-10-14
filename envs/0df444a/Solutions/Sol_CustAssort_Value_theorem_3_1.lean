-- Prove2me | solution 1 for CustAssort.Value.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:00:54.051102+00:00
-- url     : https://prove2.me/submissions/5caaa4aa-1c86-461b-8e5a-d30547b0ba44

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

namespace RRAux_CustAssort_Value_theorem_3_1

open CustAssort.AugGreedy (rev fj fC)
open CustAssort.Value (vI revI thetaI alpha feasible aStar bStar)

lemma rev_nonneg {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hv : ∀ i j, 0 ≤ v i j) (j : Fin m) (S : Finset (Fin n)) : 0 ≤ rev v r j S := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).le (hv i j))
  · have := Finset.sum_nonneg (fun i (_ : i ∈ S) => hv i j)
    linarith

lemma part1 (n m K : ℕ) (r : Fin n → ℝ) (v : Fin n → Fin m → ℝ) (θ : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i j, 0 ≤ v i j) (hθ : ∀ j, 0 ≤ θ j) :
    CustAssort.Value.zMMNL θ v r K ≤ CustAssort.Value.zCAP θ v r K ∧
    CustAssort.Value.zCAP θ v r K ≤ (m : ℝ) * CustAssort.Value.zMMNL θ v r K := by
  constructor
  · unfold CustAssort.Value.zMMNL CustAssort.Value.zCAP
    apply Finset.sup'_le
    intro S hS
    refine le_trans ?_ (Finset.le_sup' _ hS)
    unfold fC
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hθ j)
    unfold fj
    exact Finset.le_sup' (rev v r j) (Finset.mem_powerset_self S)
  · have key : ∀ S ∈ feasible n K, ∀ j : Fin m,
        θ j * fj v r j S ≤ CustAssort.Value.zMMNL θ v r K := by
      intro S hS j
      obtain ⟨T, hT, hTeq⟩ :=
        Finset.exists_mem_eq_sup' (Finset.powerset_nonempty S) (rev v r j)
      unfold fj
      rw [hTeq]
      have hTf : T ∈ feasible n K := by
        simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        exact le_trans (Finset.card_le_card (Finset.mem_powerset.mp hT)) hS
      unfold CustAssort.Value.zMMNL
      refine le_trans ?_ (Finset.le_sup' (fun S => ∑ j : Fin m, θ j * rev v r j S) hTf)
      exact Finset.single_le_sum (f := fun j' => θ j' * rev v r j' T)
        (fun j' _ => mul_nonneg (hθ j') (rev_nonneg v r hr hv j' T)) (Finset.mem_univ j)
    unfold CustAssort.Value.zCAP
    apply Finset.sup'_le
    intro S hS
    unfold fC
    calc ∑ j ∈ Finset.univ, θ j * fj v r j S
        ≤ ∑ _j : Fin m, CustAssort.Value.zMMNL θ v r K :=
          Finset.sum_le_sum (fun j _ => key S hS j)
      _ = _ := by simp

lemma half_le (α A x : ℝ) (hα : 0 ≤ α) (hA : 0 < A) (hx : 1 ≤ x) :
    α / 2 ≤ α / A * (A * x / (x + 1)) := by
  have h1 : α / A * (A * x / (x + 1)) = α * x / (x + 1) := by
    field_simp
  rw [h1, div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

lemma sum_inv_pos (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 1 ≤ m) :
    0 < ∑ j : Fin m, 1 / a ^ (j.val + 1) := by
  apply Finset.sum_pos (fun j _ => by positivity)
  exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

lemma alpha_pos (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 1 ≤ m) : 0 < alpha a m := by
  unfold alpha
  exact inv_pos.mpr (sum_inv_pos a ha m hm)

lemma vI_nonneg (b : ℝ) (hb : 0 ≤ b) (m : ℕ) (i j : Fin m) : 0 ≤ vI b m i j := by
  unfold vI; split_ifs <;> positivity

lemma vI_diag (b : ℝ) (m : ℕ) (j : Fin m) : vI b m j j = b ^ (m - j.val) := by
  simp [vI]

lemma term_le (a b α : ℝ) (m : ℕ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α) (i j : Fin m) :
    α / a ^ (j.val + 1) * (a ^ (i.val + 1) * vI b m i j) ≤
      α / a * vI b m i j + (if i = j then α * vI b m j j else 0) := by
  have ha0 : 0 < a := by linarith
  rcases lt_trichotomy i j with h | h | h
  · simp only [if_neg (ne_of_lt h), add_zero]
    have hv := vI_nonneg b hb m i j
    have hpow : a ^ (i.val + 1) * a ≤ a ^ (j.val + 1) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ ha (by have := Fin.lt_def.mp h; omega)
    have key : α / a ^ (j.val + 1) * a ^ (i.val + 1) ≤ α / a := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) ha0]
      calc α * a ^ (i.val + 1) * a = α * (a ^ (i.val + 1) * a) := by ring
        _ ≤ α * a ^ (j.val + 1) := mul_le_mul_of_nonneg_left hpow hα
    calc α / a ^ (j.val + 1) * (a ^ (i.val + 1) * vI b m i j)
        = (α / a ^ (j.val + 1) * a ^ (i.val + 1)) * vI b m i j := by ring
      _ ≤ α / a * vI b m i j := mul_le_mul_of_nonneg_right key hv
  · subst h
    simp only [if_true]
    have hv := vI_nonneg b hb m i i
    have h1 : α / a ^ (i.val + 1) * (a ^ (i.val + 1) * vI b m i i) = α * vI b m i i := by
      field_simp
    rw [h1]
    have : 0 ≤ α / a * vI b m i i := by positivity
    linarith
  · have hv : vI b m i j = 0 := by
      unfold vI; rw [if_neg]; exact not_le.mpr h
    simp [hv, ne_of_gt h]

lemma rev_le (a b : ℝ) (m : ℕ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ alpha a m)
    (S : Finset (Fin m)) (j : Fin m) :
    thetaI a m j * rev (vI b m) (revI a m) j S ≤
      alpha a m / a + alpha a m *
        (if j ∈ S then b ^ (m - j.val) / (∑ i ∈ S, vI b m i j + 1) else 0) := by
  have hsnn : 0 ≤ ∑ i ∈ S, vI b m i j := Finset.sum_nonneg (fun i _ => vI_nonneg b hb m i j)
  have hD : 0 < ∑ i ∈ S, vI b m i j + 1 := by linarith
  have hnum : thetaI a m j * ∑ i ∈ S, revI a m i * vI b m i j ≤
      alpha a m / a * ∑ i ∈ S, vI b m i j +
        (if j ∈ S then alpha a m * b ^ (m - j.val) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ i ∈ S, thetaI a m j * (revI a m i * vI b m i j)
        ≤ ∑ i ∈ S, (alpha a m / a * vI b m i j +
            (if i = j then alpha a m * vI b m j j else 0)) :=
          Finset.sum_le_sum (fun i _ => term_le a b (alpha a m) m ha hb hα i j)
      _ = ∑ i ∈ S, alpha a m / a * vI b m i j +
            (if j ∈ S then alpha a m * b ^ (m - j.val) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', vI_diag]
  have ha0 : 0 ≤ alpha a m / a := div_nonneg hα (by linarith)
  unfold rev ChoiceCDLP.MNL.mnlObjective
  rw [← mul_div_assoc, div_le_iff₀ hD]
  by_cases hj : j ∈ S
  · simp only [hj, if_true] at hnum ⊢
    have e : (alpha a m / a + alpha a m * (b ^ (m - j.val) / (∑ i ∈ S, vI b m i j + 1))) *
        (∑ i ∈ S, vI b m i j + 1) =
        alpha a m / a * ∑ i ∈ S, vI b m i j + alpha a m / a +
          alpha a m * b ^ (m - j.val) := by
      field_simp
    rw [e]
    linarith
  · simp only [hj, if_false] at hnum ⊢
    nlinarith

lemma diag_le (m : ℕ) (b : ℝ) (hb1 : 1 ≤ b) (hbm : (m : ℝ) - 1 ≤ b) (S : Finset (Fin m)) :
    ∑ j ∈ S, b ^ (m - j.val) / (∑ i ∈ S, vI b m i j + 1) ≤ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨i0, hi0, hmin⟩ : ∃ i0 ∈ S, ∀ j ∈ S, i0 ≤ j :=
    ⟨S.min' hS, S.min'_mem hS, fun j hj => S.min'_le j hj⟩
  have hb0 : 0 ≤ b := by linarith
  have hD : ∀ j, 0 < ∑ i ∈ S, vI b m i j + 1 := by
    intro j
    have := Finset.sum_nonneg (fun i (_ : i ∈ S) => vI_nonneg b hb0 m i j)
    linarith
  rw [← Finset.add_sum_erase S _ hi0]
  have t1 : b ^ (m - i0.val) / (∑ i ∈ S, vI b m i i0 + 1) ≤ 1 := by
    rw [div_le_one (hD i0)]
    have := Finset.single_le_sum (f := fun i => vI b m i i0)
      (fun i _ => vI_nonneg b hb0 m i i0) hi0
    rw [vI_diag] at this
    linarith
  have t_le : ∀ j ∈ S.erase i0, b ^ (m - j.val) / (∑ i ∈ S, vI b m i j + 1) ≤ 1 / b := by
    intro j hj
    have hjS := Finset.mem_of_mem_erase hj
    have hne := Finset.ne_of_mem_erase hj
    have hlt : i0 < j := lt_of_le_of_ne (hmin j hjS) (Ne.symm hne)
    rw [div_le_div_iff₀ (hD j) (by linarith)]
    have h1 : b ^ (m - j.val) * b ≤ b ^ (m - i0.val) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hb1 (by have := Fin.lt_def.mp hlt; have := j.isLt; omega)
    have h2 : b ^ (m - i0.val) ≤ ∑ i ∈ S, vI b m i j := by
      have := Finset.single_le_sum (f := fun i => vI b m i j)
        (fun i _ => vI_nonneg b hb0 m i j) hi0
      have hv : vI b m i0 j = b ^ (m - i0.val) := by simp [vI, hlt.le]
      rw [hv] at this
      exact this
    linarith
  have hsum := Finset.sum_le_card_nsmul (S.erase i0) _ (1 / b) t_le
  rw [nsmul_eq_mul] at hsum
  have hc : ((S.erase i0).card : ℝ) ≤ b := by
    rw [Finset.card_erase_of_mem hi0]
    have hcm : S.card ≤ m := by simpa using Finset.card_le_univ S
    have h1 : 1 ≤ S.card := Finset.card_pos.mpr hS
    rw [Nat.cast_sub h1]
    have : (S.card : ℝ) ≤ m := by exact_mod_cast hcm
    push_cast
    linarith
  have h3 : ((S.erase i0).card : ℝ) * (1 / b) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]
    exact hc
  linarith

lemma bStar_ge (m : ℕ) (hm : 2 ≤ m) : 1 ≤ bStar m := by
  unfold bStar
  have : (2 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

lemma aStar_ge (m : ℕ) (hm : 2 ≤ m) : (m : ℝ) ≤ aStar m ∧ 1 ≤ aStar m := by
  unfold aStar
  have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 1 ≤ ((m : ℝ) - 1) ^ m := one_le_pow₀ (by linarith)
  constructor <;> nlinarith

lemma mmnl_le (m : ℕ) (hm : 2 ≤ m) :
    CustAssort.Value.zMMNL (thetaI (aStar m) m) (vI (bStar m) m) (revI (aStar m) m) m ≤
      3 * alpha (aStar m) m := by
  obtain ⟨hma, ha1⟩ := aStar_ge m hm
  have hb1 := bStar_ge m hm
  have hα := alpha_pos (aStar m) (by linarith) m (by omega)
  unfold CustAssort.Value.zMMNL
  apply Finset.sup'_le
  intro S _
  calc ∑ j : Fin m, thetaI (aStar m) m j * rev (vI (bStar m) m) (revI (aStar m) m) j S
      ≤ ∑ j : Fin m, (alpha (aStar m) m / aStar m + alpha (aStar m) m *
          (if j ∈ S then bStar m ^ (m - j.val) / (∑ i ∈ S, vI (bStar m) m i j + 1)
            else 0)) :=
        Finset.sum_le_sum (fun j _ => rev_le _ _ m ha1 (by linarith) hα.le S j)
    _ = (m : ℝ) * (alpha (aStar m) m / aStar m) + alpha (aStar m) m *
          ∑ j ∈ S, bStar m ^ (m - j.val) / (∑ i ∈ S, vI (bStar m) m i j + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
        simp
    _ ≤ 3 * alpha (aStar m) m := by
        have h1 : (m : ℝ) * (alpha (aStar m) m / aStar m) ≤ alpha (aStar m) m := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          calc (m : ℝ) * alpha (aStar m) m = alpha (aStar m) m * m := by ring
            _ ≤ alpha (aStar m) m * aStar m := mul_le_mul_of_nonneg_left hma hα.le
        have h2 := mul_le_mul_of_nonneg_left
          (diag_le m (bStar m) hb1 (by unfold bStar; exact le_refl _) S) hα.le
        linarith

lemma cap_ge (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) * (alpha (aStar m) m / 2) ≤
      CustAssort.Value.zCAP (thetaI (aStar m) m) (vI (bStar m) m) (revI (aStar m) m) m := by
  obtain ⟨hma, ha1⟩ := aStar_ge m hm
  have hb1 := bStar_ge m hm
  have hα := alpha_pos (aStar m) (by linarith) m (by omega)
  unfold CustAssort.Value.zCAP
  have huniv : (Finset.univ : Finset (Fin m)) ∈ feasible m m := by
    simp [feasible]
  refine le_trans ?_ (Finset.le_sup' _ huniv)
  unfold fC
  calc (m : ℝ) * (alpha (aStar m) m / 2) = ∑ _j : Fin m, alpha (aStar m) m / 2 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      have h1 : rev (vI (bStar m) m) (revI (aStar m) m) j {j} ≤
          fj (vI (bStar m) m) (revI (aStar m) m) j Finset.univ :=
        Finset.le_sup' _ (by simp)
      have hθ : 0 ≤ thetaI (aStar m) m j := by
        unfold thetaI; have : 0 < aStar m := by linarith
        positivity
      have h2 : alpha (aStar m) m / 2 ≤
          thetaI (aStar m) m j * rev (vI (bStar m) m) (revI (aStar m) m) j {j} := by
        unfold rev ChoiceCDLP.MNL.mnlObjective thetaI
        simp only [Finset.sum_singleton]
        rw [vI_diag]
        unfold revI
        have : 0 < aStar m := by linarith
        exact half_le _ _ _ hα.le (by positivity) (one_le_pow₀ (by linarith))
      exact le_trans h2 (mul_le_mul_of_nonneg_left h1 hθ)

lemma mmnl_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < CustAssort.Value.zMMNL (thetaI (aStar m) m) (vI (bStar m) m) (revI (aStar m) m) m := by
  obtain ⟨hma, ha1⟩ := aStar_ge m hm
  have hb1 := bStar_ge m hm
  have hα := alpha_pos (aStar m) (by linarith) m (by omega)
  have ha0 : 0 < aStar m := by linarith
  have hb0 : 0 < bStar m := by linarith
  let i0 : Fin m := ⟨0, by omega⟩
  have h0 : ({i0} : Finset (Fin m)) ∈ feasible m m := by
    simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_singleton]
    omega
  unfold CustAssort.Value.zMMNL
  refine lt_of_lt_of_le ?_ (Finset.le_sup' _ h0)
  apply Finset.sum_pos _ ⟨i0, Finset.mem_univ _⟩
  intro j _
  apply mul_pos
  · unfold thetaI; positivity
  · unfold rev ChoiceCDLP.MNL.mnlObjective
    simp only [Finset.sum_singleton]
    have hv : vI (bStar m) m i0 j = bStar m ^ m := by
      simp [vI, i0, Fin.le_def]
    rw [hv]
    unfold revI
    positivity

lemma theta_sum (m : ℕ) (hm : 2 ≤ m) : (∑ j : Fin m, thetaI (aStar m) m j) = 1 := by
  obtain ⟨hma, ha1⟩ := aStar_ge m hm
  unfold thetaI
  simp_rw [div_eq_mul_one_div (alpha (aStar m) m)]
  rw [← Finset.mul_sum]
  unfold alpha
  exact inv_mul_cancel₀ (ne_of_gt (sum_inv_pos _ (by linarith) m (by omega)))

end RRAux_CustAssort_Value_theorem_3_1

open RRAux_CustAssort_Value_theorem_3_1 in
open CustAssort.Value in
-- Theorem 3.1, page 7, including the explicit tightness family of pages 8–9.
theorem solution :
    (∀ (n m K : ℕ) (r : Fin n → ℝ) (v : Fin n → Fin m → ℝ)
      (θ : Fin m → ℝ),
      (∀ i, 0 < r i) → (∀ i j, 0 ≤ v i j) → (∀ j, 0 ≤ θ j) →
      (∑ j : Fin m, θ j) = 1 →
      zMMNL θ v r K ≤ zCAP θ v r K ∧
      zCAP θ v r K ≤ (m : ℝ) * zMMNL θ v r K) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∀ i : Fin m, 0 < revI (aStar m) m i) ∧
      (∀ i j : Fin m, 0 ≤ vI (bStar m) m i j) ∧
      (∀ j : Fin m, 0 ≤ thetaI (aStar m) m j) ∧
      (∑ j : Fin m, thetaI (aStar m) m j) = 1 ∧
      0 < zMMNL (thetaI (aStar m) m) (vI (bStar m) m)
        (revI (aStar m) m) m ∧
      (m : ℝ) / 6 * zMMNL (thetaI (aStar m) m) (vI (bStar m) m)
        (revI (aStar m) m) m ≤
      zCAP (thetaI (aStar m) m) (vI (bStar m) m)
        (revI (aStar m) m) m) := by
  refine ⟨fun n m K r v θ hr hv hθ _ => part1 n m K r v θ hr hv hθ, ?_⟩
  intro m hm
  obtain ⟨hma, ha1⟩ := aStar_ge m hm
  have hb1 := bStar_ge m hm
  have hα := alpha_pos (aStar m) (by linarith) m (by omega)
  have ha0 : 0 < aStar m := by linarith
  refine ⟨fun i => by unfold revI; positivity,
    fun i j => vI_nonneg _ (by linarith) m i j,
    fun j => by unfold thetaI; positivity,
    theta_sum m hm, mmnl_pos m hm, ?_⟩
  have h1 := mmnl_le m hm
  have h2 := cap_ge m hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have h3 : (m : ℝ) / 6 * zMMNL (thetaI (aStar m) m) (vI (bStar m) m) (revI (aStar m) m) m ≤
      (m : ℝ) / 6 * (3 * alpha (aStar m) m) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (m : ℝ) / 6 * (3 * alpha (aStar m) m) = (m : ℝ) * (alpha (aStar m) m / 2) := by ring
  linarith

#print axioms solution
