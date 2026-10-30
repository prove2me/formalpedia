-- Prove2me | solution 1 for FreemiumActions.Threshold.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:13:09.347895+00:00
-- url     : https://prove2.me/submissions/f2ab28a8-dc1b-4a74-8995-a0e15f87a2dc

import Mathlib

namespace FreemiumActions.Threshold
lemma prodIco {m : ℕ} (f : Fin (m+1) → ℝ) (i i' j : Fin (m+1)) (hij : i < j) (hi' : i'.val = i.val + 1) :
    ∏ v ∈ Finset.Ico i j, f v = f i * ∏ v ∈ Finset.Ico i' j, f v := by
  set g : ℕ → ℝ := fun n => if h : n < m + 1 then f ⟨n, h⟩ else 1 with hg
  have hconv : ∀ a b : Fin (m+1), ∏ v ∈ Finset.Ico a b, f v = ∏ n ∈ Finset.Ico a.val b.val, g n := by
    intro a b
    have := Finset.prod_map (Finset.Ico a b) Fin.valEmbedding g
    rw [Fin.map_valEmbedding_Ico] at this
    rw [this]
    apply Finset.prod_congr rfl
    intro v _
    simp [hg]
    intro h; exact absurd v.isLt (by omega)
  rw [hconv, hconv, hi', Finset.prod_eq_prod_Ico_succ_bot (Fin.lt_def.1 hij)]
  simp only [hg]
  rw [dif_pos i.isLt]

lemma prodIcc {m : ℕ} (f : Fin (m+1) → ℝ) (i i' j : Fin (m+1)) (hij : i < j) (hi' : i'.val = i.val + 1) :
    ∏ v ∈ Finset.Icc i j, f v = f i * ∏ v ∈ Finset.Icc i' j, f v := by
  set g : ℕ → ℝ := fun n => if h : n < m + 1 then f ⟨n, h⟩ else 1 with hg
  have hconv : ∀ a b : Fin (m+1), ∏ v ∈ Finset.Icc a b, f v = ∏ n ∈ Finset.Icc a.val b.val, g n := by
    intro a b
    have := Finset.prod_map (Finset.Icc a b) Fin.valEmbedding g
    rw [Fin.map_valEmbedding_Icc] at this
    rw [this]
    apply Finset.prod_congr rfl
    intro v _
    simp [hg]
    intro h; exact absurd v.isLt (by omega)
  have e : ∀ a b : ℕ, Finset.Icc a b = Finset.Ico a (b+1) := fun a b => by ext x; simp
  have h1 : i.val < j.val + 1 := by have := Fin.lt_def.1 hij; omega
  rw [hconv, hconv, hi', e, e,
    Finset.prod_eq_prod_Ico_succ_bot h1]
  simp only [hg]
  rw [dif_pos i.isLt]



end FreemiumActions.Threshold

theorem solution (m : ℕ) (S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hb : ∀ i j, i ≠ j → j.val ≠ i.val + 1 → S i j = 0)
    (hd : ∀ i, 1 - S i i ≠ 0) :
    (∀ i j, j < i → (1 - S)⁻¹ i j = 0) ∧
    (∀ i, (1 - S)⁻¹ i i = 1 / (1 - S i i)) ∧
    (∀ i j, i < j → (1 - S)⁻¹ i j =
      (∏ v ∈ Finset.Ico i j, S v (Fin.ofNat (m + 1) (v.val + 1))) /
        (∏ v ∈ Finset.Icc i j, (1 - S v v))) := by
  classical
  have hdet : (1 - S).det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular]
    · exact Finset.prod_ne_zero_iff.2 (fun i _ => by simpa using hd i)
    · intro i j hij
      have h1 : i ≠ j := ne_of_gt hij
      have h2 : j.val ≠ i.val + 1 := by
        have : j.val < i.val := hij
        omega
      simp [Matrix.one_apply, h1, hb i j h1 h2]
  set X := (1 - S)⁻¹ with hX
  have hmul : (1 - S) * X = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
  -- row relation
  have row : ∀ (i l : Fin (m+1)), (1 - S i i) * X i l -
      (if h : i.val + 1 < m + 1 then S i ⟨i.val + 1, h⟩ * X ⟨i.val + 1, h⟩ l else 0)
      = if i = l then 1 else 0 := by
    intro i l
    have := congrFun (congrFun hmul i) l
    rw [Matrix.mul_apply] at this
    simp only [Matrix.one_apply] at this
    rw [← this]
    by_cases h : i.val + 1 < m + 1
    · rw [dif_pos h]
      have hne : i ≠ (⟨i.val + 1, h⟩ : Fin (m+1)) := by
        intro hh; have := congrArg Fin.val hh; simp at this
      rw [Finset.sum_eq_add i ⟨i.val + 1, h⟩ hne]
      · simp [Matrix.sub_apply, Matrix.one_apply, hne]
        ring
      · intro c _ hc
        have : S i c = 0 := hb i c (Ne.symm hc.1) (fun hh => hc.2 (Fin.ext hh))
        simp [Matrix.sub_apply, Matrix.one_apply, this, Ne.symm hc.1]
      · intro h'; exact absurd (Finset.mem_univ _) h'
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rw [dif_neg h]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.sub_apply, Matrix.one_apply]
      · intro c _ hc
        have : S i c = 0 := hb i c (Ne.symm hc) (by have := c.isLt; omega)
        simp [Matrix.sub_apply, Matrix.one_apply, this, Ne.symm hc]
      · intro h'; exact absurd (Finset.mem_univ _) h'
  have hne : ∀ (i j : Fin (m+1)), (∏ v ∈ Finset.Icc i j, (1 - S v v)) ≠ 0 :=
    fun i j => Finset.prod_ne_zero_iff.2 (fun v _ => hd v)
  have step : ∀ (i l : Fin (m+1)),
      (∀ i' : Fin (m+1), i'.val = i.val + 1 →
        X i' l = if i' < l then (∏ v ∈ Finset.Ico i' l, S v (Fin.ofNat (m + 1) (v.val + 1))) /
          (∏ v ∈ Finset.Icc i' l, (1 - S v v)) else if i' = l then 1 / (1 - S i' i') else 0) →
      X i l = if i < l then (∏ v ∈ Finset.Ico i l, S v (Fin.ofNat (m + 1) (v.val + 1))) /
          (∏ v ∈ Finset.Icc i l, (1 - S v v)) else if i = l then 1 / (1 - S i i) else 0 := by
    intro i l ih
    have hr := row i l
    have hdi := hd i
    by_cases h : i.val + 1 < m + 1
    · rw [dif_pos h] at hr
      set i' : Fin (m+1) := ⟨i.val + 1, h⟩ with hi'
      have ih' := ih i' rfl
      have hof : Fin.ofNat (m + 1) (i.val + 1) = i' := by
        apply Fin.ext; simp [Fin.ofNat, Nat.mod_eq_of_lt h, hi']
      by_cases hil : i < l
      · have hne' : i ≠ l := ne_of_lt hil
        rw [if_neg hne'] at hr
        rw [if_pos hil]
        have hi'l : i' ≤ l := by
          rw [Fin.le_def]; have := Fin.lt_def.1 hil; simp [hi']; omega
        have hX' : X i' l = (∏ v ∈ Finset.Ico i' l, S v (Fin.ofNat (m + 1) (v.val + 1))) /
            (∏ v ∈ Finset.Icc i' l, (1 - S v v)) := by
          rcases hi'l.lt_or_eq with hlt | heq
          · rw [ih', if_pos hlt]
          · rw [ih', if_neg (not_lt.2 hi'l.ge |> fun _ => by rw [heq]; exact lt_irrefl _), if_pos heq]
            rw [heq]; simp
        have e1 := FreemiumActions.Threshold.prodIco (fun v => S v (Fin.ofNat (m + 1) (v.val + 1))) i i' l hil rfl
        have e2 := FreemiumActions.Threshold.prodIcc (fun v => 1 - S v v) i i' l hil rfl
        beta_reduce at e1 e2
        rw [e1, e2, hof]
        have hP := hne i' l
        have : (1 - S i i) * X i l = S i i' * X i' l := by linarith
        rw [hX'] at this
        field_simp
        field_simp at this
        linarith
      · rw [if_neg hil]
        have hX'0 : X i' l = 0 := by
          have := ih'
          have hnl : ¬ i' < l := by
            intro hlt; apply hil; rw [Fin.lt_def] at hlt ⊢; simp [hi'] at hlt; omega
          have hnl' : i' ≠ l := by
            intro heq; apply hil; rw [Fin.lt_def]; have := congrArg Fin.val heq; simp [hi'] at this; omega
          rw [this, if_neg hnl, if_neg hnl']
        rw [hX'0] at hr
        by_cases hil' : i = l
        · rw [if_pos hil']
          subst hil'
          simp at hr
          field_simp
          linarith
        · rw [if_neg hil']
          rw [if_neg hil'] at hr
          simp at hr
          rcases hr with hr | hr
          · exact absurd hr hdi
          · exact hr
    · rw [dif_neg h] at hr
      by_cases hil : i < l
      · exfalso; have := Fin.lt_def.1 hil; have := l.isLt; have := i.isLt; omega
      · rw [if_neg hil]
        by_cases hil' : i = l
        · rw [if_pos hil']
          subst hil'
          simp at hr
          field_simp
          linarith
        · rw [if_neg hil']
          rw [if_neg hil'] at hr
          simp at hr
          rcases hr with hr | hr
          · exact absurd hr hdi
          · exact hr
  have main : ∀ (l : Fin (m+1)) (n : ℕ) (i : Fin (m+1)), m - i.val = n →
      X i l = if i < l then (∏ v ∈ Finset.Ico i l, S v (Fin.ofNat (m + 1) (v.val + 1))) /
          (∏ v ∈ Finset.Icc i l, (1 - S v v)) else if i = l then 1 / (1 - S i i) else 0 := by
    intro l n
    induction n with
    | zero =>
      intro i hi
      apply step
      intro i' hi'
      have := i'.isLt; omega
    | succ n ih =>
      intro i hi
      apply step
      intro i' hi'
      apply ih
      omega
  have mm : ∀ i l, X i l = if i < l then (∏ v ∈ Finset.Ico i l, S v (Fin.ofNat (m + 1) (v.val + 1))) /
          (∏ v ∈ Finset.Icc i l, (1 - S v v)) else if i = l then 1 / (1 - S i i) else 0 :=
    fun i l => main l _ i rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i j hji
    rw [mm, if_neg (not_lt.2 hji.le), if_neg (ne_of_gt hji)]
  · intro i
    rw [mm, if_neg (lt_irrefl _), if_pos rfl]
  · intro i j hij
    rw [mm, if_pos hij]
