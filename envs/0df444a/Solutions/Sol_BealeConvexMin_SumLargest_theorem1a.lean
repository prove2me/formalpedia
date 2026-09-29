-- Prove2me | solution 1 for BealeConvexMin.SumLargest.theorem1a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T17:48:19.9388+00:00
-- url     : https://prove2.me/submissions/bb528de7-fdec-443e-b915-8001d6f1f070

import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms



namespace BealeConvexMin.SumLargest

open Finset

/-- If `S0` has `τ` elements, all at least `t`, and every other value is at most `t`, then the
sum of the `τ` largest values is the sum over `S0`. -/
lemma top_sum {k τ : ℕ} (v : Fin k → ℝ) (S0 : Finset (Fin k)) (hc : S0.card = τ) (t : ℝ)
    (hin : ∀ i ∈ S0, t ≤ v i) (hout : ∀ j ∉ S0, v j ≤ t) :
    sumLargest τ v = ∑ i ∈ S0, v i := by
  have hτ : τ ≤ k := by
    have := Finset.card_le_univ S0
    rw [Fintype.card_fin] at this; omega
  unfold sumLargest
  rw [dif_pos hτ]
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    rw [mem_powersetCard] at hS
    have e1 : ∑ i ∈ S, v i = ∑ i ∈ S, (v i - t) + (S.card : ℝ) * t := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
    have e2 : ∑ i ∈ S0, v i = ∑ i ∈ S0, (v i - t) + (S0.card : ℝ) * t := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
    have h1 : ∑ i ∈ S, (v i - t) = ∑ i ∈ S.filter (· ∈ S0), (v i - t)
        + ∑ i ∈ S.filter (fun i => ¬ i ∈ S0), (v i - t) :=
      (sum_filter_add_sum_filter_not S (· ∈ S0) _).symm
    have h2 : ∑ i ∈ S.filter (fun i => ¬ i ∈ S0), (v i - t) ≤ 0 :=
      sum_nonpos (fun j hj => by have := hout j (mem_filter.1 hj).2; linarith)
    have h3 : ∑ i ∈ S.filter (· ∈ S0), (v i - t) ≤ ∑ i ∈ S0, (v i - t) :=
      sum_le_sum_of_subset_of_nonneg (fun i hi => (mem_filter.1 hi).2)
        (fun i hi _ => by linarith [hin i hi])
    rw [e1, e2, hS.2, hc]
    linarith
  · exact Finset.le_sup' (fun S => ∑ i ∈ S, v i) (mem_powersetCard.2 ⟨subset_univ _, hc⟩)

lemma L_zero {r s : ℕ} (P : Forms r s) (z : Fin r → ℝ) (u : Fin s → ℝ) :
    P.L z u 0 = P.L0 z u := rfl

lemma L_succ {r s : ℕ} (P : Forms r s) (z : Fin r → ℝ) (u : Fin s → ℝ) (f : Fin s) :
    P.L z u f.succ = P.L0 z u - u f := rfl

lemma card_lt {s τ : ℕ} (hτ : τ ≤ s) :
    (univ.filter (fun f : Fin s => (f : ℕ) < τ)).card = τ := by
  rw [Fin.card_filter_val_lt]; omega

theorem rearrangement {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ1 : 1 ≤ τ) (hτs : τ ≤ s)
    (z' : Fin r → ℝ) (u' : Fin s → ℝ) (hmono : Monotone u')
    (hτneg : u' ⟨τ - 1, by omega⟩ ≤ 0) :
    P.C τ z' u' =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z' l
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => (f : ℕ) < τ),
              (P.φ f + (τ : ℝ) * P.θ f - 1) * u' f
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => τ ≤ (f : ℕ)),
              (P.φ f + (τ : ℝ) * P.θ f) * u' f ∧
    P.C τ z' u' =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z' l
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => (f : ℕ) < τ),
              (P.φ f + (τ : ℝ) * P.θ f - 1) * (u' f - u' ⟨τ - 1, by omega⟩)
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => τ ≤ (f : ℕ)),
              (P.φ f + (τ : ℝ) * P.θ f) * (u' f - u' ⟨τ - 1, by omega⟩)
          + (∑ f, (P.φ f + (τ : ℝ) * P.θ f) - (τ : ℝ)) * u' ⟨τ - 1, by omega⟩ := by
  set m : Fin s := ⟨τ - 1, by omega⟩ with hm
  set Flt := univ.filter (fun f : Fin s => (f : ℕ) < τ) with hFlt
  set Fge := univ.filter (fun f : Fin s => τ ≤ (f : ℕ)) with hFge
  have hcard : Flt.card = τ := card_lt hτs
  set S0 := Flt.map (Fin.succEmb s) with hS0
  have hS0c : S0.card = τ := by rw [hS0, card_map, hcard]
  set L0 := P.L0 z' u' with hL0
  have hsum : sumLargest τ (P.L z' u') = ∑ i ∈ S0, P.L z' u' i := by
    apply top_sum _ S0 hS0c (L0 - u' m)
    · intro i hi
      rw [hS0, mem_map] at hi
      obtain ⟨f, hf, rfl⟩ := hi
      rw [hFlt, mem_filter] at hf
      rw [Fin.coe_succEmb, L_succ]
      have : u' f ≤ u' m := hmono (by rw [Fin.le_def, hm]; simp only; omega)
      linarith
    · intro j hj
      induction j using Fin.cases with
      | zero => rw [L_zero]; linarith
      | succ f =>
        rw [L_succ]
        have hf : ¬ (f : ℕ) < τ := by
          intro hlt; apply hj; rw [hS0, mem_map]
          exact ⟨f, by rw [hFlt, mem_filter]; exact ⟨mem_univ _, hlt⟩, rfl⟩
        have : u' m ≤ u' f := hmono (by rw [Fin.le_def, hm]; simp only; omega)
        linarith
  have hsum2 : ∑ i ∈ S0, P.L z' u' i = (τ : ℝ) * L0 - ∑ f ∈ Flt, u' f := by
    rw [hS0, sum_map]
    simp only [Fin.coe_succEmb, L_succ]
    rw [sum_sub_distrib, sum_const, hcard, nsmul_eq_mul]
  have hC : P.C τ z' u' = P.formA z' u' + ((τ : ℝ) * L0 - ∑ f ∈ Flt, u' f) := by
    unfold Forms.C; rw [hsum, hsum2]
  -- split sums over f into Flt and Fge
  have hsplit : ∀ w : Fin s → ℝ, ∑ f, w f = ∑ f ∈ Flt, w f + ∑ f ∈ Fge, w f := by
    intro w
    rw [← sum_filter_add_sum_filter_not univ (fun f : Fin s => (f : ℕ) < τ)]
    congr 1
    apply sum_congr _ (fun _ _ => rfl)
    ext f; simp [hFge, not_lt]
  have hfirst : P.C τ z' u' =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z' l
          + ∑ f ∈ Flt, (P.φ f + (τ : ℝ) * P.θ f - 1) * u' f
          + ∑ f ∈ Fge, (P.φ f + (τ : ℝ) * P.θ f) * u' f := by
    rw [hC, hL0]
    unfold Forms.formA Forms.L0
    rw [hsplit (fun f => P.φ f * u' f), hsplit (fun f => P.θ f * u' f)]
    simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum, one_mul]
    ring
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  have hc1 : ∑ f ∈ Flt, (P.φ f + (τ : ℝ) * P.θ f - 1) * (u' f - u' m) =
      ∑ f ∈ Flt, (P.φ f + (τ : ℝ) * P.θ f - 1) * u' f
        - (∑ f ∈ Flt, (P.φ f + (τ : ℝ) * P.θ f) - (τ : ℝ)) * u' m := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, sub_mul, one_mul]
    rw [sum_const, hcard, nsmul_eq_mul]
  have hc2 : ∑ f ∈ Fge, (P.φ f + (τ : ℝ) * P.θ f) * (u' f - u' m) =
      ∑ f ∈ Fge, (P.φ f + (τ : ℝ) * P.θ f) * u' f
        - (∑ f ∈ Fge, (P.φ f + (τ : ℝ) * P.θ f)) * u' m := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
  rw [hc1, hc2, hsplit (fun f => P.φ f + (τ : ℝ) * P.θ f)]
  ring

theorem C_convex {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s + 1) :
    ConvexOn ℝ Set.univ (fun p : (Fin r → ℝ) × (Fin s → ℝ) => P.C τ p.1 p.2) := by
  refine ⟨convex_univ, fun p _ q _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold Forms.C sumLargest
  rw [dif_pos hτ, dif_pos hτ, dif_pos hτ]
  -- linearity of the forms
  have hA : P.formA (a • p + b • q).1 (a • p + b • q).2 =
      a * P.formA p.1 p.2 + b * P.formA q.1 q.2 := by
    unfold Forms.formA
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum]
    simp only [mul_left_comm (P.A _), mul_left_comm (P.φ _)]
    linear_combination (-P.A0) * hab
  have hL : ∀ i, P.L (a • p + b • q).1 (a • p + b • q).2 i =
      a * P.L p.1 p.2 i + b * P.L q.1 q.2 i := by
    have hL0 : P.L0 (a • p + b • q).1 (a • p + b • q).2 = a * P.L0 p.1 p.2 + b * P.L0 q.1 q.2 := by
      unfold Forms.L0
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum]
      simp only [mul_left_comm (P.c0 _), mul_left_comm (P.θ _)]
      linear_combination (-P.c00) * hab
    intro i
    induction i using Fin.cases with
    | zero => simp only [L_zero]; exact hL0
    | succ f =>
      rw [L_succ, L_succ, L_succ, hL0]
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  rw [hA]
  have hsup : (univ.powersetCard τ).sup' (powersetCard_nonempty.mpr (by rw [Finset.card_univ, Fintype.card_fin]; exact hτ))
      (fun S => ∑ i ∈ S, P.L (a • p + b • q).1 (a • p + b • q).2 i) ≤
      a * (univ.powersetCard τ).sup' (powersetCard_nonempty.mpr (by rw [Finset.card_univ, Fintype.card_fin]; exact hτ))
        (fun S => ∑ i ∈ S, P.L p.1 p.2 i) +
      b * (univ.powersetCard τ).sup' (powersetCard_nonempty.mpr (by rw [Finset.card_univ, Fintype.card_fin]; exact hτ))
        (fun S => ∑ i ∈ S, P.L q.1 q.2 i) := by
    apply Finset.sup'_le
    intro S hS
    try dsimp only
    rw [Finset.sum_congr rfl (fun i _ => hL i), sum_add_distrib, ← mul_sum, ← mul_sum]
    have h1 := Finset.le_sup' (fun S => ∑ i ∈ S, P.L p.1 p.2 i) hS
    have h2 := Finset.le_sup' (fun S => ∑ i ∈ S, P.L q.1 q.2 i) hS
    try simp only at h1 h2
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  linarith

lemma sum_single_mul {n : ℕ} (c : Fin n → ℝ) (l : Fin n) (t : ℝ) :
    ∑ l', c l' * (Pi.single l t : Fin n → ℝ) l' = c l * t := by
  simp [Pi.single_apply]

lemma sL_zero {k : ℕ} (v : Fin k → ℝ) : sumLargest 0 v = 0 := by
  simp [sumLargest]

/-- A `τ`-subset avoiding a given element, when `τ ≤ k`. -/
lemma exists_sub_erase {k τ : ℕ} (a : Fin (k + 1)) (hτ : τ ≤ k) :
    ∃ T ⊆ (univ : Finset (Fin (k + 1))).erase a, T.card = τ :=
  exists_subset_card_eq (by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega)

lemma C_def {r s : ℕ} (P : Forms r s) (τ : ℕ) (z : Fin r → ℝ) (u : Fin s → ℝ) :
    P.C τ z u = P.formA z u + sumLargest τ (P.L z u) := rfl

lemma C00 {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s + 1) :
    P.C τ 0 0 = P.A0 + (τ : ℝ) * P.c00 := by
  obtain ⟨T, _, hT⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (s + 1)))) (n := τ)
    (by rw [card_univ, Fintype.card_fin]; exact hτ)
  rw [C_def, top_sum _ T hT (P.c00) (fun i _ => ?_) (fun j _ => ?_)]
  · have : ∀ i, P.L 0 0 i = P.c00 := by
      intro i; induction i using Fin.cases with
      | zero => simp [L_zero, Forms.L0]
      | succ f => simp [L_succ, Forms.L0]
    rw [sum_congr rfl (fun i _ => this i), sum_const, hT, nsmul_eq_mul]
    simp [Forms.formA]
  · induction i using Fin.cases with
    | zero => simp [L_zero, Forms.L0]
    | succ f => simp [L_succ, Forms.L0]
  · induction j using Fin.cases with
    | zero => simp [L_zero, Forms.L0]
    | succ f => simp [L_succ, Forms.L0]

theorem descent_rules {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s) (F : Finset (Fin r)) :
    (∀ l : Fin r, P.A l + (τ : ℝ) * P.c0 l < 0 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ (Pi.single l t) 0 < P.C τ 0 0) ∧
    (∀ l ∈ F, 0 < P.A l + (τ : ℝ) * P.c0 l →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ (Pi.single l (-t)) 0 < P.C τ 0 0) ∧
    (∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f < 0 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (Pi.single f t) < P.C τ 0 0) ∧
    (∀ f : Fin s, 1 < P.φ f + (τ : ℝ) * P.θ f →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (Pi.single f (-t)) < P.C τ 0 0) ∧
    (∑ f, (P.φ f + (τ : ℝ) * P.θ f) < (τ : ℝ) - 1 →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (fun _ => t) < P.C τ 0 0) ∧
    ((τ : ℝ) < ∑ f, (P.φ f + (τ : ℝ) * P.θ f) →
      ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
        P.C τ 0 (fun _ => -t) < P.C τ 0 0) := by
  have hτ1 : τ ≤ s + 1 := by omega
  have hC0 := C00 P τ hτ1
  -- C at (z, 0): all L equal
  have Cz : ∀ z : Fin r → ℝ, P.C τ z 0 = P.formA z 0 + (τ : ℝ) * P.L0 z 0 := by
    intro z
    obtain ⟨T, _, hT⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (s + 1)))) (n := τ)
      (by rw [card_univ, Fintype.card_fin]; exact hτ1)
    have hall : ∀ i, P.L z 0 i = P.L0 z 0 := by
      intro i; induction i using Fin.cases with
      | zero => rfl
      | succ f => rw [L_succ]; simp
    rw [C_def, top_sum _ T hT (P.L0 z 0) (fun i _ => (hall i).ge) (fun j _ => (hall j).le),
      sum_congr rfl (fun i _ => hall i), sum_const, hT, nsmul_eq_mul]
  have hzs : ∀ (l : Fin r) (t : ℝ), P.C τ (Pi.single l t) 0 =
      P.C τ 0 0 + (P.A l + (τ : ℝ) * P.c0 l) * t := by
    intro l t
    rw [Cz, hC0]
    simp only [Forms.formA, Forms.L0, sum_single_mul, Pi.zero_apply, mul_zero, sum_const_zero,
      add_zero]
    ring
  refine ⟨fun l hl => ⟨1, one_pos, fun t ht _ => ?_⟩, fun l _ hl => ⟨1, one_pos, fun t ht _ => ?_⟩,
    fun f hf => ⟨1, one_pos, fun t ht _ => ?_⟩, fun f hf => ⟨1, one_pos, fun t ht _ => ?_⟩,
    fun hf => ⟨1, one_pos, fun t ht _ => ?_⟩, fun hf => ⟨1, one_pos, fun t ht _ => ?_⟩⟩
  · rw [hzs]; nlinarith
  · rw [hzs]; nlinarith
  · -- u = single f t
    obtain ⟨T, hTs, hT⟩ := exists_sub_erase (Fin.succ f) hτ
    have hval : ∀ i, P.L 0 (Pi.single f t) i ≤ (P.L0 0 (Pi.single f t)) := by
      intro i; induction i using Fin.cases with
      | zero => exact le_rfl
      | succ g =>
        rw [L_succ]
        by_cases hg : g = f
        · subst hg; simp; linarith
        · simp [Pi.single_apply, hg]
    have hT' : ∀ i ∈ T, P.L 0 (Pi.single f t) i = (P.L0 0 (Pi.single f t)) := by
      intro i hi
      have hne : i ≠ f.succ := (mem_erase.1 (hTs hi)).1
      induction i using Fin.cases with
      | zero => rfl
      | succ g =>
        have : g ≠ f := fun h => hne (by rw [h])
        rw [L_succ]; simp [Pi.single_apply, this]
    rw [C_def, top_sum _ T hT (P.L0 0 (Pi.single f t)) (fun i hi => (hT' i hi).ge) (fun j _ => hval j),
      sum_congr rfl hT', sum_const, hT, nsmul_eq_mul, hC0]
    simp only [Forms.formA, Forms.L0, sum_single_mul, Pi.zero_apply, mul_zero, sum_const_zero,
      add_zero]
    nlinarith
  · -- u = single f (-t)
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · subst h0
      rw [C_def, sL_zero, hC0]
      simp only [Forms.formA, sum_single_mul, Pi.zero_apply, mul_zero, sum_const_zero, add_zero]
      simp at hf
      push_cast
      nlinarith [mul_lt_mul_of_pos_right hf ht]
    obtain ⟨T, hTs, hT⟩ := exists_sub_erase (k := s) (τ := τ - 1) (Fin.succ f) (by omega)
    set S0 := insert (Fin.succ f) T with hS0
    have hnot : Fin.succ f ∉ T := fun h => (mem_erase.1 (hTs h)).1 rfl
    have hS0c : S0.card = τ := by rw [hS0, card_insert_of_notMem hnot, hT]; omega
    have hvals : ∀ i, i ≠ Fin.succ f → P.L 0 (Pi.single f (-t)) i = (P.L0 0 (Pi.single f (-t))) := by
      intro i hne
      induction i using Fin.cases with
      | zero => rfl
      | succ g =>
        have : g ≠ f := fun h => hne (by rw [h])
        rw [L_succ]; simp [Pi.single_apply, this]
    have hf1 : P.L 0 (Pi.single f (-t)) (Fin.succ f) = (P.L0 0 (Pi.single f (-t))) + t := by
      rw [L_succ]; simp
    have hin : ∀ i ∈ S0, (P.L0 0 (Pi.single f (-t))) ≤ P.L 0 (Pi.single f (-t)) i := by
      intro i hi
      rw [hS0, mem_insert] at hi
      rcases hi with rfl | hi
      · rw [hf1]; linarith
      · rw [hvals i (fun h => hnot (h ▸ hi))]
    have hout : ∀ j ∉ S0, P.L 0 (Pi.single f (-t)) j ≤ (P.L0 0 (Pi.single f (-t))) := by
      intro j hj
      have : j ≠ Fin.succ f := fun h => hj (by rw [h, hS0]; exact mem_insert_self _ _)
      rw [hvals j this]
    rw [C_def, top_sum _ S0 hS0c (P.L0 0 (Pi.single f (-t))) hin hout, hS0, sum_insert hnot, hf1,
      sum_congr rfl (fun i hi => hvals i (fun h => hnot (h ▸ hi))), sum_const, hT,
      nsmul_eq_mul, hC0]
    simp only [Forms.formA, Forms.L0, sum_single_mul, Pi.zero_apply, mul_zero, sum_const_zero,
      add_zero]
    rw [Nat.cast_sub (by omega : 1 ≤ τ)]
    push_cast
    nlinarith
  · -- u = const t
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · subst h0
      rw [C_def, sL_zero, hC0]
      simp only [Forms.formA, Pi.zero_apply, mul_zero, sum_const_zero, add_zero]
      simp at hf
      rw [← sum_mul]
      push_cast
      nlinarith [mul_lt_mul_of_pos_right hf ht]
    obtain ⟨T, hTs, hT⟩ := exists_sub_erase (k := s) (τ := τ - 1) (0 : Fin (s + 1)) (by omega)
    set S0 := insert (0 : Fin (s + 1)) T with hS0
    have hnot : (0 : Fin (s + 1)) ∉ T := fun h => (mem_erase.1 (hTs h)).1 rfl
    have hS0c : S0.card = τ := by rw [hS0, card_insert_of_notMem hnot, hT]; omega
    have hvals : ∀ i, i ≠ 0 → P.L 0 (fun _ => t) i = (P.L0 0 (fun _ => t)) - t := by
      intro i hne
      induction i using Fin.cases with
      | zero => exact absurd rfl hne
      | succ g => rw [L_succ]
    have hin : ∀ i ∈ S0, (P.L0 0 (fun _ => t)) - t ≤ P.L 0 (fun _ => t) i := by
      intro i hi
      rw [hS0, mem_insert] at hi
      rcases hi with rfl | hi
      · rw [L_zero]; linarith
      · rw [hvals i (fun h => hnot (h ▸ hi))]
    have hout : ∀ j ∉ S0, P.L 0 (fun _ => t) j ≤ (P.L0 0 (fun _ => t)) - t := by
      intro j hj
      have : j ≠ 0 := fun h => hj (by rw [h, hS0]; exact mem_insert_self _ _)
      rw [hvals j this]
    rw [C_def, top_sum _ S0 hS0c ((P.L0 0 (fun _ => t)) - t) hin hout, hS0, sum_insert hnot, L_zero,
      sum_congr rfl (fun i hi => hvals i (fun h => hnot (h ▸ hi))), sum_const, hT,
      nsmul_eq_mul, hC0]
    simp only [Forms.formA, Forms.L0, Pi.zero_apply, mul_zero, sum_const_zero, add_zero]
    rw [Nat.cast_sub (by omega : 1 ≤ τ)]
    rw [sum_add_distrib, ← mul_sum] at hf
    rw [← sum_mul, ← sum_mul]
    push_cast
    nlinarith
  · -- u = const (-t)
    obtain ⟨T, hTs, hT⟩ := exists_sub_erase (k := s) (τ := τ) (0 : Fin (s + 1)) hτ
    have hvals : ∀ i, i ≠ 0 → P.L 0 (fun _ => -t) i = (P.L0 0 (fun _ => -t)) + t := by
      intro i hne
      induction i using Fin.cases with
      | zero => exact absurd rfl hne
      | succ g => rw [L_succ]; ring
    have hT' : ∀ i ∈ T, P.L 0 (fun _ => -t) i = (P.L0 0 (fun _ => -t)) + t :=
      fun i hi => hvals i (mem_erase.1 (hTs hi)).1
    have hout : ∀ j ∉ T, P.L 0 (fun _ => -t) j ≤ (P.L0 0 (fun _ => -t)) + t := by
      intro j _
      by_cases hj : j = 0
      · subst hj; rw [L_zero]; linarith
      · rw [hvals j hj]
    rw [C_def, top_sum _ T hT ((P.L0 0 (fun _ => -t)) + t) (fun i hi => (hT' i hi).ge) hout,
      sum_congr rfl hT', sum_const, hT, nsmul_eq_mul, hC0]
    simp only [Forms.formA, Forms.L0, Pi.zero_apply, mul_zero, sum_const_zero, add_zero]
    rw [sum_add_distrib, ← mul_sum] at hf
    rw [← sum_mul, ← sum_mul]
    nlinarith

lemma C_full {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ = s + 1) (z : Fin r → ℝ) (u : Fin s → ℝ) :
    P.C τ z u = P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z l
      + ∑ f, (P.φ f + (τ : ℝ) * P.θ f - 1) * u f := by
  have hc : (univ : Finset (Fin (s + 1))).card = τ := by rw [card_univ, Fintype.card_fin, hτ]
  rw [C_def, top_sum _ univ hc ((univ : Finset (Fin (s + 1))).inf' univ_nonempty (P.L z u))
    (fun i _ => Finset.inf'_le _ (mem_univ i)) (fun j hj => absurd (mem_univ j) hj)]
  rw [Fin.sum_univ_succ, L_zero]
  simp only [L_succ]
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Forms.formA Forms.L0
  simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum, one_mul]
  rw [hτ]; push_cast; ring

theorem theorem1b {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ = s + 1) (F : Finset (Fin r)) :
    (P.IsMinimizedAtZero τ F ↔
      P.Cond45 τ F ∧ ∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f - 1 = 0) ∧
    (∀ f : Fin s, P.φ f + (τ : ℝ) * P.θ f - 1 ≠ 0 →
      ∃ v : ℝ, v * (P.φ f + (τ : ℝ) * P.θ f - 1) < 0 ∧
        P.C τ 0 (Pi.single f v) < P.C τ 0 0) := by
  have hC := C_full P τ hτ
  have hC0 : P.C τ 0 0 = P.A0 + (τ : ℝ) * P.c00 := by rw [hC]; simp
  have hz : ∀ (l : Fin r) (x : ℝ), P.C τ (Pi.single l x) 0 =
      P.C τ 0 0 + (P.A l + (τ : ℝ) * P.c0 l) * x := by
    intro l x; rw [hC, hC0, sum_single_mul]; simp
  have hu : ∀ (f : Fin s) (x : ℝ), P.C τ 0 (Pi.single f x) =
      P.C τ 0 0 + (P.φ f + (τ : ℝ) * P.θ f - 1) * x := by
    intro f x; rw [hC, hC0, sum_single_mul]; simp
  refine ⟨⟨fun hmin => ?_, fun ⟨hcond, hd⟩ => ?_⟩, fun f hf => ?_⟩
  · have hcoef : ∀ l, 0 ≤ P.A l + (τ : ℝ) * P.c0 l := by
      intro l
      have := hmin (Pi.single l 1) 0 (fun l' _ => by
        by_cases h : l' = l
        · subst h; simp
        · simp [Pi.single_apply, h])
      rw [hz] at this; linarith
    have hcoefF : ∀ l ∈ F, P.A l + (τ : ℝ) * P.c0 l = 0 := by
      intro l hl
      have := hmin (Pi.single l (-1)) 0 (fun l' hl' => by
        have : l' ≠ l := fun h => hl' (h ▸ hl)
        simp [Pi.single_apply, this])
      rw [hz] at this
      have := hcoef l
      linarith
    have hd : ∀ f, P.φ f + (τ : ℝ) * P.θ f - 1 = 0 := by
      intro f
      have h1 := hmin 0 (Pi.single f 1) (fun _ _ => le_rfl)
      have h2 := hmin 0 (Pi.single f (-1)) (fun _ _ => le_rfl)
      rw [hu] at h1 h2
      linarith
    refine ⟨⟨hcoef, hcoefF, fun f => ?_, ?_⟩, hd⟩
    · have := hd f; constructor <;> linarith
    · have hsum : ∑ f, (P.φ f + (τ : ℝ) * P.θ f) = s := by
        rw [sum_congr rfl (fun f _ => show P.φ f + (τ : ℝ) * P.θ f = 1 by linarith [hd f])]
        simp
      rw [hsum, hτ]; push_cast; constructor <;> linarith
  · intro z u hz0
    rw [hC0, hC z u]
    have h1 : ∑ f, (P.φ f + (τ : ℝ) * P.θ f - 1) * u f = 0 := by
      apply sum_eq_zero; intro f _; rw [hd f, zero_mul]
    have h2 : 0 ≤ ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z l := by
      apply sum_nonneg; intro l _
      by_cases hl : l ∈ F
      · rw [hcond.2.1 l hl, zero_mul]
      · exact mul_nonneg (hcond.1 l) (hz0 l hl)
    linarith
  · refine ⟨-(P.φ f + (τ : ℝ) * P.θ f - 1), ?_, ?_⟩
    · have := sq_pos_of_ne_zero hf; nlinarith
    · rw [hu]
      have := sq_pos_of_ne_zero hf; nlinarith

/-- Fractional weights: `Σ w_i v_i ≤ sumLargest τ v` for `0 ≤ w ≤ 1`, `Σ w = τ`. -/
lemma frac_le_sumLargest {k τ : ℕ} (hτ : τ ≤ k) (v w : Fin k → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1) (hws : ∑ i, w i = τ) : ∑ i, w i * v i ≤ sumLargest τ v := by
  have hne : (univ.powersetCard τ : Finset (Finset (Fin k))).Nonempty :=
    powersetCard_nonempty.mpr (by rw [card_univ, Fintype.card_fin]; exact hτ)
  obtain ⟨S0, hS0, hmax⟩ := exists_max_image (univ.powersetCard τ) (fun S => ∑ i ∈ S, v i) hne
  rw [mem_powersetCard] at hS0
  have hsl : sumLargest τ v = ∑ i ∈ S0, v i := by
    unfold sumLargest; rw [dif_pos hτ]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun S hS => hmax S hS)
    · exact Finset.le_sup' (fun S => ∑ i ∈ S, v i) (mem_powersetCard.2 hS0)
  rw [hsl]
  -- exchange property
  have hexch : ∀ i ∈ S0, ∀ j ∉ S0, v j ≤ v i := by
    intro i hi j hj
    by_contra hlt
    push Not at hlt
    set S' := insert j (S0.erase i) with hS'
    have hj' : j ∉ S0.erase i := fun h => hj (mem_of_mem_erase h)
    have hc : S'.card = τ := by
      rw [hS', card_insert_of_notMem hj', card_erase_of_mem hi, hS0.2]
      have : 1 ≤ τ := by rw [← hS0.2]; exact card_pos.2 ⟨i, hi⟩
      omega
    have hsum : ∑ l ∈ S', v l = ∑ l ∈ S0, v l - v i + v j := by
      rw [hS', sum_insert hj', ← sum_erase_add _ _ hi]; ring
    have := hmax S' (mem_powersetCard.2 ⟨subset_univ _, hc⟩)
    try simp only at this
    linarith
  rcases Nat.eq_zero_or_pos τ with h0 | hpos
  · -- all weights vanish
    subst h0
    have hwz : ∀ i, w i = 0 := by
      intro i
      have := (sum_eq_zero_iff_of_nonneg (fun i _ => hw0 i)).1 (by rw [hws]; simp) i (mem_univ _)
      exact this
    have hS0e : S0 = ∅ := card_eq_zero.1 hS0.2
    simp [hwz, hS0e]
  · have hS0ne : S0.Nonempty := card_pos.1 (by rw [hS0.2]; exact hpos)
    obtain ⟨i0, hi0, hmin⟩ := exists_min_image S0 v hS0ne
    set m := v i0
    have hin : ∀ i ∈ S0, m ≤ v i := fun i hi => hmin i hi
    have hout : ∀ j ∉ S0, v j ≤ m := fun j hj => hexch i0 hi0 j hj
    have hsplit : ∀ g : Fin k → ℝ, ∑ i, g i = ∑ i ∈ S0, g i + ∑ i ∈ S0ᶜ, g i :=
      fun g => (sum_add_sum_compl S0 g).symm
    have e1 : ∑ i ∈ S0, v i - ∑ i, w i * v i =
        ∑ i ∈ S0, (1 - w i) * v i - ∑ i ∈ S0ᶜ, w i * v i := by
      rw [hsplit (fun i => w i * v i)]
      simp only [sub_mul, one_mul, sum_sub_distrib]; ring
    have h1 : ∑ i ∈ S0, (1 - w i) * m ≤ ∑ i ∈ S0, (1 - w i) * v i :=
      sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hin i hi) (by linarith [hw1 i]))
    have h2 : ∑ i ∈ S0ᶜ, w i * v i ≤ ∑ i ∈ S0ᶜ, w i * m :=
      sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hout j (mem_compl.1 hj)) (hw0 j))
    have h3 : ∑ i ∈ S0, (1 - w i) * m = ∑ i ∈ S0ᶜ, w i * m := by
      rw [← sum_mul, ← sum_mul, sum_sub_distrib, sum_const, hS0.2, nsmul_eq_mul, mul_one]
      have := hsplit w
      rw [hws] at this
      congr 1; linarith
    linarith

theorem theorem1a {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s) (F : Finset (Fin r)) :
    P.IsMinimizedAtZero τ F ↔ P.Cond45 τ F := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := descent_rules P τ hτ F
  constructor
  · intro hmin
    have hcoef : ∀ l, 0 ≤ P.A l + (τ : ℝ) * P.c0 l := by
      intro l
      by_contra h
      push Not at h
      obtain ⟨ε, hε, hdec⟩ := d1 l h
      have hlt := hdec (ε / 2) (by linarith) (by linarith)
      have := hmin (Pi.single l (ε / 2)) 0 (fun l' _ => by
        by_cases hl : l' = l
        · subst hl; simp; linarith
        · simp [hl])
      linarith
    refine ⟨hcoef, fun l hl => ?_, fun f => ⟨?_, ?_⟩, ?_, ?_⟩
    · by_contra h
      have hpos : 0 < P.A l + (τ : ℝ) * P.c0 l := lt_of_le_of_ne (hcoef l) (Ne.symm h)
      obtain ⟨ε, hε, hdec⟩ := d2 l hl hpos
      have hlt := hdec (ε / 2) (by linarith) (by linarith)
      have := hmin (Pi.single l (-(ε / 2))) 0 (fun l' hl' => by
        have : l' ≠ l := fun h => hl' (h ▸ hl)
        simp [this])
      linarith
    · by_contra h
      push Not at h
      obtain ⟨ε, hε, hdec⟩ := d3 f h
      have hlt := hdec (ε / 2) (by linarith) (by linarith)
      have := hmin 0 (Pi.single f (ε / 2)) (fun _ _ => le_rfl)
      linarith
    · by_contra h
      push Not at h
      obtain ⟨ε, hε, hdec⟩ := d4 f h
      have hlt := hdec (ε / 2) (by linarith) (by linarith)
      have := hmin 0 (Pi.single f (-(ε / 2))) (fun _ _ => le_rfl)
      linarith
    · by_contra h
      push Not at h
      obtain ⟨ε, hε, hdec⟩ := d5 h
      have hlt := hdec (ε / 2) (by linarith) (by linarith)
      have := hmin 0 (fun _ => ε / 2) (fun _ _ => le_rfl)
      linarith
    · by_contra h
      push Not at h
      obtain ⟨ε, hε, hdec⟩ := d6 h
      have hlt := hdec (ε / 2) (by linarith) (by linarith)
      have := hmin 0 (fun _ => -(ε / 2)) (fun _ _ => le_rfl)
      linarith
  · rintro ⟨hc1, hc2, hc3, hc4, hc5⟩ z u hz
    have hτ1 : τ ≤ s + 1 := by omega
    rw [C00 P τ hτ1]
    -- weights
    set c : Fin s → ℝ := fun f => P.φ f + (τ : ℝ) * P.θ f with hc
    set w : Fin (s + 1) → ℝ := fun i => Fin.cases ((τ : ℝ) - ∑ f, c f) c i with hw
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i; induction i using Fin.cases with
      | zero => simp only [hw, Fin.cases_zero]; linarith
      | succ f => simp only [hw, Fin.cases_succ]; exact (hc3 f).1
    have hw1 : ∀ i, w i ≤ 1 := by
      intro i; induction i using Fin.cases with
      | zero => simp only [hw, Fin.cases_zero]; linarith
      | succ f => simp only [hw, Fin.cases_succ]; exact (hc3 f).2
    have hws : ∑ i, w i = τ := by
      rw [Fin.sum_univ_succ]; simp only [hw, Fin.cases_zero, Fin.cases_succ]; ring
    have hfr := frac_le_sumLargest hτ1 (P.L z u) w hw0 hw1 hws
    have hwL : ∑ i, w i * P.L z u i = (τ : ℝ) * P.L0 z u - ∑ f, c f * u f := by
      rw [Fin.sum_univ_succ]
      simp only [hw, Fin.cases_zero, Fin.cases_succ, L_zero, L_succ, mul_sub, sum_sub_distrib,
        ← sum_mul]
      ring
    rw [hwL] at hfr
    have hzsum : 0 ≤ ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z l := by
      apply sum_nonneg; intro l _
      by_cases hl : l ∈ F
      · rw [hc2 l hl, zero_mul]
      · exact mul_nonneg (hc1 l) (hz l hl)
    rw [C_def]
    have hexp : P.formA z u + ((τ : ℝ) * P.L0 z u - ∑ f, c f * u f) =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z l := by
      unfold Forms.formA Forms.L0
      simp only [hc, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
      ring
    linarith

end BealeConvexMin.SumLargest

open BealeConvexMin.SumLargest

theorem solution {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ : τ ≤ s) (F : Finset (Fin r)) :
    P.IsMinimizedAtZero τ F ↔ P.Cond45 τ F := by
  exact theorem1a P τ hτ F
