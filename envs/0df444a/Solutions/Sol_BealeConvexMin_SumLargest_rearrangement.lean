-- Prove2me | solution 1 for BealeConvexMin.SumLargest.rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T17:40:32.02425+00:00
-- url     : https://prove2.me/submissions/84c01625-d732-4027-b875-e96b78f089da

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

end BealeConvexMin.SumLargest

open BealeConvexMin.SumLargest

theorem solution {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ1 : 1 ≤ τ) (hτs : τ ≤ s)
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
  exact rearrangement P τ hτ1 hτs z' u' hmono hτneg
