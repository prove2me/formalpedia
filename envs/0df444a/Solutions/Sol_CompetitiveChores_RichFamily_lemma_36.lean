-- Prove2me | solution 1 for CompetitiveChores.RichFamily.lemma_36
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:23:47.801018+00:00
-- url     : https://prove2.me/submissions/18eece7b-8866-4439-ab46-e504d4c5e024

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

open CompetitiveChores.RichFamily in
theorem solution {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (z : Fin n → Fin m → ℝ) (hz : IsFeasible z) (p : Fin m → ℝ)
    (hp : ∀ j, p j < 0) :
    IsCompetitiveWith v b z p ↔
      ((∀ i j, 0 < z i j → ∀ c, v i c / |p c| ≤ v i j / |p j|) ∧
        ∀ i, b i = bundlePrice p (z i)) := by
  classical
  have hz0 : ∀ i j, 0 ≤ z i j := hz.1
  have habs : ∀ j, |p j| = -p j := fun j => abs_of_neg (hp j)
  have habspos : ∀ j, 0 < |p j| := fun j => abs_pos.mpr (hp j).ne
  -- if the price of z i is nonzero there is a chore in its support
  have hsupp : ∀ i, bundlePrice p (z i) ≠ 0 → ∃ j, 0 < z i j := by
    intro i h
    by_contra hcon
    push_neg at hcon
    apply h
    unfold bundlePrice
    apply Finset.sum_eq_zero
    intro j _
    have : z i j = 0 := le_antisymm (hcon j) (hz0 i j)
    rw [this, mul_zero]
  constructor
  · rintro ⟨_, _, hopt⟩
    have hbud : ∀ i, b i = bundlePrice p (z i) := by
      intro i
      obtain ⟨hle, hbest⟩ := hopt i
      by_contra hne
      have hlt : bundlePrice p (z i) < b i := lt_of_le_of_ne hle (Ne.symm hne)
      have hPneg : bundlePrice p (z i) < 0 := lt_trans hlt (hb i)
      obtain ⟨j0, hj0⟩ := hsupp i hPneg.ne
      have hUneg : bundleUtility v i (z i) < 0 := by
        unfold bundleUtility
        have hle0 : ∀ j ∈ Finset.univ, v i j * z i j ≤ 0 :=
          fun j _ => mul_nonpos_of_nonpos_of_nonneg (hv i j).le (hz0 i j)
        have := Finset.sum_lt_sum_of_nonempty (s := {j0}) (f := fun j => v i j * z i j)
          (g := fun _ => (0 : ℝ)) ⟨j0, Finset.mem_singleton_self _⟩
          (fun j hj => by rw [Finset.mem_singleton.mp hj]; exact mul_neg_of_neg_of_pos (hv i j0) hj0)
        simp only [Finset.sum_singleton, Finset.sum_const_zero] at this
        calc ∑ j, v i j * z i j ≤ v i j0 * z i j0 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
              have : ∑ x ∈ Finset.univ.erase j0, v i x * z i x ≤ 0 :=
                Finset.sum_nonpos (fun x _ => hle0 x (Finset.mem_univ x))
              linarith
          _ < 0 := this
      set t := b i / bundlePrice p (z i) with ht
      have ht1 : t < 1 := by rw [ht, div_lt_one_of_neg hPneg]; exact hlt
      have ht0 : 0 < t := div_pos_of_neg_of_neg (hb i) hPneg
      have hx := hbest (fun j => t * z i j) (fun j => mul_nonneg ht0.le (hz0 i j)) (by
        unfold bundlePrice at hPneg ⊢
        have : ∑ j, p j * (t * z i j) = t * ∑ j, p j * z i j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        rw [this, ht]
        unfold bundlePrice
        rw [div_mul_cancel₀ _ hPneg.ne])
      have : bundleUtility v i (fun j => t * z i j) = t * bundleUtility v i (z i) := by
        unfold bundleUtility
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      rw [this] at hx
      nlinarith
    refine ⟨?_, hbud⟩
    intro i j hij c
    by_contra hcon
    push_neg at hcon
    have hcj : c ≠ j := by rintro rfl; exact lt_irrefl _ hcon
    obtain ⟨hle, hbest⟩ := hopt i
    set q := |p j| * z i j / |p c| with hq
    let x : Fin m → ℝ := fun k => z i k - (if k = j then z i j else 0) + (if k = c then q else 0)
    have hqpos : 0 < q := by rw [hq]; exact div_pos (mul_pos (habspos j) hij) (habspos c)
    have hx0 : ∀ k, 0 ≤ x k := by
      intro k
      simp only [x]
      by_cases hk : k = j
      · subst hk; rw [if_pos rfl, if_neg (Ne.symm hcj)]; simp
      · rw [if_neg hk]; split_ifs <;> linarith [hz0 i k]
    have hpx : bundlePrice p x = bundlePrice p (z i) := by
      unfold bundlePrice
      simp only [x, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have : p c * q = p j * z i j := by
        rw [hq, habs j, habs c]; field_simp [(hp c).ne]
      rw [this]; ring
    have hvx : bundleUtility v i x = bundleUtility v i (z i) +
        z i j * |p j| * (v i c / |p c| - v i j / |p j|) := by
      unfold bundleUtility
      simp only [x, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hq]
      field_simp [(habspos c).ne', (habspos j).ne']
      ring
    have := hbest x hx0 (by rw [hpx]; exact hle)
    rw [hvx] at this
    have hpos : 0 < z i j * |p j| * (v i c / |p c| - v i j / |p j|) :=
      mul_pos (mul_pos hij (habspos j)) (by linarith)
    linarith
  · rintro ⟨hmbb, hbud⟩
    refine ⟨hz, hp, fun i => ⟨(hbud i).symm.le, ?_⟩⟩
    intro x hx0 hpx
    obtain ⟨j0, hj0⟩ := hsupp i (by rw [← hbud i]; exact (hb i).ne)
    set ρ := v i j0 / |p j0| with hρ
    have hρneg : ρ < 0 := div_neg_of_neg_of_pos (hv i j0) (habspos j0)
    have hle : ∀ c, v i c ≤ ρ * |p c| := by
      intro c
      have := hmbb i j0 hj0 c
      rw [div_le_iff₀ (habspos c)] at this
      exact this
    have heq : ∀ j, 0 < z i j → v i j = ρ * |p j| := by
      intro j hj
      apply le_antisymm (hle j)
      have := hmbb i j hj j0
      rw [← hρ, le_div_iff₀ (habspos j)] at this
      exact this
    have hUz : bundleUtility v i (z i) = -ρ * bundlePrice p (z i) := by
      unfold bundleUtility bundlePrice
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rcases (hz0 i j).lt_or_eq with hj | hj
      · rw [heq j hj, habs j]; ring
      · rw [← hj]; ring
    have hUx : bundleUtility v i x ≤ -ρ * bundlePrice p x := by
      unfold bundleUtility bundlePrice
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c _
      have := mul_le_mul_of_nonneg_right (hle c) (hx0 c)
      rw [habs c] at this
      linarith
    rw [hUz, ← hbud i]
    have : -ρ * bundlePrice p x ≤ -ρ * b i := mul_le_mul_of_nonneg_left hpx (by linarith)
    linarith
