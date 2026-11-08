-- Prove2me | solution 1 for BasketMVMNL.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:06:18.345146+00:00
-- url     : https://prove2.me/submissions/00715419-2995-4116-b39c-1f471db7b002

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace Aux_BasketMVMNL_eq7
open BasketMVMNL Finset

variable {J I : ℕ}

noncomputable def w (P : Instance J I) (j : Fin J) (o : Option (Fin I)) : ℝ := o.elim 1 (P.v j)
noncomputable def a (x : Assortment J I) (j : Fin J) (o : Option (Fin I)) : ℝ :=
  o.elim 1 (fun i => bit (x j i))
noncomputable def g (P : Instance J I) (x : Assortment J I) (j : Fin J) (o : Option (Fin I)) : ℝ :=
  a x j o * w P j o
noncomputable def ρ (P : Instance J I) (j : Fin J) (o : Option (Fin I)) : ℝ := o.elim 0 (P.r j)

lemma perm_ind (x : Assortment J I) (y : Bundle J I) :
    (if Permissible x y then (1 : ℝ) else 0) = ∏ j, a x j (y j) := by
  by_cases h : Permissible x y
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro j _
    cases hy : y j with
    | none => simp [a]
    | some i => simp [a, bit, h j i hy]
  · rw [if_neg h]
    simp only [Permissible, not_forall] at h
    obtain ⟨j, i, hy, hx⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [a, hy, bit, hx]

lemma exp_mu (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P) (y : Bundle J I) :
    Real.exp (mu P y) = ∏ j, w P j (y j) + (if y = emptyBundle J I then P.v0 - 1 else 0) := by
  unfold mu
  by_cases hy : y = emptyBundle J I
  · rw [if_pos hy, if_pos hy, Real.exp_log (by linarith [hP.one_lt_v0])]
    subst hy
    simp [w, emptyBundle]
  · rw [if_neg hy, if_neg hy, add_zero]
    have hψ0 : (∑ j, ∑ i, ∑ j', ∑ i',
        if j < j' ∧ y j = some i ∧ y j' = some i' then P.ψ j i j' i' else (0 : ℝ)) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      apply Finset.sum_eq_zero; intro i _
      apply Finset.sum_eq_zero; intro j' _
      apply Finset.sum_eq_zero; intro i' _
      split_ifs with h
      · exact hψ j i j' i' (ne_of_lt h.1)
      · rfl
    rw [hψ0, add_zero, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    cases hyj : y j with
    | none => simp [w]
    | some i0 =>
      simp only [w, Option.elim_some]
      rw [Real.exp_sum]
      rw [Finset.prod_eq_single i0]
      · simp [Real.exp_log (hP.v_pos j i0)]
      · intro i _ hi
        simp [Ne.symm hi]
      · simp

lemma rev_eq (P : Instance J I) (y : Bundle J I) : bundleRev P y = ∑ j, ρ P j (y j) := by
  unfold bundleRev
  apply Finset.sum_congr rfl
  intro j _
  cases hyj : y j with
  | none => simp [ρ]
  | some i0 => simp [ρ]

lemma sum_g (P : Instance J I) (x : Assortment J I) (j : Fin J) :
    ∑ o, g P x j o = γ P x j := by
  rw [Fintype.sum_option]
  simp only [g, a, w, Option.elim_none, Option.elim_some, one_mul, γ]
  congr 1
  apply Finset.sum_congr rfl; intro i _; ring

lemma sum_ρg (P : Instance J I) (x : Assortment J I) (j : Fin J) :
    ∑ o, ρ P j o * g P x j o = Λ P x j := by
  rw [Fintype.sum_option]
  simp only [g, a, w, ρ, Option.elim_none, Option.elim_some, zero_mul, zero_add, Λ]
  apply Finset.sum_congr rfl; intro i _; ring

lemma sum_filter_bundles (x : Assortment J I) (F : Bundle J I → ℝ) :
    ∑ y ∈ bundles x, F y = ∑ y, (∏ j, a x j (y j)) * F y := by
  rw [bundles, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  rw [← perm_ind]
  split_ifs <;> simp

lemma prod_a_none (x : Assortment J I) : ∏ j, a x j ((emptyBundle J I) j) = 1 := by
  simp [a, emptyBundle]

lemma den_eq (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P) (x : Assortment J I) :
    ∑ y ∈ bundles x, Real.exp (mu P y) = Γ P x + (P.v0 - 1) := by
  rw [sum_filter_bundles]
  simp only [exp_mu P hP hψ, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Γ]
    simp only [← Finset.prod_mul_distrib]
    have : ∀ y : Bundle J I, ∏ j, a x j (y j) * w P j (y j) = ∏ j, g P x j (y j) := fun y => rfl
    simp only [this]
    rw [← Fintype.prod_sum (fun j o => g P x j o)]
    exact Finset.prod_congr rfl (fun j _ => sum_g P x j)
  · rw [Finset.sum_eq_single (emptyBundle J I)]
    · rw [if_pos rfl, prod_a_none, one_mul]
    · intro y _ hy; rw [if_neg hy, mul_zero]
    · simp

lemma num_eq (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P) (x : Assortment J I) :
    ∑ y ∈ bundles x, bundleRev P y * Real.exp (mu P y)
      = ∑ j, ∏ j', (if j' = j then Λ P x j else γ P x j') := by
  rw [sum_filter_bundles]
  have h1 : ∀ y : Bundle J I, (∏ j, a x j (y j)) * (bundleRev P y * Real.exp (mu P y))
      = ∑ j, ∏ j', (if j' = j then ρ P j (y j') * g P x j' (y j') else g P x j' (y j')) := by
    intro y
    rw [exp_mu P hP hψ, rev_eq]
    have hz : (∑ j, ρ P j (y j)) * (if y = emptyBundle J I then P.v0 - 1 else 0) = 0 := by
      split_ifs with hy
      · subst hy; simp [ρ, emptyBundle]
      · rw [mul_zero]
    rw [mul_add, hz, add_zero, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have : ∀ j', (if j' = j then ρ P j (y j') * g P x j' (y j') else g P x j' (y j'))
        = (if j' = j then ρ P j (y j) else 1) * g P x j' (y j') := by
      intro j'; split_ifs with h
      · subst h; rfl
      · rw [one_mul]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    simp only [g]
    rw [Finset.prod_mul_distrib]
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Fintype.prod_sum (fun j' o => if j' = j then ρ P j o * g P x j' o else g P x j' o)]
  apply Finset.prod_congr rfl
  intro j' _
  by_cases h : j' = j
  · subst h; simp only [if_true]; exact sum_ρg P x j'
  · simp only [h, if_false]; exact sum_g P x j'

lemma γ_pos (P : Instance J I) (hP : P.Standing) (x : Assortment J I) (j : Fin J) :
    0 < γ P x j := by
  unfold γ
  have : 0 ≤ ∑ i, P.v j i * bit (x j i) := by
    apply Finset.sum_nonneg; intro i _
    apply mul_nonneg (hP.v_pos j i).le
    unfold bit; split_ifs <;> norm_num
  linarith

end Aux_BasketMVMNL_eq7

open BasketMVMNL Aux_BasketMVMNL_eq7 in
theorem solution {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (x : Assortment J I) :
    R P x = ∑ j, Rj P x j := by
  unfold R
  rw [num_eq P hP hψ, den_eq P hP hψ, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hγ := γ_pos P hP x j
  have hΓ : 0 < Γ P x := Finset.prod_pos (fun j _ => γ_pos P hP x j)
  have hv0 := hP.one_lt_v0
  have hQ : (∏ j', (if j' = j then Λ P x j else γ P x j')) * γ P x j = Λ P x j * Γ P x := by
    rw [Γ, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), if_pos rfl]
    have : ∏ j' ∈ Finset.univ.erase j, (if j' = j then Λ P x j else γ P x j')
        = ∏ j' ∈ Finset.univ.erase j, γ P x j' :=
      Finset.prod_congr rfl (fun j' hj' => if_neg (Finset.ne_of_mem_erase hj'))
    rw [this]; ring
  unfold Rj
  have hD : 0 < Γ P x + (P.v0 - 1) := by linarith
  have hE0 : 0 < ((P.v0 - 1) / Γ P x + 1) * γ P x j := by
    have := div_pos (by linarith : (0:ℝ) < P.v0 - 1) hΓ
    exact mul_pos (by linarith) hγ
  rw [div_eq_div_iff hD.ne' hE0.ne']
  have hE : ((P.v0 - 1) / Γ P x + 1) * γ P x j * Γ P x = (Γ P x + (P.v0 - 1)) * γ P x j := by
    field_simp; ring
  apply mul_right_cancel₀ hΓ.ne'
  calc (∏ j', (if j' = j then Λ P x j else γ P x j')) * (((P.v0 - 1) / Γ P x + 1) * γ P x j)
        * Γ P x
      = (∏ j', (if j' = j then Λ P x j else γ P x j')) * γ P x j * (Γ P x + (P.v0 - 1)) := by
        rw [mul_assoc, hE]; ring
    _ = Λ P x j * (Γ P x + (P.v0 - 1)) * Γ P x := by rw [hQ]; ring
