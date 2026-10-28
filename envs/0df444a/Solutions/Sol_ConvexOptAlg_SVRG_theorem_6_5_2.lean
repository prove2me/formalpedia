-- Prove2me | solution 2 for ConvexOptAlg.SVRG.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T03:39:34.399977+00:00
-- url     : https://prove2.me/submissions/6da17307-9c75-4dbc-b78b-c45e249e4515

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Theorems.Thm_Gradient_cocoercive
import Theorems.Thm_Gradient_convex_first_order
import Theorems.Thm_Gradient_descent_lemma

-- carved verbatim out of submission 5cff3f1a-262b-4e42-b670-aa35e51700e7, lines 510-561

section
set_option autoImplicit false
open ConvexOptAlg.SVRG
open scoped RealInnerProductSpace

theorem grad_sum {n m : ℕ} (hm : 0 < m)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : (m:ℝ) • fullGradient gs x = ∑ i, gs i x := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold fullGradient; rw [smul_smul, mul_inv_cancel₀ hm', one_smul]

theorem dir_sq_sum {n m : ℕ} {fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hF0 : fullGradient gs xstar = 0) (x y : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ‖direction gs x y i‖ ^ 2 ≤
      4 * β * (∑ i, fs i x - ∑ i, fs i xstar + (∑ i, fs i y - ∑ i, fs i xstar)) := by
  obtain ⟨hF, hc, hG⟩ := hfamily
  have hcoc : ∀ z, ∑ i, ‖gs i z - gs i xstar‖ ^ 2 ≤ 2 * β * (∑ i, fs i z - ∑ i, fs i xstar) := by
    intro z
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Gradient.cocoercive hβ (hF i) (hG i) (hc i) xstar z)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← sum_inner,
      ← grad_sum hm, hF0, smul_zero, inner_zero_left, sub_zero] at this
    exact this
  set c := fullGradient gs y with hcdef
  have hsumb : ∑ i, (gs i y - gs i xstar) = (m:ℝ) • c := by
    rw [Finset.sum_sub_distrib, ← grad_sum hm, ← grad_sum hm, hF0, smul_zero, sub_zero]
  have hdir : ∀ i, direction gs x y i = (gs i x - gs i xstar) - ((gs i y - gs i xstar) - c) := by
    intro i; simp only [direction, hcdef]; abel
  have hpt : ∀ i, ‖direction gs x y i‖ ^ 2 ≤
      2 * ‖gs i x - gs i xstar‖ ^ 2 + 2 * ‖(gs i y - gs i xstar) - c‖ ^ 2 := by
    intro i; rw [hdir i]
    have h1 := norm_sub_sq_real (gs i x - gs i xstar) ((gs i y - gs i xstar) - c)
    have h2 := norm_add_sq_real (gs i x - gs i xstar) ((gs i y - gs i xstar) - c)
    nlinarith [sq_nonneg ‖(gs i x - gs i xstar) + ((gs i y - gs i xstar) - c)‖]
  have hvar : ∑ i, ‖(gs i y - gs i xstar) - c‖ ^ 2 ≤ ∑ i, ‖gs i y - gs i xstar‖ ^ 2 := by
    have e : ∀ i, ‖(gs i y - gs i xstar) - c‖ ^ 2 =
        ‖gs i y - gs i xstar‖ ^ 2 - 2 * ⟪gs i y - gs i xstar, c⟫ + ‖c‖ ^ 2 :=
      fun i => norm_sub_sq_real _ _
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hsumb,
      real_inner_smul_left, real_inner_self_eq_norm_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (0:ℝ) ≤ m * ‖c‖ ^ 2 := by positivity
    linarith
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  have h1 := hcoc x
  have h2 := hcoc y
  linarith

end

section
set_option autoImplicit false
open ConvexOptAlg.SVRG

theorem epochOutput_snoc {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y₁ : EuclideanSpace ℝ (Fin n)) (s : ℕ) (r : Fin s → Fin k → Fin m)
    (a : Fin k → Fin m) :
    epochOutput gs η y₁ (s + 1) (Fin.snoc r a) = epochOut gs η k (epochOutput gs η y₁ s r) a := by
  simp [epochOutput]

end

section
set_option autoImplicit false
open ConvexOptAlg.SVRG
open scoped RealInnerProductSpace

theorem final_arith (P Q N r fst Δ α β k : ℝ) (hN : 0 < N) (hk : 0 < k) (hα : 0 < α)
    (hβ : 0 < β) (hβeq : β = k * α / 20) (hΔ : 0 ≤ Δ) (hJ : k * P ≤ Q)
    (htel : 4 / (25 * β) * (Q - k * (N * fst)) ≤ N * r + k * (N * (1 / (25 * β) * Δ)))
    (hr : α / 2 * r ≤ Δ) : P / N - fst ≤ 9 / 10 * Δ := by
  have hβ' : β ≠ 0 := hβ.ne'
  have h1 : Q - k * (N * fst) ≤ 25 * β / 4 * (N * r) + k * N * Δ / 4 := by
    have e : Q - k * (N * fst) = 25 * β / 4 * (4 / (25 * β) * (Q - k * (N * fst))) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left htel (by positivity : (0:ℝ) ≤ 25 * β / 4)
    have e2 : 25 * β / 4 * (N * r + k * (N * (1 / (25 * β) * Δ))) =
        25 * β / 4 * (N * r) + k * N * Δ / 4 := by
      field_simp
    linarith
  have h2 : 25 * β / 4 * (N * r) ≤ 5 / 8 * k * N * Δ := by
    rw [hβeq]
    have := mul_le_mul_of_nonneg_left hr (by positivity : (0:ℝ) ≤ 5 / 8 * k * N)
    linarith
  have hkN : 0 ≤ k * N * Δ := by positivity
  have h3 : k * P ≤ k * (N * (fst + 9 / 10 * Δ)) := by linarith
  have h4 : P ≤ N * (fst + 9 / 10 * Δ) := le_of_mul_le_mul_left h3 hk
  have : P / N ≤ fst + 9 / 10 * Δ := by
    rw [div_le_iff₀ hN]; linarith
  linarith

theorem obj_sum {n m : ℕ} (hm : 0 < m) (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, fs i x = (m:ℝ) * objective fs x := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold objective uniformMean
  rw [Fintype.card_fin]; field_simp

theorem grad_zero {n m : ℕ} {fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    fullGradient gs xstar = 0 := by
  obtain ⟨hF, _, hG⟩ := hfamily
  set G := ∑ i, gs i xstar with hGdef
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hm'' : (m:ℝ) ≠ 0 := hm'.ne'
  have hβ' : β ≠ 0 := hβ.ne'
  have hdesc : ∀ z, ∑ i, fs i z ≤
      ∑ i, fs i xstar + ⟪G, z - xstar⟫ + (m:ℝ) * (β / 2 * ‖z - xstar‖ ^ 2) := by
    intro z
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => Gradient.descent_lemma (hF i) (hG i) xstar z)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hminS : ∀ z, ∑ i, fs i xstar ≤ ∑ i, fs i z := by
    intro z; rw [obj_sum hm, obj_sum hm]; exact mul_le_mul_of_nonneg_left (hmin z) hm'.le
  set s : ℝ := 1 / ((m:ℝ) * β) with hsdef
  have hspos : 0 < s := by positivity
  have h1 := hdesc (xstar - s • G)
  have h2 := hminS (xstar - s • G)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos hspos, real_inner_self_eq_norm_sq] at h1
  have hs : (m:ℝ) * (β / 2 * (s * ‖G‖) ^ 2) = s / 2 * ‖G‖ ^ 2 := by
    rw [hsdef]; field_simp
  have hGn : ‖G‖ ^ 2 ≤ 0 := by nlinarith
  have hG2 : ‖G‖ ^ 2 = 0 := le_antisymm hGn (sq_nonneg _)
  have hG0 : G = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hG2)
  unfold fullGradient; rw [← hGdef, hG0, smul_zero]

theorem iter_update {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) (t : Fin k) (i : Fin m) :
    ∀ s, s ≤ t.val → innerIter gs η y (Function.update idx t i) s = innerIter gs η y idx s := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hlt : s < t.val := hs
    simp only [innerIter]
    rw [ih hlt.le]
    by_cases hk : s < k
    · rw [dif_pos hk, dif_pos hk, Function.update_of_ne]
      intro heq; rw [← heq] at hlt; exact lt_irrefl _ hlt
    · rw [dif_neg hk, dif_neg hk]

theorem iter_update_succ {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) (t : Fin k) (i : Fin m) :
    innerIter gs η y (Function.update idx t i) (t.val + 1) =
      innerIter gs η y idx t.val - η • direction gs (innerIter gs η y idx t.val) y i := by
  simp only [innerIter]
  rw [dif_pos t.isLt, iter_update gs η y idx t i t.val le_rfl]
  simp

end

section
set_option autoImplicit false
open ConvexOptAlg.SVRG

theorem mean_affine {A : Type*} [Fintype A] [Nonempty A] (c d : ℝ) (g : A → ℝ) :
    uniformMean (fun a => c + d * g a) = c + d * uniformMean g := by
  unfold uniformMean
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mean_mono {A : Type*} [Fintype A] {g h : A → ℝ} (hgh : ∀ a, g a ≤ h a) :
    uniformMean g ≤ uniformMean h := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => hgh a) (by positivity)

theorem sum_snoc {X : Type*} [Fintype X] (s : ℕ) (F : (Fin (s + 1) → X) → ℝ) :
    ∑ idx, F idx = ∑ r : Fin s → X, ∑ a : X, F (Fin.snoc r a) := by
  rw [← Fintype.sum_prod_type']
  let e : (Fin s → X) × X ≃ (Fin (s + 1) → X) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun idx => (fun j => idx j.castSucc, idx (Fin.last s))
      left_inv := by
        rintro ⟨r, a⟩
        simp
      right_inv := by
        intro idx
        exact Fin.snoc_init_self idx }
  exact (Fintype.sum_equiv e _ _ (fun p => rfl)).symm

theorem mean_snoc {X : Type*} [Fintype X] (s : ℕ) (F : (Fin (s + 1) → X) → ℝ) :
    uniformMean F = uniformMean (fun r : Fin s → X => uniformMean (fun a : X => F (Fin.snoc r a))) := by
  unfold uniformMean
  rw [sum_snoc, ← Finset.sum_div, div_div]
  congr 1
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring

end

section
set_option autoImplicit false
open ConvexOptAlg.SVRG
open scoped RealInnerProductSpace

theorem step_sum {n m : ℕ} {fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hF0 : fullGradient gs xstar = 0) (η : ℝ) (hη : 0 ≤ η) (x y : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ‖x - η • direction gs x y i - xstar‖ ^ 2 ≤
      (m:ℝ) * ‖x - xstar‖ ^ 2 - 2 * η * (∑ i, fs i x - ∑ i, fs i xstar) +
        η ^ 2 * (4 * β * (∑ i, fs i x - ∑ i, fs i xstar + (∑ i, fs i y - ∑ i, fs i xstar))) := by
  have e : ∀ i, ‖x - η • direction gs x y i - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪direction gs x y i, x - xstar⟫ +
        η ^ 2 * ‖direction gs x y i‖ ^ 2 := by
    intro i
    have : x - η • direction gs x y i - xstar = (x - xstar) - η • direction gs x y i := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_comm]
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← sum_inner]
  have hsd : ∑ i, direction gs x y i = ∑ i, gs i x := by
    simp only [direction]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, grad_sum hm]
    abel
  rw [hsd, sum_inner]
  have hlin : ∑ i, fs i x - ∑ i, fs i xstar ≤ ∑ i, ⟪gs i x, x - xstar⟫ := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_le_sum; intro i _
    have := Gradient.convex_first_order (hfamily.1 i) (hfamily.2.1 i) x xstar
    have h2 : ⟪gs i x, xstar - x⟫ = -⟪gs i x, x - xstar⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  have hq := dir_sq_sum hm hβ hfamily hF0 x y
  have h3 := mul_le_mul_of_nonneg_left hlin (by positivity : (0:ℝ) ≤ 2 * η)
  have h4 := mul_le_mul_of_nonneg_left hq (sq_nonneg η)
  linarith

theorem sum_update {k m : ℕ} [NeZero m] (F : (Fin k → Fin m) → ℝ) (t : Fin k) :
    ∑ idx : Fin k → Fin m, ∑ i : Fin m, F (Function.update idx t i) =
      (m:ℝ) * ∑ idx, F idx := by
  have h1 : ∀ idx : Fin k → Fin m, ∑ i, F (Function.update idx t i) =
      ∑ i, F (Function.update idx t (i + idx t)) := fun idx =>
    (Equiv.sum_comp (Equiv.addRight (idx t)) (fun j => F (Function.update idx t j))).symm
  rw [Finset.sum_congr rfl (fun idx _ => h1 idx), Finset.sum_comm]
  have h2 : ∀ i : Fin m, ∑ idx : Fin k → Fin m, F (Function.update idx t (i + idx t)) =
      ∑ idx, F idx := by
    intro i
    let e : (Fin k → Fin m) ≃ (Fin k → Fin m) :=
      { toFun := fun idx => Function.update idx t (i + idx t)
        invFun := fun idx => Function.update idx t (idx t - i)
        left_inv := by
          intro idx; funext j
          by_cases hj : j = t
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        right_inv := by
          intro idx; funext j
          by_cases hj : j = t
          · subst hj; simp
          · simp [Function.update_of_ne hj] }
    exact Equiv.sum_comp e F
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

theorem telescope (D E : ℕ → ℝ) (c B : ℝ) (k : ℕ)
    (h : ∀ s, s < k → D (s + 1) ≤ D s - c * E s + B) (hD : 0 ≤ D k) :
    c * ∑ s ∈ Finset.range k, E s ≤ D 0 + k * B := by
  have key : ∀ j, j ≤ k → D j + c * ∑ s ∈ Finset.range j, E s ≤ D 0 + j * B := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := h j (by omega)
      rw [Finset.sum_range_succ]
      push_cast
      linarith
  have := key k le_rfl
  linarith

end

section
set_option autoImplicit false

open ConvexOptAlg.SVRG in open scoped InnerProductSpace in
theorem svrg65_epoch {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (k : ℕ) (y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hα : 0 < α) (hβ : 0 < β)
    (hkexact : (k : ℝ) = 20 * (β / α))
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin k → Fin m =>
        objective fs (epochOut gs (1 / (10 * β)) k y idx)) -
        objective fs xstar ≤
      (9 / 10 : ℝ) * (objective fs y - objective fs xstar) := by
  have : NeZero m := ⟨hm.ne'⟩
  set η : ℝ := 1 / (10 * β) with hηdef
  have hη : 0 ≤ η := by positivity
  have hF0 := grad_zero hm hβ hfamily hmin
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hNpos : (0:ℝ) < (Fintype.card (Fin k → Fin m) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hΔ : 0 ≤ objective fs y - objective fs xstar := sub_nonneg.mpr (hmin y)
  have hstep : ∀ s, s < k →
      ∑ idx : Fin k → Fin m, ‖innerIter gs η y idx (s + 1) - xstar‖ ^ 2 ≤
        ∑ idx : Fin k → Fin m, ‖innerIter gs η y idx s - xstar‖ ^ 2 -
          (2 * η - 4 * β * η ^ 2) *
            ∑ idx : Fin k → Fin m, (objective fs (innerIter gs η y idx s) - objective fs xstar) +
          (Fintype.card (Fin k → Fin m) : ℝ) *
            (4 * β * η ^ 2 * (objective fs y - objective fs xstar)) := by
    intro s hs
    have hA := sum_update
      (fun idx : Fin k → Fin m => ‖innerIter gs η y idx (s + 1) - xstar‖ ^ 2) (⟨s, hs⟩ : Fin k)
    have hupd : ∀ (idx : Fin k → Fin m) (i : Fin m),
        innerIter gs η y (Function.update idx ⟨s, hs⟩ i) (s + 1) =
          innerIter gs η y idx s - η • direction gs (innerIter gs η y idx s) y i :=
      fun idx i => iter_update_succ gs η y idx ⟨s, hs⟩ i
    simp only [hupd] at hA
    have hb : ∀ idx : Fin k → Fin m,
        ∑ i, ‖innerIter gs η y idx s - η • direction gs (innerIter gs η y idx s) y i - xstar‖ ^ 2 ≤
          (m:ℝ) * (‖innerIter gs η y idx s - xstar‖ ^ 2 -
            (2 * η - 4 * β * η ^ 2) * (objective fs (innerIter gs η y idx s) - objective fs xstar) +
            4 * β * η ^ 2 * (objective fs y - objective fs xstar)) := by
      intro idx
      have h := step_sum hm hβ hfamily hF0 η hη (innerIter gs η y idx s) y
      rw [obj_sum hm fs (innerIter gs η y idx s), obj_sum hm fs xstar,
        obj_sum hm fs y] at h
      linarith
    have hsum := Finset.sum_le_sum (fun idx (_ : idx ∈ Finset.univ) => hb idx)
    rw [hA, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    exact le_of_mul_le_mul_left hsum hmR
  have htel := telescope
    (fun s => ∑ idx : Fin k → Fin m, ‖innerIter gs η y idx s - xstar‖ ^ 2)
    (fun s => ∑ idx : Fin k → Fin m, (objective fs (innerIter gs η y idx s) - objective fs xstar))
    (2 * η - 4 * β * η ^ 2)
    ((Fintype.card (Fin k → Fin m) : ℝ) * (4 * β * η ^ 2 * (objective fs y - objective fs xstar)))
    k hstep (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  beta_reduce at htel
  have hD0 : ∑ idx : Fin k → Fin m, ‖innerIter gs η y idx 0 - xstar‖ ^ 2 =
      (Fintype.card (Fin k → Fin m) : ℝ) * ‖y - xstar‖ ^ 2 := by
    show ∑ _idx : Fin k → Fin m, ‖y - xstar‖ ^ 2 = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hQ : ∑ s ∈ Finset.range k, ∑ idx : Fin k → Fin m,
      (objective fs (innerIter gs η y idx s) - objective fs xstar) =
      ∑ s ∈ Finset.range k, ∑ idx : Fin k → Fin m, objective fs (innerIter gs η y idx s) -
        (k:ℝ) * ((Fintype.card (Fin k → Fin m) : ℝ) * objective fs xstar) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Finset.card_range,
      nsmul_eq_mul]
  rw [hD0, hQ] at htel
  have hc : 2 * η - 4 * β * η ^ 2 = 4 / (25 * β) := by
    rw [hηdef]; field_simp; ring
  have hB : 4 * β * η ^ 2 = 1 / (25 * β) := by
    rw [hηdef]; field_simp; ring
  rw [hc, hB] at htel
  have hjen : ∀ idx : Fin k → Fin m, (k:ℝ) * objective fs (epochOut gs η k y idx) ≤
      ∑ t : Fin k, objective fs (innerIter gs η y idx t.val) := by
    intro idx
    have hz : ∑ t : Fin k, innerIter gs η y idx t.val = (k:ℝ) • epochOut gs η k y idx := by
      rw [epochOut, smul_smul, mul_inv_cancel₀ hkR.ne', one_smul]
    have h1 : ∀ t : Fin k, objective fs (epochOut gs η k y idx) +
        ⟪fullGradient gs (epochOut gs η k y idx),
          innerIter gs η y idx t.val - epochOut gs η k y idx⟫_ℝ ≤
        objective fs (innerIter gs η y idx t.val) := by
      intro t
      have h := hstrong (epochOut gs η k y idx) (Set.mem_univ _)
        (innerIter gs η y idx t.val) (Set.mem_univ _)
      have : 0 ≤ α / 2 * ‖innerIter gs η y idx t.val - epochOut gs η k y idx‖ ^ 2 := by
        positivity
      linarith
    have h2 := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => h1 t)
    rw [Finset.sum_add_distrib, ← inner_sum, Finset.sum_sub_distrib, hz] at h2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h2
    rw [← Nat.cast_smul_eq_nsmul ℝ k (epochOut gs η k y idx), sub_self, inner_zero_right,
      add_zero, nsmul_eq_mul] at h2
    exact h2
  have hsumJ := Finset.sum_le_sum (fun idx (_ : idx ∈ Finset.univ) => hjen idx)
  rw [← Finset.mul_sum, Finset.sum_comm,
    Fin.sum_univ_eq_sum_range
      (fun s => ∑ idx : Fin k → Fin m, objective fs (innerIter gs η y idx s)) k] at hsumJ
  have hr : α / 2 * ‖y - xstar‖ ^ 2 ≤ objective fs y - objective fs xstar := by
    have h := hstrong xstar (Set.mem_univ _) y (Set.mem_univ _)
    rw [hF0, inner_zero_left] at h
    linarith
  have hβeq : β = (k:ℝ) * α / 20 := by
    rw [hkexact]; field_simp
  show (∑ idx : Fin k → Fin m, objective fs (epochOut gs η k y idx)) /
      (Fintype.card (Fin k → Fin m) : ℝ) - objective fs xstar ≤
    9 / 10 * (objective fs y - objective fs xstar)
  exact final_arith _ _ _ _ _ _ α β (k:ℝ) hNpos hkR hα hβ hβeq hΔ hsumJ htel hr

open ConvexOptAlg.SVRG in open scoped InnerProductSpace in
theorem solution {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (k s : ℕ) (y₁ xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hs : 1 ≤ s)
    (hα : 0 < α) (hβ : 0 < β)
    (hkexact : (k : ℝ) = 20 * (β / α))
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin s → Fin k → Fin m =>
        objective fs (epochOutput gs (1 / (10 * β)) y₁ s idx)) -
        objective fs xstar ≤
      (9 / 10 : ℝ) ^ s * (objective fs y₁ - objective fs xstar) := by
  have : NeZero m := ⟨hm.ne'⟩
  clear hs
  induction s with
  | zero =>
    simp [uniformMean, epochOutput]
  | succ s ih =>
    rw [mean_snoc]
    have key : ∀ r : Fin s → Fin k → Fin m,
        uniformMean (fun a : Fin k → Fin m =>
          objective fs (epochOutput gs (1 / (10 * β)) y₁ (s + 1) (Fin.snoc r a))) ≤
        objective fs xstar + (9 / 10 : ℝ) *
          objective fs (epochOutput gs (1 / (10 * β)) y₁ s r) +
          (9 / 10 : ℝ) * (- objective fs xstar) := by
      intro r
      simp only [epochOutput_snoc]
      have := svrg65_epoch fs gs α β k (epochOutput gs (1 / (10 * β)) y₁ s r) xstar
        hm hk hα hβ hkexact hfamily hstrong hmin
      linarith
    have h2 := mean_mono key
    have h3 := mean_affine (objective fs xstar + (9 / 10 : ℝ) * (- objective fs xstar))
      (9 / 10 : ℝ)
      (fun r : Fin s → Fin k → Fin m => objective fs (epochOutput gs (1 / (10 * β)) y₁ s r))
    have h4 : uniformMean (fun r : Fin s → Fin k → Fin m =>
        objective fs xstar + (9 / 10 : ℝ) *
          objective fs (epochOutput gs (1 / (10 * β)) y₁ s r) +
          (9 / 10 : ℝ) * (- objective fs xstar)) =
        objective fs xstar + (9 / 10 : ℝ) * (- objective fs xstar) + (9 / 10 : ℝ) *
          uniformMean (fun r : Fin s → Fin k → Fin m =>
            objective fs (epochOutput gs (1 / (10 * β)) y₁ s r)) := by
      rw [← h3]
      congr 1
      funext r
      ring
    rw [h4] at h2
    rw [pow_succ]
    nlinarith [ih]

end
