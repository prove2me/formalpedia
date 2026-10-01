-- Prove2me | solution 1 for CandesTao.Decoding.l1_recovers_sparse_vector
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @radokirov
-- created : 2026-10-01T05:11:14.917922+00:00
-- url     : https://prove2.me/submissions/6f443d98-9c64-49a5-bf00-43ab4ba13e6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_CandesTao_Decoding_L1Minimization
import Theorems.Thm_CandesTao_Decoding_dual_reconstruction_linf
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open CandesTao.Decoding

namespace CandesTaoThm14

lemma nsq {n : ℕ} (x : Fin n → ℝ) : l2Norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2Norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

lemma mulVec_sq_le {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (x : Fin m → ℝ) :
    l2Norm (F.mulVec x) ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * l2Norm x ^ 2 := by
  rw [nsq, nsq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Under `δ_S < 1`, a vector supported on at most `S` columns with `F h = 0` vanishes. -/
lemma eq_zero_of_isometry {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hδ : restrictedIsometryConst F S < 1) (T : Finset (Fin m)) (hT : T.card ≤ S)
    (h : Fin m → ℝ) (hs : SupportedOn h T) (hF : F.mulVec h = 0) : h = 0 := by
  have hne : {δ : ℝ | 0 ≤ δ ∧ ∀ T : Finset (Fin m), T.card ≤ S → ∀ c : Fin m → ℝ,
      SupportedOn c T →
      (1 - δ) * l2Norm c ^ 2 ≤ l2Norm (F.mulVec c) ^ 2 ∧
      l2Norm (F.mulVec c) ^ 2 ≤ (1 + δ) * l2Norm c ^ 2}.Nonempty := by
    refine ⟨max 1 (∑ i, ∑ j, F i j ^ 2), le_trans zero_le_one (le_max_left _ _), ?_⟩
    intro U _ x _
    have h0 : 0 ≤ l2Norm x ^ 2 := sq_nonneg _
    have h1 : 0 ≤ l2Norm (F.mulVec x) ^ 2 := sq_nonneg _
    have hb := mulVec_sq_le F x
    have hm1 : 1 ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_left _ _
    have hmK : (∑ i, ∑ j, F i j ^ 2) ≤ max 1 (∑ i, ∑ j, F i j ^ 2) := le_max_right _ _
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨δ, hδmem, hδlt⟩ := exists_lt_of_csInf_lt hne hδ
  have key := (hδmem.2 T hT h hs).1
  rw [hF] at key
  have hz : l2Norm (0 : Fin p → ℝ) ^ 2 = 0 := by rw [nsq]; simp
  rw [hz] at key
  have hd0 : l2Norm h ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos (by linarith : (0 : ℝ) < 1 - δ) hc
    linarith
  rw [nsq] at hd0
  have hsum : ∑ i, h i ^ 2 = 0 :=
    le_antisymm hd0 (Finset.sum_nonneg fun i _ => sq_nonneg (h i))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (h i))] at hsum
  funext j
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hsum j (Finset.mem_univ j))

/-- `∑ⱼ hⱼ ⟨w, vⱼ⟩ = ⟨w, F h⟩`. -/
lemma sum_dot_column {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (w : Fin p → ℝ)
    (h : Fin m → ℝ) :
    ∑ j, dotProduct w (column F j) * h j = dotProduct w (F.mulVec h) := by
  simp only [dotProduct, column, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- the sign of a real number -/
noncomputable def sgn (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

lemma sgn_mul_self (x : ℝ) : sgn x * x = |x| := by
  unfold sgn
  split_ifs with h1 h2
  · rw [one_mul, abs_of_pos h1]
  · rw [abs_of_neg h2]; ring
  · have : x = 0 := by linarith [not_lt.mp h1, not_lt.mp h2]
    simp [this]

lemma sgn_mul_le_abs (s x : ℝ) (hs : |s| ≤ 1) : s * x ≤ |x| := by
  calc s * x ≤ |s * x| := le_abs_self _
    _ = |s| * |x| := abs_mul _ _
    _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ = |x| := one_mul _

lemma abs_sgn_le (x : ℝ) : |sgn x| ≤ 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma sgn_sq_le (x : ℝ) : sgn x ^ 2 ≤ 1 := by
  unfold sgn; split_ifs <;> norm_num

end CandesTaoThm14

open CandesTaoThm14 in
theorem solution {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 3 * S ≤ m)
    (h : restrictedIsometryConst F S + restrictedOrthogonalityConst F S S +
      restrictedOrthogonalityConst F S (2 * S) < 1)
    (T : Finset (Fin m)) (c : Fin m → ℝ) (hT : T.card ≤ S) (hc : SupportedOn c T) :
    IsUniqueL1Minimizer F (F.mulVec c) c := by
  classical
  set δ := restrictedIsometryConst F S with hδdef
  set θ := restrictedOrthogonalityConst F S S with hθdef
  set θ₂ := restrictedOrthogonalityConst F S (2 * S) with hθ₂def
  have hθ0 : 0 ≤ θ := Real.sInf_nonneg fun x hx => hx.1
  have hθ₂0 : 0 ≤ θ₂ := Real.sInf_nonneg fun x hx => hx.1
  have hδ1 : δ < 1 := by linarith
  have hden : 0 < 1 - δ - θ₂ := by linarith
  -- the sign pattern of `c` on `T`
  set σ : Fin m → ℝ := fun j => if j ∈ T then sgn (c j) else 0 with hσdef
  have hσs : SupportedOn σ T := by intro j hj; simp [hσdef, hj]
  have hσn : l2Norm σ ≤ Real.sqrt S := by
    unfold l2Norm
    apply Real.sqrt_le_sqrt
    calc ∑ j, σ j ^ 2 ≤ ∑ j, (if j ∈ T then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j ∈ T
          · simp only [hσdef, hj, if_true]; exact sgn_sq_le _
          · simp [hσdef, hj]
      _ = T.card := by rw [Finset.sum_boole]; simp
      _ ≤ S := by exact_mod_cast hT
  -- the dual certificate from Lemma 2.2
  obtain ⟨w, -, hwT, hwoff⟩ :=
    dual_reconstruction_linf F S hS hSm (by linarith) T σ hT hσs
  set a : Fin m → ℝ := fun j => dotProduct w (column F j) with hadef
  have hsqrt : 0 < Real.sqrt (S : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS)
  have hoff : ∀ j, j ∉ T → |a j| < 1 := by
    intro j hj
    have hb := hwoff j hj
    have h1 : θ / ((1 - δ - θ₂) * Real.sqrt S) * l2Norm σ ≤ θ / (1 - δ - θ₂) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hden hsqrt) hden]
      have := mul_le_mul_of_nonneg_left hσn hθ0
      nlinarith [mul_le_mul_of_nonneg_left this hden.le]
    have h2 : θ / (1 - δ - θ₂) < 1 := by
      rw [div_lt_one hden]; linarith
    exact lt_of_le_of_lt (le_trans hb h1) h2
  have hon : ∀ j, j ∈ T → a j = sgn (c j) := by
    intro j hj
    rw [hadef]; simp only
    rw [hwT j hj]; simp [hσdef, hj]
  refine ⟨rfl, ?_⟩
  intro d hd hne
  set e : Fin m → ℝ := d - c with hedef
  have hFe : F.mulVec e = 0 := by rw [hedef, Matrix.mulVec_sub, hd, sub_self]
  -- termwise: |c_j + e_j| ≥ |c_j| + a_j e_j + g_j
  set g : Fin m → ℝ := fun j => if j ∈ T then 0 else (1 - |a j|) * |e j| with hgdef
  have hterm : ∀ j, |c j| + a j * e j + g j ≤ |d j| := by
    intro j
    have hdj : d j = c j + e j := by rw [hedef]; simp
    rw [hdj]
    by_cases hj : j ∈ T
    · simp only [hgdef, hj, if_true, add_zero]
      rw [hon j hj, ← sgn_mul_self (c j), ← mul_add]
      exact sgn_mul_le_abs _ _ (abs_sgn_le _)
    · simp only [hgdef, hj, if_false]
      rw [hc j hj, abs_zero, zero_add, zero_add]
      have hae : a j * e j ≤ |a j| * |e j| := by
        rw [← abs_mul]; exact le_abs_self _
      nlinarith
  have hsum0 : ∑ j, a j * e j = 0 := by
    rw [hadef]
    simp only
    rw [sum_dot_column, hFe, dotProduct_zero]
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    simp only [hgdef]
    split_ifs with hj
    · exact le_rfl
    · exact mul_nonneg (by linarith [hoff j hj]) (abs_nonneg _)
  -- some coordinate of `e` off `T` is nonzero
  have hex : ∃ j, j ∉ T ∧ e j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have he0 : e = 0 := eq_zero_of_isometry F S hδ1 T hT e hcon hFe
    apply hne
    funext j
    have := congrFun he0 j
    rw [hedef] at this
    simpa [sub_eq_zero] using this
  obtain ⟨j₀, hj₀T, hj₀e⟩ := hex
  have hgpos : 0 < g j₀ := by
    simp only [hgdef, hj₀T, if_false]
    exact mul_pos (by linarith [hoff j₀ hj₀T]) (abs_pos.mpr hj₀e)
  have hgsum : 0 < ∑ j, g j :=
    lt_of_lt_of_le hgpos (Finset.single_le_sum (fun j _ => hg0 j) (Finset.mem_univ j₀))
  have htot : ∑ j, (|c j| + a j * e j + g j) ≤ ∑ j, |d j| :=
    Finset.sum_le_sum fun j _ => hterm j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum0] at htot
  unfold l1Norm
  linarith
