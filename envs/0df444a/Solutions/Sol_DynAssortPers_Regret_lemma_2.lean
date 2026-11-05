-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:06:44.074195+00:00
-- url     : https://prove2.me/submissions/e4be51e2-3f5b-4a24-aa57-5865c4938bdb

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Estimator

namespace DAPl2

variable {n : ℕ}

noncomputable def Dn (S : Finset (Fin n)) (θ v : Fin n → ℝ) (s : ℝ) : ℝ :=
  1 + ∑ j ∈ S, Real.exp (θ j + s * v j)
noncomputable def N1 (S : Finset (Fin n)) (θ v : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ S, Real.exp (θ j + s * v j) * v j
noncomputable def N2 (S : Finset (Fin n)) (θ v : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ S, Real.exp (θ j + s * v j) * v j ^ 2

lemma hasDerivAt_exp_line (a b s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (a + s * b)) (Real.exp (a + s * b) * b) s := by
  have h1 : HasDerivAt (fun s : ℝ => a + s * b) b s := by
    simpa using ((hasDerivAt_id s).mul_const b).const_add a
  exact h1.exp

lemma Dn_pos (S : Finset (Fin n)) (θ v : Fin n → ℝ) (s : ℝ) : 0 < Dn S θ v s := by
  unfold Dn
  have := Finset.sum_nonneg (s := S) (fun k _ => (Real.exp_pos (θ k + s * v k)).le)
  linarith

lemma hasDerivAt_Dn (S : Finset (Fin n)) (θ v : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (Dn S θ v) (N1 S θ v s) s := by
  have := HasDerivAt.fun_sum (u := S) (fun k _ => hasDerivAt_exp_line (θ k) (v k) s)
  unfold Dn N1
  exact this.const_add 1

lemma hasDerivAt_N1 (S : Finset (Fin n)) (θ v : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (N1 S θ v) (N2 S θ v s) s := by
  have := HasDerivAt.fun_sum (u := S) (fun k _ => (hasDerivAt_exp_line (θ k) (v k) s).mul_const (v k))
  unfold N1 N2
  refine this.congr_deriv (Finset.sum_congr rfl (fun k _ => by ring))

/-- Cauchy–Schwarz plus the outside option: `N2 ≤ N2 * D − N1²`. -/
lemma hess_lower (S : Finset (Fin n)) (θ v : Fin n → ℝ) (s : ℝ) :
    N2 S θ v s ≤ N2 S θ v s * Dn S θ v s - N1 S θ v s ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun j => Real.sqrt (Real.exp (θ j + s * v j)))
    (fun j => Real.sqrt (Real.exp (θ j + s * v j)) * v j)
  have e1 : ∀ j, Real.sqrt (Real.exp (θ j + s * v j)) * (Real.sqrt (Real.exp (θ j + s * v j)) * v j)
      = Real.exp (θ j + s * v j) * v j := by
    intro j; rw [← mul_assoc, Real.mul_self_sqrt (Real.exp_pos _).le]
  have e2 : ∀ j, Real.sqrt (Real.exp (θ j + s * v j)) ^ 2 = Real.exp (θ j + s * v j) := by
    intro j; rw [Real.sq_sqrt (Real.exp_pos _).le]
  have e3 : ∀ j, (Real.sqrt (Real.exp (θ j + s * v j)) * v j) ^ 2 =
      Real.exp (θ j + s * v j) * v j ^ 2 := by
    intro j; rw [mul_pow, e2]
  simp only [e1, e2, e3] at hcs
  unfold N1 N2 Dn
  have hN2 : 0 ≤ ∑ j ∈ S, Real.exp (θ j + s * v j) * v j ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  nlinarith

lemma line_bound (S : Finset (Fin n)) (θ v : Fin n → ℝ) (b : ℝ)
    (h0 : ∀ j ∈ S, |θ j| ≤ b) (h1 : ∀ j ∈ S, |θ j + v j| ≤ b) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ∀ j ∈ S, |θ j + s * v j| ≤ b := by
  intro j hj
  have a0 := abs_le.1 (h0 j hj)
  have a1 := abs_le.1 (h1 j hj)
  rw [abs_le]
  constructor <;> nlinarith [hs.1, hs.2]

lemma hess_bound (S : Finset (Fin n)) (θ v : Fin n → ℝ) (b : ℝ) (s : ℝ)
    (hy : ∀ j ∈ S, |θ j + s * v j| ≤ b) :
    Real.exp (-b) / (1 + S.card * Real.exp b) ^ 2 * ∑ j ∈ S, v j ^ 2 ≤
      (N2 S θ v s * Dn S θ v s - N1 S θ v s * N1 S θ v s) / Dn S θ v s ^ 2 := by
  have hD := Dn_pos S θ v s
  have hl := hess_lower S θ v s
  have hN2 : Real.exp (-b) * ∑ j ∈ S, v j ^ 2 ≤ N2 S θ v s := by
    unfold N2; rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have := (abs_le.1 (hy j hj)).1
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 this) (sq_nonneg _)
  have hDle : Dn S θ v s ≤ 1 + S.card * Real.exp b := by
    unfold Dn
    have : ∑ j ∈ S, Real.exp (θ j + s * v j) ≤ ∑ j ∈ S, Real.exp b :=
      Finset.sum_le_sum (fun j hj => Real.exp_le_exp.2 (abs_le.1 (hy j hj)).2)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    linarith
  have hQ : 0 ≤ Real.exp (-b) * ∑ j ∈ S, v j ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [div_mul_eq_mul_div]
  calc (Real.exp (-b) * ∑ j ∈ S, v j ^ 2) / (1 + S.card * Real.exp b) ^ 2
      ≤ (Real.exp (-b) * ∑ j ∈ S, v j ^ 2) / Dn S θ v s ^ 2 := by
        apply div_le_div_of_nonneg_left hQ (by positivity)
        exact pow_le_pow_left₀ hD.le hDle 2
    _ ≤ N2 S θ v s / Dn S θ v s ^ 2 := div_le_div_of_nonneg_right hN2 (by positivity)
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : N1 S θ v s * N1 S θ v s = N1 S θ v s ^ 2 := by ring
        linarith

theorem breg_line (S : Finset (Fin n)) (θ v : Fin n → ℝ) (b : ℝ)
    (h0 : ∀ j ∈ S, |θ j| ≤ b) (h1 : ∀ j ∈ S, |θ j + v j| ≤ b) :
    (1 / 2) * (Real.exp (-b) / (1 + S.card * Real.exp b) ^ 2) * ∑ j ∈ S, v j ^ 2 ≤
      Real.log (Dn S θ v 1) - Real.log (Dn S θ v 0) - N1 S θ v 0 / Dn S θ v 0 := by
  set c := Real.exp (-b) / (1 + S.card * Real.exp b) ^ 2 with hc
  set Q := ∑ j ∈ S, v j ^ 2 with hQ
  set G := N1 S θ v 0 / Dn S θ v 0 with hG
  let h : ℝ → ℝ := fun s => Real.log (Dn S θ v s) - Real.log (Dn S θ v 0) - s * G - c / 2 * s ^ 2 * Q
  let h' : ℝ → ℝ := fun s => N1 S θ v s / Dn S θ v s - G - c * s * Q
  let h'' : ℝ → ℝ := fun s =>
    (N2 S θ v s * Dn S θ v s - N1 S θ v s * N1 S θ v s) / Dn S θ v s ^ 2 - c * Q
  have dh : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    have a := ((hasDerivAt_Dn S θ v s).log (Dn_pos S θ v s).ne')
    have b1 := ((hasDerivAt_id s).mul_const G)
    have b2 := (((hasDerivAt_id s).pow 2).const_mul (c / 2)).mul_const Q
    have := ((a.sub_const (Real.log (Dn S θ v 0))).sub b1).sub b2
    refine this.congr_deriv ?_
    simp only [h', id]; ring
  have dh' : ∀ s, HasDerivAt h' (h'' s) s := by
    intro s
    have a := (hasDerivAt_N1 S θ v s).div (hasDerivAt_Dn S θ v s) (Dn_pos S θ v s).ne'
    have b2 := ((hasDerivAt_id s).const_mul c).mul_const Q
    have := (a.sub_const G).sub b2
    refine this.congr_deriv ?_
    simp [h'']
  have hmono' : MonotoneOn h' (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun x _ => (dh' x).continuousAt.continuousWithinAt)
      (fun x _ => (dh' x).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have := hess_bound S θ v b x (line_bound S θ v b h0 h1 x ⟨hx.1.le, hx.2.le⟩)
    simp only [h'']; linarith
  have hd0 : h' 0 = 0 := by simp [h', hG]
  have hmono : MonotoneOn h (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun x _ => (dh x).continuousAt.continuousWithinAt)
      (fun x _ => (dh x).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [← hd0]
    exact hmono' ⟨le_refl 0, zero_le_one⟩ ⟨hx.1.le, hx.2.le⟩ hx.1.le
  have := hmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [h] at this
  simp at this
  linarith


open DynAssortPers.Regret MatrixCompletion

lemma list_le {ι : Type*} (O : List ι) (f g : ι → ℝ) (h : ∀ o ∈ O, f o ≤ g o) :
    (O.map f).sum ≤ (O.map g).sum := by
  induction O with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun o ho => h o (by simp [ho])))

lemma list_mul {ι : Type*} (O : List ι) (f : ι → ℝ) (c : ℝ) :
    (O.map (fun o => c * f o)).sum = c * (O.map f).sum := by
  induction O with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_sub {ι : Type*} (O : List ι) (f g : ι → ℝ) :
    (O.map (fun o => f o - g o)).sum = (O.map f).sum - (O.map g).sum := by
  induction O with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_fin {ι κ : Type*} (O : List ι) (s : Finset κ) (f : ι → κ → ℝ) :
    ∑ a ∈ s, (O.map (fun o => f o a)).sum = (O.map (fun o => ∑ a ∈ s, f o a)).sum := by
  induction O with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- the gradient term of one observation. -/
noncomputable def gterm {m n : ℕ} (Θ : RealMatrix m n) (o : Obs m n) (a : Fin m) (b : Fin n) : ℝ :=
  (if a = o.1 ∧ b ∈ o.2.2 then
        Real.exp (Θ o.1 b) / (1 + ∑ j ∈ o.2.2, Real.exp (Θ o.1 j)) else 0) -
      (if a = o.1 ∧ o.2.1 = some b then 1 else 0)

lemma inner_grad {m n : ℕ} (O : List (Obs m n)) (Θ Δ : RealMatrix m n) :
    matrixInner (lossGrad O Θ) Δ = (1 / (O.length : ℝ)) *
      (O.map (fun o => ∑ a : Fin m, ∑ b : Fin n, gterm Θ o a b * Δ a b)).sum := by
  unfold matrixInner lossGrad
  have e : ∀ a b, (1 / (O.length : ℝ)) * (O.map (fun o => gterm Θ o a b)).sum * Δ a b =
      (1 / (O.length : ℝ)) * (O.map (fun o => gterm Θ o a b * Δ a b)).sum := by
    intro a b
    have := list_mul O (fun o => gterm Θ o a b) (Δ a b)
    simp only [mul_comm (Δ a b)] at this
    rw [this]; ring
  simp only [gterm] at e
  simp only [e, ← Finset.mul_sum]
  congr 1
  rw [← list_fin]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← list_fin]
  rfl

lemma grad_obs {m n : ℕ} (Θ Δ : RealMatrix m n) (o : Obs m n) :
    ∑ a : Fin m, ∑ b : Fin n, gterm Θ o a b * Δ a b =
      ∑ b ∈ o.2.2, Real.exp (Θ o.1 b) / (1 + ∑ j ∈ o.2.2, Real.exp (Θ o.1 j)) * Δ o.1 b
        - chosenScore Δ o := by
  rw [Finset.sum_eq_single o.1]
  · unfold gterm
    simp only [true_and, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    congr 1
    unfold chosenScore
    rcases o with ⟨i, c, S⟩
    cases c with
    | none => simp
    | some j => simp [eq_comm]
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    simp [gterm, ha]
  · simp

lemma chosen_add {m n : ℕ} (Θ Δ : RealMatrix m n) (o : Obs m n) :
    chosenScore (Θ + Δ) o = chosenScore Θ o + chosenScore Δ o := by
  unfold chosenScore
  rcases o with ⟨i, c, S⟩
  cases c <;> simp

lemma obs_breg {m n : ℕ} (Θ Δ : RealMatrix m n) (o : Obs m n) :
    obsLoss (Θ + Δ) o - obsLoss Θ o - ∑ a : Fin m, ∑ b : Fin n, gterm Θ o a b * Δ a b =
      Real.log (Dn o.2.2 (Θ o.1) (Δ o.1) 1) - Real.log (Dn o.2.2 (Θ o.1) (Δ o.1) 0) -
        N1 o.2.2 (Θ o.1) (Δ o.1) 0 / Dn o.2.2 (Θ o.1) (Δ o.1) 0 := by
  rw [grad_obs]
  unfold obsLoss Dn N1
  rw [chosen_add]
  simp only [Matrix.add_apply, one_mul, zero_mul, add_zero, Finset.sum_div]
  have : ∀ b ∈ o.2.2, Real.exp (Θ o.1 b) / (1 + ∑ j ∈ o.2.2, Real.exp (Θ o.1 j)) * Δ o.1 b =
      Real.exp (Θ o.1 b) * Δ o.1 b / (1 + ∑ j ∈ o.2.2, Real.exp (Θ o.1 j)) := by
    intro b _; ring
  rw [Finset.sum_congr rfl this]
  ring

lemma breg_eq {m n : ℕ} (O : List (Obs m n)) (Θ Δ : RealMatrix m n) :
    bregman O Θ Δ = (1 / (O.length : ℝ)) * (O.map (fun o =>
      Real.log (Dn o.2.2 (Θ o.1) (Δ o.1) 1) - Real.log (Dn o.2.2 (Θ o.1) (Δ o.1) 0) -
        N1 o.2.2 (Θ o.1) (Δ o.1) 0 / Dn o.2.2 (Θ o.1) (Δ o.1) 0)).sum := by
  unfold bregman loss
  rw [inner_grad]
  have := List.map_congr_left (l := O) (fun o _ => obs_breg Θ Δ o)
  rw [← this, list_sub, list_sub]
  ring

lemma le_entrySup {m n : ℕ} (X : RealMatrix m n) (i : Fin m) (j : Fin n) :
    |X i j| ≤ entrySupNorm X := by
  unfold entrySupNorm
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j : Fin n, |X i j|) (Finite.bddAbove_range _) i)
  exact le_ciSup (f := fun j => |X i j|) (Finite.bddAbove_range _) j

lemma const_le (K k : ℕ) (hk : 1 ≤ k) (hK : k ≤ K) (b : ℝ) (hb : 0 ≤ b) :
    (1 / 2) * (1 / Real.exp (4 * (2 * b))) * (1 / (4 * (K : ℝ))) * (1 / (k : ℝ)) ≤
      (1 / 2) * (Real.exp (-b) / (1 + k * Real.exp b) ^ 2) := by
  set E := Real.exp b with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hb
  have h8 : Real.exp (4 * (2 * b)) = E ^ 8 := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hm : Real.exp (-b) = 1 / E := by rw [Real.exp_neg, hE, one_div]
  rw [h8, hm]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK' : (k : ℝ) ≤ K := by exact_mod_cast hK
  have hE0 : 0 < E := by positivity
  have hkE : 1 ≤ (k : ℝ) * E := by nlinarith
  have h3 : E ^ 3 ≤ E ^ 8 := pow_le_pow_right₀ hE1 (by norm_num)
  have key : E * (1 + k * E) ^ 2 ≤ E ^ 8 * (4 * K) * k := by
    have a1 : (1 + k * E) ^ 2 ≤ (2 * k * E) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    have a2 : E * (2 * k * E) ^ 2 = 4 * (k : ℝ) ^ 2 * E ^ 3 := by ring
    have a3 : 4 * (k : ℝ) ^ 2 * E ^ 3 ≤ E ^ 8 * (4 * K) * k := by
      have : (k : ℝ) ^ 2 ≤ K * k := by nlinarith
      have hE3 : 0 ≤ E ^ 3 := by positivity
      nlinarith [mul_le_mul this h3 hE3 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left a1 hE0.le]
  have lhs : (1 / 2) * (1 / E ^ 8) * (1 / (4 * (K : ℝ))) * (1 / (k : ℝ)) =
      (1 / 2) * (1 / (E ^ 8 * (4 * K) * k)) := by field_simp
  have rhs : (1 / 2) * (1 / E / (1 + k * E) ^ 2) = (1 / 2) * (1 / (E * (1 + k * E) ^ 2)) := by
    field_simp
  rw [lhs, rhs]
  have : 1 / (E ^ 8 * (4 * K) * k) ≤ 1 / (E * (1 + k * E) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) key
  linarith

lemma obs_bound {m n : ℕ} (K : ℕ) (Θ Δ : RealMatrix m n) (o : Obs m n) (hK : o.2.2.card ≤ K)
    (b : ℝ) (h0 : ∀ j, |Θ o.1 j| ≤ b) (h1 : ∀ j, |Θ o.1 j + Δ o.1 j| ≤ b) :
    (1 / 2) * (1 / Real.exp (4 * (2 * b))) * (1 / (4 * (K : ℝ))) *
        ((1 / (o.2.2.card : ℝ)) * ∑ j ∈ o.2.2, (Δ o.1 j) ^ 2) ≤
      Real.log (Dn o.2.2 (Θ o.1) (Δ o.1) 1) - Real.log (Dn o.2.2 (Θ o.1) (Δ o.1) 0) -
        N1 o.2.2 (Θ o.1) (Δ o.1) 0 / Dn o.2.2 (Θ o.1) (Δ o.1) 0 := by
  have hl := breg_line o.2.2 (Θ o.1) (Δ o.1) b (fun j _ => h0 j) (fun j _ => h1 j)
  have hQ : 0 ≤ ∑ j ∈ o.2.2, (Δ o.1 j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine le_trans ?_ hl
  rcases Nat.eq_zero_or_pos o.2.2.card with h | h
  · rw [h]; simp
    have := Finset.card_eq_zero.1 h
    rw [this]; simp
  · obtain ⟨j, hj⟩ := Finset.card_pos.1 h
    have hb : 0 ≤ b := (abs_nonneg _).trans (h0 j)
    have := const_le K o.2.2.card h hK b hb
    calc (1 / 2) * (1 / Real.exp (4 * (2 * b))) * (1 / (4 * (K : ℝ))) *
        ((1 / (o.2.2.card : ℝ)) * ∑ j ∈ o.2.2, (Δ o.1 j) ^ 2)
        = ((1 / 2) * (1 / Real.exp (4 * (2 * b))) * (1 / (4 * (K : ℝ))) *
            (1 / (o.2.2.card : ℝ))) * ∑ j ∈ o.2.2, (Δ o.1 j) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hQ

theorem l2 {m n : ℕ} (K : ℕ) (O : List (Obs m n)) (hK : ∀ o ∈ O, o.2.2.card ≤ K)
    (α : ℝ) (Θs Δ : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘΔ : entrySupNorm (Θs + Δ) ≤ α / Real.sqrt ((m : ℝ) * n)) :
    (1 / 2) * (1 / Real.exp (4 * (2 * α / Real.sqrt ((m : ℝ) * n)))) * (1 / (4 * (K : ℝ))) *
        lquad O Δ ≤ bregman O Θs Δ := by
  set b := α / Real.sqrt ((m : ℝ) * n) with hb
  have hγ : 2 * α / Real.sqrt ((m : ℝ) * n) = 2 * b := by rw [hb]; ring
  rw [hγ, breg_eq]
  unfold lquad
  set c := (1 / 2) * (1 / Real.exp (4 * (2 * b))) * (1 / (4 * (K : ℝ)))
  have hN : 0 ≤ 1 / (O.length : ℝ) := by positivity
  rw [← mul_assoc, mul_comm c, mul_assoc, ← list_mul]
  refine mul_le_mul_of_nonneg_left (list_le O _ _ (fun o ho => ?_)) hN
  refine obs_bound K Θs Δ o (hK o ho) b (fun j => (le_entrySup Θs o.1 j).trans hΘs) (fun j => ?_)
  have := (le_entrySup (Θs + Δ) o.1 j).trans hΘΔ
  simpa [Matrix.add_apply] using this

end DAPl2

open MatrixCompletion in
theorem solution {m n : ℕ} (K : ℕ) (O : List (DynAssortPers.Regret.Obs m n))
    (hK : ∀ o ∈ O, o.2.2.card ≤ K)
    (α : ℝ) (Θs Δ : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘΔ : entrySupNorm (Θs + Δ) ≤ α / Real.sqrt ((m : ℝ) * n)) :
    (1 / 2) * (1 / Real.exp (4 * (2 * α / Real.sqrt ((m : ℝ) * n)))) * (1 / (4 * (K : ℝ))) *
        DynAssortPers.Regret.lquad O Δ ≤ DynAssortPers.Regret.bregman O Θs Δ :=
  DAPl2.l2 K O hK α Θs Δ hΘs hΘΔ
