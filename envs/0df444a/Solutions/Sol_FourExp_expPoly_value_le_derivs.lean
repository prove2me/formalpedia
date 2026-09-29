-- Prove2me | solution 1 for FourExp.expPoly_value_le_derivs
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T09:05:05.672265+00:00
-- url     : https://prove2.me/submissions/0a598397-2278-47b9-9478-a0794a098725

import Mathlib

open Finset

namespace FourExpDerivs

open Polynomial

variable {l : ℕ}

/-- The exponential polynomial `z ↦ ∑ⱼ Pⱼ(z) e^{wⱼ z}`. -/
noncomputable def expPoly (w : Fin l → ℂ) (P : Fin l → ℂ[X]) : ℂ → ℂ :=
  fun z => ∑ j, (P j).eval z * Complex.exp (w j * z)

/-- The polynomials of `f' - μ f`. -/
noncomputable def peelP (w : Fin l → ℂ) (P : Fin l → ℂ[X]) (μ : ℂ) : Fin l → ℂ[X] :=
  fun j => derivative (P j) + C (w j - μ) * P j

/-- `C(n, m) · W^(n - m)`. -/
noncomputable def cf (W : ℝ) (n m : ℕ) : ℝ := (n.choose m : ℝ) * W ^ (n - m)

lemma hasDerivAt_finsum {ι : Type*} (s : Finset ι) (g g' : ι → ℂ → ℂ) (z : ℂ)
    (h : ∀ i, HasDerivAt (g i) (g' i z) z) :
    HasDerivAt (fun y => ∑ i ∈ s, g i y) (∑ i ∈ s, g' i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const z (0 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

lemma hasDerivAt_term (p : ℂ[X]) (v z : ℂ) :
    HasDerivAt (fun y => p.eval y * Complex.exp (v * y))
      ((p.derivative.eval z + p.eval z * v) * Complex.exp (v * z)) z := by
  have h1 := p.hasDerivAt z
  have h2 : HasDerivAt (fun y => Complex.exp (v * y)) (Complex.exp (v * z) * v) z := by
    simpa using ((hasDerivAt_id z).const_mul v).cexp
  exact (h1.mul h2).congr_deriv (by ring)

lemma hasDerivAt_expPoly (w : Fin l → ℂ) (P : Fin l → ℂ[X]) (z : ℂ) :
    HasDerivAt (expPoly w P)
      (∑ j, ((P j).derivative.eval z + (P j).eval z * w j) * Complex.exp (w j * z)) z :=
  hasDerivAt_finsum Finset.univ (fun j y => (P j).eval y * Complex.exp (w j * y))
    (fun j y => ((P j).derivative.eval y + (P j).eval y * w j) * Complex.exp (w j * y)) z
    (fun j => hasDerivAt_term (P j) (w j) z)

lemma differentiable_expPoly (w : Fin l → ℂ) (P : Fin l → ℂ[X]) :
    Differentiable ℂ (expPoly w P) :=
  fun z => (hasDerivAt_expPoly w P z).differentiableAt

lemma deriv_expPoly (w : Fin l → ℂ) (P : Fin l → ℂ[X]) (μ : ℂ) :
    deriv (expPoly w P) = expPoly w (peelP w P μ) + fun z => μ * expPoly w P z := by
  funext z
  rw [(hasDerivAt_expPoly w P z).deriv]
  simp only [expPoly, peelP, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [eval_add, eval_mul, eval_C]
  ring

lemma iter_succ (w : Fin l → ℂ) (P : Fin l → ℂ[X]) (μ : ℂ) (n : ℕ) :
    iteratedDeriv (n + 1) (expPoly w P) 0
      = iteratedDeriv n (expPoly w (peelP w P μ)) 0 + μ * iteratedDeriv n (expPoly w P) 0 := by
  rw [iteratedDeriv_succ', deriv_expPoly w P μ,
    iteratedDeriv_add (differentiable_expPoly w _).contDiff.contDiffAt
      ((differentiable_expPoly w P).const_mul μ).contDiff.contDiffAt,
    iteratedDeriv_const_mul μ (differentiable_expPoly w P).contDiff.contDiffAt]

lemma expPoly_zero_of (w : Fin l → ℂ) (P : Fin l → ℂ[X]) (h : ∀ j, P j = 0) :
    expPoly w P = fun _ => 0 := by
  funext z
  simp [expPoly, h]

lemma iteratedDeriv_zero_const (n : ℕ) : iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ']; simpa using ih

lemma cf_succ_zero (W : ℝ) (n : ℕ) : cf W (n + 1) 0 = W * cf W n 0 := by
  simp only [cf, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, pow_succ]
  ring

lemma cf_succ_succ (W : ℝ) (n m : ℕ) : cf W (n + 1) (m + 1) = cf W n m + W * cf W n (m + 1) := by
  unfold cf
  have e1 : n + 1 - (m + 1) = n - m := by omega
  rcases le_or_gt (m + 1) n with h | h
  · have e2 : n - m = (n - (m + 1)) + 1 := by omega
    rw [Nat.choose_succ_succ, e1, e2, pow_succ]
    push_cast
    ring
  · rw [Nat.choose_succ_succ, e1, Nat.choose_eq_zero_of_lt h]
    push_cast
    ring

lemma cf_split (W : ℝ) (N n : ℕ) :
    ∑ m ∈ range (N + 1), (W + 1) ^ m * cf W (n + 1) m
      = (W + 1) * ∑ m ∈ range N, (W + 1) ^ m * cf W n m
        + W * ∑ m ∈ range (N + 1), (W + 1) ^ m * cf W n m := by
  have h1 : ∑ m ∈ range (N + 1), (W + 1) ^ m * cf W (n + 1) m
      = ∑ m ∈ range N, (W + 1) ^ (m + 1) * cf W (n + 1) (m + 1) + (W + 1) ^ 0 * cf W (n + 1) 0 :=
    Finset.sum_range_succ' (fun m => (W + 1) ^ m * cf W (n + 1) m) N
  have h2 : ∑ m ∈ range (N + 1), (W + 1) ^ m * cf W n m
      = ∑ m ∈ range N, (W + 1) ^ (m + 1) * cf W n (m + 1) + (W + 1) ^ 0 * cf W n 0 :=
    Finset.sum_range_succ' (fun m => (W + 1) ^ m * cf W n m) N
  have h3 : ∑ m ∈ range N, (W + 1) ^ (m + 1) * cf W (n + 1) (m + 1)
      = (W + 1) * ∑ m ∈ range N, (W + 1) ^ m * cf W n m
        + W * ∑ m ∈ range N, (W + 1) ^ (m + 1) * cf W n (m + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [cf_succ_succ]
    ring
  rw [h1, h2, h3, cf_succ_zero]
  ring

/-- The coefficient bound: peel one frequency at a time. -/
lemma coeff_bound (w : Fin l → ℂ) (W : ℝ) (hW0 : 0 ≤ W) (hW : ∀ j, ‖w j‖ ≤ W) :
    ∀ (N : ℕ) (q : Fin l → ℕ) (P : Fin l → ℂ[X]), (∀ j, P j = 0 ∨ (P j).natDegree < q j) →
      ∑ j, q j = N → ∀ D : ℝ, (∀ s < N, ‖iteratedDeriv s (expPoly w P) 0‖ ≤ D) →
      ∀ n, ‖iteratedDeriv n (expPoly w P) 0‖ ≤ D * ∑ m ∈ range N, (W + 1) ^ m * cf W n m := by
  intro N
  induction N with
  | zero =>
    intro q P hP hsum D _ n
    have hP0 : ∀ j, P j = 0 := fun j => (hP j).resolve_right (by
      rw [Finset.sum_eq_zero_iff.1 hsum j (Finset.mem_univ j)]
      exact Nat.not_lt_zero _)
    rw [expPoly_zero_of w P hP0, iteratedDeriv_zero_const]
    simp
  | succ N ih =>
    intro q P hP hsum D hD n
    obtain ⟨j0, hj0⟩ : ∃ j0, 1 ≤ q j0 := by
      by_contra hc
      push_neg at hc
      have : ∑ j, q j = 0 := Finset.sum_eq_zero fun j _ => by have := hc j; omega
      omega
    have hP' : ∀ j, peelP w P (w j0) j = 0 ∨
        (peelP w P (w j0) j).natDegree < Function.update q j0 (q j0 - 1) j := by
      intro j
      by_cases hj : j = j0
      · subst hj
        simp only [peelP, sub_self, map_zero, zero_mul, add_zero, Function.update_self]
        rcases hP j with h | h
        · left
          simp [h]
        · by_cases hd : (P j).natDegree = 0
          · left
            exact derivative_of_natDegree_zero hd
          · right
            have := natDegree_derivative_le (P j)
            omega
      · simp only [peelP, Function.update_of_ne hj]
        rcases hP j with h | h
        · left
          simp [h]
        · right
          calc (derivative (P j) + C (w j - w j0) * P j).natDegree
              ≤ max (derivative (P j)).natDegree (C (w j - w j0) * P j).natDegree :=
                natDegree_add_le _ _
            _ ≤ (P j).natDegree :=
                max_le ((natDegree_derivative_le _).trans (Nat.sub_le _ _)) (natDegree_C_mul_le _ _)
            _ < q j := h
    have hsum' : ∑ j, Function.update q j0 (q j0 - 1) j = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ j0), Finset.sdiff_singleton_eq_erase]
      have h2 := Finset.add_sum_erase Finset.univ q (Finset.mem_univ j0)
      omega
    have hDG : ∀ s < N, ‖iteratedDeriv s (expPoly w (peelP w P (w j0))) 0‖ ≤ D * (W + 1) := by
      intro s hs
      have h1 := hD (s + 1) (by omega)
      have h2 := hD s (by omega)
      have e : iteratedDeriv s (expPoly w (peelP w P (w j0))) 0
          = iteratedDeriv (s + 1) (expPoly w P) 0 - w j0 * iteratedDeriv s (expPoly w P) 0 := by
        rw [iter_succ w P (w j0) s]
        ring
      rw [e]
      calc _ ≤ ‖iteratedDeriv (s + 1) (expPoly w P) 0‖ + ‖w j0 * iteratedDeriv s (expPoly w P) 0‖ :=
            norm_sub_le _ _
        _ ≤ D + W * D := by
            rw [norm_mul]
            exact add_le_add h1 (mul_le_mul (hW j0) h2 (norm_nonneg _) hW0)
        _ = D * (W + 1) := by ring
    have ih' := ih (Function.update q j0 (q j0 - 1)) (peelP w P (w j0)) hP' hsum' (D * (W + 1)) hDG
    induction n with
    | zero =>
      have h0 := hD 0 (by omega)
      have hs : ∑ m ∈ range (N + 1), (W + 1) ^ m * cf W 0 m = 1 := by
        rw [Finset.sum_range_succ']
        simp [cf]
      rw [hs, mul_one]
      exact h0
    | succ n ihn =>
      rw [iter_succ w P (w j0) n]
      calc _ ≤ ‖iteratedDeriv n (expPoly w (peelP w P (w j0))) 0‖
              + ‖w j0 * iteratedDeriv n (expPoly w P) 0‖ := norm_add_le _ _
        _ ≤ D * (W + 1) * ∑ m ∈ range N, (W + 1) ^ m * cf W n m
              + W * (D * ∑ m ∈ range (N + 1), (W + 1) ^ m * cf W n m) := by
            rw [norm_mul]
            exact add_le_add (ih' n) (mul_le_mul (hW j0) ihn (norm_nonneg _) hW0)
        _ = D * ∑ m ∈ range (N + 1), (W + 1) ^ m * cf W (n + 1) m := by
            rw [cf_split]
            ring

/-- `∑_{n<K} C(n,m) W^(n-m) Rⁿ/n! ≤ R^m/m! · e^{WR}`. -/
lemma inner_le (W R : ℝ) (hW0 : 0 ≤ W) (hR : 0 ≤ R) (K m : ℕ) :
    ∑ n ∈ range K, cf W n m * R ^ n / (n.factorial : ℝ)
      ≤ R ^ m / (m.factorial : ℝ) * Real.exp (W * R) := by
  have hnn : ∀ n, 0 ≤ cf W n m * R ^ n / (n.factorial : ℝ) := fun n =>
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hW0 _)) (pow_nonneg hR _))
      (Nat.cast_nonneg _)
  calc ∑ n ∈ range K, cf W n m * R ^ n / (n.factorial : ℝ)
      ≤ ∑ n ∈ range (m + K), cf W n m * R ^ n / (n.factorial : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun n _ _ => hnn n)
    _ = ∑ k ∈ range K, R ^ m / (m.factorial : ℝ) * ((W * R) ^ k / (k.factorial : ℝ)) := by
        rw [Finset.sum_range_add]
        have hzero : ∑ n ∈ range m, cf W n m * R ^ n / (n.factorial : ℝ) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            simp [cf, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hn)]
        rw [hzero, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hc := Nat.add_choose_mul_factorial_mul_factorial k m
        rw [add_comm k m] at hc
        have hc' : ((m + k).choose m : ℝ) * (k.factorial : ℝ) * (m.factorial : ℝ)
            = ((m + k).factorial : ℝ) := by
          exact_mod_cast hc
        have hk : (k.factorial : ℝ) ≠ 0 := by positivity
        have hm : (m.factorial : ℝ) ≠ 0 := by positivity
        have hC : ((m + k).choose m : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (by omega)).ne'
        unfold cf
        rw [Nat.add_sub_cancel_left, ← hc']
        field_simp
        ring
    _ = R ^ m / (m.factorial : ℝ) * ∑ k ∈ range K, (W * R) ^ k / (k.factorial : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ R ^ m / (m.factorial : ℝ) * Real.exp (W * R) :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (mul_nonneg hW0 hR) K)
          (div_nonneg (pow_nonneg hR _) (Nat.cast_nonneg _))

end FourExpDerivs

theorem solution
    {l : ℕ} (q : Fin l → ℕ) (w : Fin l → ℂ) (hw : Function.Injective w)
    (P : Fin l → Polynomial ℂ) (hP : ∀ j, P j = 0 ∨ (P j).natDegree < q j)
    (W R D : ℝ) (hW0 : 0 ≤ W) (hW : ∀ j, ‖w j‖ ≤ W) (hR : 0 ≤ R)
    (hD : ∀ s : ℕ, s < ∑ j, q j →
      ‖iteratedDeriv s (fun z : ℂ => ∑ j, (P j).eval z * Complex.exp (w j * z)) 0‖ ≤ D)
    (u : ℂ) (hu : ‖u‖ ≤ R) :
    ‖∑ j, (P j).eval u * Complex.exp (w j * u)‖
      ≤ ((∑ j, q j : ℕ) : ℝ) * (W + 1) ^ ((∑ j, q j) + 1) * Real.exp (R * (W + 1)) * D := by
  set N := ∑ j, q j with hN
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hs0 : ∑ j, q j = 0 := by rw [← hN]; exact hN0
    have hP0 : ∀ j, P j = 0 := fun j => (hP j).resolve_right (by
      rw [Finset.sum_eq_zero_iff.1 hs0 j (Finset.mem_univ j)]
      exact Nat.not_lt_zero _)
    simp [hP0, hN0]
  have hdiff := FourExpDerivs.differentiable_expPoly w P
  have hcoeff := FourExpDerivs.coeff_bound w W hW0 hW N q P hP hN.symm D hD
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 hNpos)
  have hT := Complex.hasSum_taylorSeries_of_entire (c := 0) (z := u) hdiff
  have hK : ∀ K : ℕ, ‖∑ n ∈ range K,
      ((n.factorial : ℂ)⁻¹ • (u - 0) ^ n • iteratedDeriv n (FourExpDerivs.expPoly w P) 0)‖
      ≤ D * ∑ m ∈ range N, (W + 1) ^ m * (R ^ m / (m.factorial : ℝ) * Real.exp (W * R)) := by
    intro K
    calc _ ≤ ∑ n ∈ range K,
          ‖(n.factorial : ℂ)⁻¹ • (u - 0) ^ n • iteratedDeriv n (FourExpDerivs.expPoly w P) 0‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ range K, (n.factorial : ℝ)⁻¹ * R ^ n
            * (D * ∑ m ∈ range N, (W + 1) ^ m * FourExpDerivs.cf W n m) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [sub_zero, norm_smul, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
          have hun : ‖u‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) hu n
          have hfi : 0 ≤ (n.factorial : ℝ)⁻¹ := by positivity
          calc (n.factorial : ℝ)⁻¹ * (‖u‖ ^ n * ‖iteratedDeriv n (FourExpDerivs.expPoly w P) 0‖)
              ≤ (n.factorial : ℝ)⁻¹
                  * (R ^ n * (D * ∑ m ∈ range N, (W + 1) ^ m * FourExpDerivs.cf W n m)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hun (hcoeff n) (norm_nonneg _) (pow_nonneg hR _)) hfi
            _ = _ := by ring
      _ = D * ∑ m ∈ range N, (W + 1) ^ m
            * ∑ n ∈ range K, FourExpDerivs.cf W n m * R ^ n / (n.factorial : ℝ) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
          ring
      _ ≤ _ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
            mul_le_mul_of_nonneg_left (FourExpDerivs.inner_le W R hW0 hR K m)
              (pow_nonneg (by linarith) _)) hD0
  have hle : ‖FourExpDerivs.expPoly w P u‖
      ≤ D * ∑ m ∈ range N, (W + 1) ^ m * (R ^ m / (m.factorial : ℝ) * Real.exp (W * R)) :=
    le_of_tendsto' hT.tendsto_sum_nat.norm hK
  have hsum1 : ∑ m ∈ range N, (W + 1) ^ m * (R ^ m / (m.factorial : ℝ) * Real.exp (W * R))
      ≤ (W + 1) ^ (N - 1) * Real.exp (W * R) * Real.exp R := by
    calc ∑ m ∈ range N, (W + 1) ^ m * (R ^ m / (m.factorial : ℝ) * Real.exp (W * R))
        ≤ ∑ m ∈ range N, (W + 1) ^ (N - 1) * Real.exp (W * R) * (R ^ m / (m.factorial : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmN := Finset.mem_range.1 hm
          have hpw : (W + 1) ^ m ≤ (W + 1) ^ (N - 1) := pow_le_pow_right₀ (by linarith) (by omega)
          have h0 : 0 ≤ R ^ m / (m.factorial : ℝ) * Real.exp (W * R) :=
            mul_nonneg (div_nonneg (pow_nonneg hR m) (Nat.cast_nonneg _)) (Real.exp_pos _).le
          calc (W + 1) ^ m * (R ^ m / (m.factorial : ℝ) * Real.exp (W * R))
              ≤ (W + 1) ^ (N - 1) * (R ^ m / (m.factorial : ℝ) * Real.exp (W * R)) :=
                mul_le_mul_of_nonneg_right hpw h0
            _ = _ := by ring
      _ = (W + 1) ^ (N - 1) * Real.exp (W * R) * ∑ m ∈ range N, R ^ m / (m.factorial : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (W + 1) ^ (N - 1) * Real.exp (W * R) * Real.exp R :=
          mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hR N)
            (mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le)
  have hpow : (W + 1) ^ (N - 1) ≤ (N : ℝ) * (W + 1) ^ (N + 1) := by
    calc (W + 1) ^ (N - 1) ≤ (W + 1) ^ (N + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      _ ≤ (N : ℝ) * (W + 1) ^ (N + 1) :=
          le_mul_of_one_le_left (pow_nonneg (by linarith) _) (Nat.one_le_cast.mpr hNpos)
  have hexp : Real.exp (W * R) * Real.exp R = Real.exp (R * (W + 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  show ‖FourExpDerivs.expPoly w P u‖ ≤ (N : ℝ) * (W + 1) ^ (N + 1) * Real.exp (R * (W + 1)) * D
  calc ‖FourExpDerivs.expPoly w P u‖
      ≤ D * ((W + 1) ^ (N - 1) * Real.exp (W * R) * Real.exp R) :=
        hle.trans (mul_le_mul_of_nonneg_left hsum1 hD0)
    _ ≤ D * ((N : ℝ) * (W + 1) ^ (N + 1) * Real.exp (R * (W + 1))) := by
        rw [mul_assoc ((W + 1) ^ (N - 1)), hexp]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) hD0
    _ = _ := by ring
