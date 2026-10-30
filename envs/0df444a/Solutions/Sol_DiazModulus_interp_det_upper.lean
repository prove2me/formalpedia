-- Prove2me | solution 1 for DiazModulus.interp_det_upper
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:18:01.221998+00:00
-- url     : https://prove2.me/submissions/a9c30e45-0000-4e01-9f33-3a94995926b8

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_interpolation_det_order
import Theorems.Thm_DiazModulus_schwarz_order_at_zero
import Theorems.Thm_DiazModulus_iteratedFDeriv_expMono_eq_op
import Theorems.Thm_DiazModulus_op_monomial_eval_norm_le

open Complex ComplexConjugate

/-! # Upper bound for the interpolation determinant (Step 4 of the C1.4 route)

Let `n = dim V`, fix a basis of `V` and let `ψ : ℂⁿ →L V ⊆ ℂ^{ι₀} × ℂ^{ι₁}` be the coordinate map.
Each column `l'` gives the entire function `f_{l'} ∘ ψ`, with `f_{l'}(z) = z.1^τ · exp⟨t, z.2⟩`; each row
`l` gives the point `ζ_l = ψ⁻¹(Σ_j s_j η_j)` and the directions `ψ⁻¹(w_{k})`. By
`ContinuousLinearMap.iteratedFDeriv_comp_right` and `iteratedFDeriv_expMono_eq_op` (A6) the entries of
`F(z) = det(D^{σ}(f ∘ ψ)(z ζ)(v))` are `(Op⋯Op X^τ)(z p.1) · exp(z ⟨t, p.2⟩)`, so `F(1) = Δ` (up to a
transpose and a reindexing by `Fin L`). `interpolation_det_order` (A4) gives `ord₀ F ≥ Θₙ(L) − Σσ ≥
Θₙ(L) − L·N₀`, and `schwarz_order_at_zero` (A5) with `R = e` gives `|Δ| ≤ e^{−ord}·sup_{|z|=e}|F|`.
On `|z| = e` each entry is at most `exp β`, by `op_monomial_eval_norm_le` (A7) for the polynomial
part and `|exp u| ≤ exp |u|` for the exponential, and the Leibniz expansion gives `|F| ≤ L!·exp(β)^L`.
Finally `log L + β ≤ K·Ξ` is elementary (`log x ≤ x − 1`, `log(T₀+T₁+2) ≥ 1`, `log(N₁+2) ≥ 1/2`). -/

namespace C14_upper
open DiazModulus

/-- The polynomial `Op_{w_{k 0}} ⋯ Op_{w_{k (r-1)}} X^τ`. -/
noncomputable def opPoly {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (r : ℕ) (k : Fin r → κ₀) (t : ι₁ → ℂ) (τ : ι₀ → ℕ) :
    MvPolynomial ι₀ ℂ :=
  (List.ofFn fun k' : Fin r =>
    ((∑ h, (w (k k')).1 h • (MvPolynomial.pderiv h).toLinearMap
      + (∑ i, (w (k k')).2 i * t i) • LinearMap.id : Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
    (∏ h, MvPolynomial.X h ^ τ h)

/-- The exponential monomial `z.1^τ · exp⟨t, z.2⟩`. -/
noncomputable def expMono {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] (τ : ι₀ → ℕ) (t : ι₁ → ℤ) :
    (ι₀ → ℂ) × (ι₁ → ℂ) → ℂ :=
  fun z => (∏ h, z.1 h ^ τ h) * Complex.exp (∑ i, (t i : ℂ) * z.2 i)

lemma expMono_analytic {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] (τ : ι₀ → ℕ) (t : ι₁ → ℤ) :
    AnalyticOnNhd ℂ (expMono τ t) Set.univ := by
  intro z _
  have h1 : ∀ h, AnalyticAt ℂ (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) => z.1 h) z := fun h =>
    ((ContinuousLinearMap.proj h).comp (ContinuousLinearMap.fst ℂ _ _)).analyticAt z
  have h2 : ∀ i, AnalyticAt ℂ (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) => z.2 i) z := fun i =>
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ _ _)).analyticAt z
  unfold expMono
  fun_prop

lemma comp_analytic {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] {n : ℕ} (τ : ι₀ → ℕ) (t : ι₁ → ℤ)
    (ψ : (Fin n → ℂ) →L[ℂ] (ι₀ → ℂ) × (ι₁ → ℂ)) :
    AnalyticOnNhd ℂ (expMono τ t ∘ ψ) Set.univ :=
  fun y _ => (expMono_analytic τ t (ψ y) trivial).comp (ψ.analyticAt y)

/-- The entries after restriction to `V`. -/
lemma entry_eq {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀] {n : ℕ}
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (τ : ι₀ → ℕ) (t : ι₁ → ℤ) (tc : ι₁ → ℂ)
    (htc : ∀ i, ((t i : ℤ) : ℂ) = tc i)
    (ψ : (Fin n → ℂ) →L[ℂ] (ι₀ → ℂ) × (ι₁ → ℂ)) (y : Fin n → ℂ) (r : ℕ) (κ : Fin r → κ₀)
    (v : Fin r → Fin n → ℂ) (hv : ∀ k, ψ (v k) = w (κ k)) :
    iteratedFDeriv ℂ r (expMono τ t ∘ ψ) y v =
      MvPolynomial.eval (ψ y).1 (opPoly w r κ tc τ) * Complex.exp (∑ i, (t i : ℂ) * (ψ y).2 i) := by
  rw [ψ.iteratedFDeriv_comp_right ((expMono_analytic τ t).contDiff (n := ⊤)) y le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv' : (fun k => ψ (v k)) = fun k => w (κ k) := funext hv
  rw [hv']
  have htc' : tc = fun i => ((t i : ℤ) : ℂ) := funext fun i => (htc i).symm
  rw [htc']
  exact iteratedFDeriv_expMono_eq_op w τ t (ψ y) r κ

lemma differentiable_det {m : Type} [Fintype m] [DecidableEq m] (A : ℂ → Matrix m m ℂ)
    (h : ∀ i j, Differentiable ℂ fun z => A z i j) : Differentiable ℂ fun z => (A z).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply Differentiable.fun_sum
  intro σ _
  exact (differentiable_const _).mul (Differentiable.fun_finsetProd fun i _ => h _ _)

lemma norm_det_le {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (x : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ x) : ‖A.det‖ ≤ (Fintype.card m).factorial * x ^ Fintype.card m := by
  have := Matrix.det_le (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) h
  simpa [nsmul_eq_mul] using this

lemma exp_prod_eq {κ₁ ι₁ : Type} [Fintype κ₁] [Fintype ι₁] (x : κ₁ → ι₁ → ℂ) (s : κ₁ → ℤ)
    (t : ι₁ → ℤ) :
    ∏ i, (∏ j, Complex.exp (x j i) ^ s j) ^ t i =
      Complex.exp (∑ i, (t i : ℂ) * ∑ j, (s j : ℂ) * x j i) := by
  simp_rw [← Complex.exp_int_mul, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Complex.exp_sum]

/-- `log L + β ≤ K·Ξ`. -/
lemma xi_bound (H E : ℝ) (hH : 1 ≤ H) (hE : 1 ≤ E) (d₀ d₁ : ℕ) : ∃ K : ℝ, 0 < K ∧
    ∀ T₀ T₁ N₀ N₁ : ℕ, 1 ≤ T₀ → 1 ≤ T₁ →
    Real.log (((T₀ + 1) ^ d₀ * (2 * T₁ + 1) ^ d₁ : ℕ) : ℝ)
      + ((N₀ : ℝ) * Real.log (H * (d₀ * T₀ + d₁ * T₁ + 1))
        + ((d₀ : ℝ) * T₀) * Real.log (3 * E * (N₁ + 1)) + 3 * E * T₁ * N₁)
    ≤ K * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1)) := by
  have hd₀ : (0 : ℝ) ≤ d₀ := d₀.cast_nonneg
  have hd₁ : (0 : ℝ) ≤ d₁ := d₁.cast_nonneg
  set a1 := Real.log (H * (d₀ + d₁ + 1)) with ha1
  set a2 := Real.log (3 * E) with ha2
  have ha1n : 0 ≤ a1 := Real.log_nonneg (by nlinarith)
  have ha2n : 0 ≤ a2 := Real.log_nonneg (by nlinarith)
  have hk0 : 0 ≤ (d₀ : ℝ) * (2 * a2 + 3) := mul_nonneg hd₀ (by linarith)
  refine ⟨a1 + 1 + d₀ * (2 * a2 + 3) + 2 * d₁ + 3 * E, by linarith, ?_⟩
  intro T₀ T₁ N₀ N₁ hT₀ hT₁
  have hT₀' : (1 : ℝ) ≤ T₀ := by exact_mod_cast hT₀
  have hT₁' : (1 : ℝ) ≤ T₁ := by exact_mod_cast hT₁
  have hN₀ : (0 : ℝ) ≤ N₀ := N₀.cast_nonneg
  have hN₁ : (0 : ℝ) ≤ N₁ := N₁.cast_nonneg
  set lam := Real.log ((T₀ : ℝ) + T₁ + 2)
  set mu := Real.log ((N₁ : ℝ) + 2)
  have hlam : 1 ≤ lam := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hmu : 1 / 2 ≤ mu := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ mu := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlogL : Real.log (((T₀ + 1) ^ d₀ * (2 * T₁ + 1) ^ d₁ : ℕ) : ℝ) ≤ d₀ * T₀ + d₁ * (2 * T₁) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have e1 : Real.log ((T₀ : ℝ) + 1) ≤ T₀ := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T₀ + 1); linarith
    have e2 : Real.log (2 * (T₁ : ℝ) + 1) ≤ 2 * T₁ := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * T₁ + 1); linarith
    have := mul_le_mul_of_nonneg_left e1 hd₀
    have := mul_le_mul_of_nonneg_left e2 hd₁
    linarith
  have hX : Real.log (H * (d₀ * T₀ + d₁ * T₁ + 1)) ≤ (a1 + 1) * lam := by
    have h1 : H * (d₀ * T₀ + d₁ * T₁ + 1) ≤ H * (d₀ + d₁ + 1) * (T₀ + T₁ + 2) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have := mul_nonneg hd₀ (by linarith : (0 : ℝ) ≤ T₁ + 2)
      have := mul_nonneg hd₁ (by linarith : (0 : ℝ) ≤ T₀ + 2)
      nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    have e : Real.log (H * (d₀ + d₁ + 1) * (T₀ + T₁ + 2)) = a1 + lam :=
      Real.log_mul (by positivity) (by positivity)
    have := le_mul_of_one_le_right ha1n hlam
    linarith
  have hP : Real.log (3 * E * (N₁ + 1)) ≤ (2 * a2 + 1) * mu := by
    have h2 := Real.log_le_log (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith : (N₁ : ℝ) + 1 ≤ N₁ + 2) (by positivity : (0:ℝ) ≤ 3 * E))
    have e : Real.log (3 * E * ((N₁ : ℝ) + 2)) = a2 + mu :=
      Real.log_mul (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left hmu ha2n
    linarith
  have f1 : (N₀ : ℝ) * Real.log (H * (d₀ * T₀ + d₁ * T₁ + 1)) ≤ (a1 + 1) * (N₀ * lam) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hN₀]
  have f2 : ((d₀ : ℝ) * T₀) * Real.log (3 * E * (N₁ + 1)) + d₀ * T₀ ≤ d₀ * (2 * a2 + 3) * (T₀ * mu) := by
    have := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ d₀ * T₀)
    have : (d₀ : ℝ) * T₀ ≤ d₀ * T₀ * (2 * mu) := by
      have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 2 * mu) (by positivity : (0 : ℝ) ≤ d₀ * T₀)
      linarith
    nlinarith
  have f3 : (d₁ : ℝ) * (2 * T₁) + 3 * E * T₁ * N₁ ≤ (2 * d₁ + 3 * E) * (T₁ * (N₁ + 1)) := by
    have := mul_nonneg (mul_nonneg hd₁ (by linarith : (0 : ℝ) ≤ T₁)) hN₁
    have : 0 ≤ E * T₁ := by nlinarith
    nlinarith
  have g0 : 0 ≤ (N₀ : ℝ) * lam := by positivity
  have g1 : 0 ≤ (T₀ : ℝ) * mu := mul_nonneg (by linarith) (by linarith)
  have g2 : 0 ≤ (T₁ : ℝ) * (N₁ + 1) := by positivity
  set K := a1 + 1 + d₀ * (2 * a2 + 3) + 2 * d₁ + 3 * E
  have k1 := mul_le_mul_of_nonneg_right (by linarith : a1 + 1 ≤ K) g0
  have k2 := mul_le_mul_of_nonneg_right (by linarith : d₀ * (2 * a2 + 3) ≤ K) g1
  have k3 := mul_le_mul_of_nonneg_right (by linarith : 2 * d₁ + 3 * E ≤ K) g2
  have hdist : K * ((N₀ : ℝ) * lam + (T₀ : ℝ) * mu + (T₁ : ℝ) * ((N₁ : ℝ) + 1)) =
      K * (N₀ * lam) + K * (T₀ * mu) + K * (T₁ * (N₁ + 1)) := by ring
  rw [hdist]
  linarith

/-- The norms of the points `Σ s_j η_j`. -/
lemma p_bounds {ι₀ ι₁ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₁]
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (N₁ : ℕ) (s : κ₁ → ℤ) (hs : ∀ j, |s j| ≤ (N₁ : ℤ)) :
    (∀ h, ‖(∑ j, ((s j : ℤ) : ℂ) • η j).1 h‖ ≤
      N₁ * (1 + ∑ j, (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖))) ∧
    ∑ i, ‖(∑ j, ((s j : ℤ) : ℂ) • η j).2 i‖ ≤
      N₁ * (1 + ∑ j, (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖)) := by
  have hs' : ∀ j, ‖((s j : ℤ) : ℂ)‖ ≤ N₁ := by
    intro j; rw [Complex.norm_intCast, ← Int.cast_abs]; exact_mod_cast hs j
  have hN₁ : (0 : ℝ) ≤ N₁ := N₁.cast_nonneg
  have hsum : ∑ j, (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖) ≤
      1 + ∑ j, (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖) := by linarith
  constructor
  · intro h
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖((s j : ℤ) : ℂ) * (η j).1 h‖
        ≤ ∑ j, (N₁ : ℝ) * (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖) := by
          gcongr with j
          rw [norm_mul]
          refine mul_le_mul (hs' j) ?_ (norm_nonneg _) hN₁
          have := Finset.single_le_sum (f := fun h => ‖(η j).1 h‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ h)
          have : 0 ≤ ∑ i, ‖(η j).2 i‖ := by positivity
          linarith
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum hN₁
  · simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ i, ‖∑ j, ((s j : ℤ) : ℂ) * (η j).2 i‖
        ≤ ∑ i, ∑ j, (N₁ : ℝ) * ‖(η j).2 i‖ := by
          gcongr with i
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hs' j) (norm_nonneg _)
      _ = ∑ j, (N₁ : ℝ) * ∑ i, ‖(η j).2 i‖ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
      _ ≤ ∑ j, (N₁ : ℝ) * (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖) := by
          gcongr with j
          have : 0 ≤ ∑ h, ‖(η j).1 h‖ := by positivity
          linarith
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum hN₁

/-- The entries on `‖z‖ ≤ 3` are at most `exp β`. -/
lemma entry_norm_le {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (H : ℝ) (hH : 1 ≤ H)
    (hw : ∀ k, (∀ h, ‖(w k).1 h‖ ≤ H) ∧ ∀ i, ‖(w k).2 i‖ ≤ H) (T₀ T₁ N₀ N₁ : ℕ) (E : ℝ)
    (hE : 1 ≤ E) (q : (ι₀ → ℂ) × (ι₁ → ℂ)) (hq1 : ∀ h, ‖q.1 h‖ ≤ N₁ * E)
    (hq2 : ∑ i, ‖q.2 i‖ ≤ N₁ * E) (z : ℂ) (hz : ‖z‖ ≤ 3) (r : ℕ) (hr : r ≤ N₀) (κ : Fin r → κ₀)
    (l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) :
    ‖MvPolynomial.eval (z • q).1
        (opPoly w r κ (fun i => ((l'.2 i : ℕ) : ℂ) - T₁) (fun h => (l'.1 h : ℕ)))
      * Complex.exp (∑ i, ((((l'.2 i : ℕ) : ℤ) - T₁ : ℤ) : ℂ) * (z • q).2 i)‖ ≤
    Real.exp ((N₀ : ℝ) * Real.log (H * (Fintype.card ι₀ * T₀ + Fintype.card ι₁ * T₁ + 1))
      + ((Fintype.card ι₀ : ℝ) * T₀) * Real.log (3 * E * (N₁ + 1)) + 3 * E * T₁ * N₁) := by
  have hN₁ : (0 : ℝ) ≤ N₁ := N₁.cast_nonneg
  have htt : ∀ i, ((((l'.2 i : ℕ) : ℤ) - T₁ : ℤ) : ℂ) = ((l'.2 i : ℕ) : ℂ) - T₁ := by
    intro i; push_cast; ring
  have ht : ∀ i, ‖((l'.2 i : ℕ) : ℂ) - T₁‖ ≤ T₁ := by
    intro i
    have h2 : ((l'.2 i : ℕ) : ℝ) ≤ 2 * T₁ := by exact_mod_cast (by omega : (l'.2 i : ℕ) ≤ 2 * T₁)
    have h0 : (0 : ℝ) ≤ ((l'.2 i : ℕ) : ℝ) := Nat.cast_nonneg _
    have : ((l'.2 i : ℕ) : ℂ) - T₁ = ((((l'.2 i : ℕ) : ℝ) - T₁ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have htb : ∑ i, ‖((l'.2 i : ℕ) : ℂ) - T₁‖ ≤ Fintype.card ι₁ * T₁ := by
    calc _ ≤ ∑ _i : ι₁, (T₁ : ℝ) := Finset.sum_le_sum fun i _ => ht i
      _ = _ := by simp
  have hτ : (∑ h, (l'.1 h : ℕ)) ≤ Fintype.card ι₀ * T₀ := by
    calc _ ≤ ∑ _h : ι₀, T₀ := Finset.sum_le_sum fun h _ => Nat.lt_succ_iff.mp (l'.1 h).isLt
      _ = _ := by simp
  have hτr : ((∑ h, (l'.1 h : ℕ) : ℕ) : ℝ) ≤ Fintype.card ι₀ * T₀ := by exact_mod_cast hτ
  set P : ℝ := 3 * E * (N₁ + 1) with hPdef
  have hP : 1 ≤ P := by nlinarith
  have hp : ∀ h, ‖(z • q).1 h‖ ≤ P := by
    intro h
    rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, norm_mul]
    calc ‖z‖ * ‖q.1 h‖ ≤ 3 * (N₁ * E) := mul_le_mul hz (hq1 h) (norm_nonneg _) (by norm_num)
      _ ≤ P := by nlinarith
  have hA7 := op_monomial_eval_norm_le w H (by linarith) hw (z • q).1 P hP hp
    (fun i => ((l'.2 i : ℕ) : ℂ) - T₁) _ htb r κ (fun h => (l'.1 h : ℕ))
  set X := H * (Fintype.card ι₀ * T₀ + Fintype.card ι₁ * T₁ + 1) with hXdef
  have hX1 : 1 ≤ X := by
    have : (0 : ℝ) ≤ Fintype.card ι₀ * T₀ + Fintype.card ι₁ * T₁ := by positivity
    nlinarith
  have h1 : ‖MvPolynomial.eval (z • q).1
        (opPoly w r κ (fun i => ((l'.2 i : ℕ) : ℂ) - T₁) (fun h => (l'.1 h : ℕ)))‖ ≤
      X ^ N₀ * P ^ (Fintype.card ι₀ * T₀) := by
    refine hA7.trans (mul_le_mul ?_ (pow_le_pow_right₀ hP hτ) (by positivity) (by positivity))
    refine (pow_le_pow_left₀ (by positivity) ?_ r).trans (pow_le_pow_right₀ hX1 hr)
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : ‖Complex.exp (∑ i, ((((l'.2 i : ℕ) : ℤ) - T₁ : ℤ) : ℂ) * (z • q).2 i)‖ ≤
      Real.exp (3 * E * T₁ * N₁) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    calc ∑ i, ‖((((l'.2 i : ℕ) : ℤ) - T₁ : ℤ) : ℂ) * (z • q).2 i‖
        ≤ ∑ i, (T₁ : ℝ) * (3 * ‖q.2 i‖) := by
          gcongr with i
          rw [norm_mul, htt, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, norm_mul]
          exact mul_le_mul (ht i) (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
            (by positivity) (by positivity)
      _ = 3 * T₁ * ∑ i, ‖q.2 i‖ := by rw [Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ 3 * E * T₁ * N₁ := by
          have := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ 3 * T₁)
          linarith
  rw [norm_mul]
  refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
  have e1 : Real.exp (N₀ * Real.log X) = X ^ N₀ := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  have e2 : Real.exp (((Fintype.card ι₀ : ℝ) * T₀) * Real.log P) = P ^ (Fintype.card ι₀ * T₀) := by
    have : ((Fintype.card ι₀ : ℝ) * T₀) = ((Fintype.card ι₀ * T₀ : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by linarith)]
  rw [Real.exp_add, Real.exp_add, e1, e2]

end C14_upper

open DiazModulus C14_upper in
theorem solution {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (V : Submodule ℂ ((ι₀ → ℂ) × (ι₁ → ℂ))) (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwV : ∀ k, w k ∈ V)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηV : ∀ j, η j ∈ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ T₁ N₀ N₁ : ℕ, 1 ≤ T₀ → 1 ≤ T₁ →
    ∀ (ro : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℕ) (ka : (l : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → Fin (ro l) → κ₀)
      (sv : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → κ₁ → ℤ), (∀ l, ro l ≤ N₀) → (∀ l j, |sv l j| ≤ (N₁ : ℤ)) →
      ‖(Matrix.of fun l l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) =>
        MvPolynomial.eval (∑ j, (((sv l) j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin (ro l) =>
            ((∑ h, (w ((ka l) k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w ((ka l) k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ (sv l) j) ^ (((l'.2 i : ℕ) : ℤ) - T₁)).det‖
        ≤ Real.exp (-(((sInf {S | ∃ κ' : Fin ((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁) → (Fin (Module.finrank ℂ ↥V) → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} : ℕ) : ℝ)
              - (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) * N₀)
            + C * (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1))) := by
  -- the coordinate map of `V`
  set n := Module.finrank ℂ ↥V with hn
  let b := Module.finBasis ℂ ↥V
  let ψ : (Fin n → ℂ) →L[ℂ] (ι₀ → ℂ) × (ι₁ → ℂ) :=
    V.subtypeL.comp (b.equivFunL.symm : (Fin n → ℂ) →L[ℂ] ↥V)
  have hψ : ∀ x (hx : x ∈ V), ψ (b.equivFunL ⟨x, hx⟩) = x := by intro x hx; simp [ψ]
  -- the constants
  set H : ℝ := 1 + ∑ k, (∑ h, ‖(w k).1 h‖ + ∑ i, ‖(w k).2 i‖) with hHdef
  set E : ℝ := 1 + ∑ j, (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖) with hEdef
  have hH : 1 ≤ H := by have : 0 ≤ ∑ k, (∑ h, ‖(w k).1 h‖ + ∑ i, ‖(w k).2 i‖) := by positivity
                        linarith
  have hE : 1 ≤ E := by have : 0 ≤ ∑ j, (∑ h, ‖(η j).1 h‖ + ∑ i, ‖(η j).2 i‖) := by positivity
                        linarith
  have hw : ∀ k, (∀ h, ‖(w k).1 h‖ ≤ H) ∧ ∀ i, ‖(w k).2 i‖ ≤ H := by
    intro k
    have hk := Finset.single_le_sum (f := fun k => ∑ h, ‖(w k).1 h‖ + ∑ i, ‖(w k).2 i‖)
      (fun _ _ => by positivity) (Finset.mem_univ k)
    have a1 : 0 ≤ ∑ h, ‖(w k).1 h‖ := by positivity
    have a2 : 0 ≤ ∑ i, ‖(w k).2 i‖ := by positivity
    refine ⟨fun h => ?_, fun i => ?_⟩
    · have := Finset.single_le_sum (f := fun h => ‖(w k).1 h‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ h)
      linarith
    · have := Finset.single_le_sum (f := fun i => ‖(w k).2 i‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
      linarith
  obtain ⟨K, hK, hKb⟩ := xi_bound H E hH hE (Fintype.card ι₀) (Fintype.card ι₁)
  refine ⟨K, hK, ?_⟩
  intro T₀ T₁ N₀ N₁ hT₀ hT₁ ro ka sv hro hsv
  classical
  set Lnat := (T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ with hLnat
  have hcard : Fintype.card ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) = Lnat := by
    simp [Lnat]
  let e := Fintype.equivFinOfCardEq hcard
  -- the data of the determinant
  let p : ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → (ι₀ → ℂ) × (ι₁ → ℂ) :=
    fun l => ∑ j, ((sv l j : ℤ) : ℂ) • η j
  have hpV : ∀ l, p l ∈ V := fun l => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hηV j)
  let τ : ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → ι₀ → ℕ := fun l' h => (l'.1 h : ℕ)
  let tt : ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → ι₁ → ℤ :=
    fun l' i => ((l'.2 i : ℕ) : ℤ) - T₁
  let tc : ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → ι₁ → ℂ :=
    fun l' i => ((l'.2 i : ℕ) : ℂ) - T₁
  let f : Fin Lnat → (Fin n → ℂ) → ℂ := fun a => expMono (τ (e.symm a)) (tt (e.symm a)) ∘ ψ
  let ζ : Fin Lnat → Fin n → ℂ := fun μ => b.equivFunL ⟨p (e.symm μ), hpV _⟩
  let σ : Fin Lnat → ℕ := fun μ => ro (e.symm μ)
  let v : (μ : Fin Lnat) → Fin (σ μ) → Fin n → ℂ :=
    fun μ k => b.equivFunL ⟨w (ka (e.symm μ) k), hwV _⟩
  have hζ : ∀ μ, ψ (ζ μ) = p (e.symm μ) := fun μ => hψ _ _
  have hv : ∀ μ k, ψ (v μ k) = w (ka (e.symm μ) k) := fun μ k => hψ _ _
  let G : ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) →
      ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → ℂ → ℂ := fun l l' z =>
    MvPolynomial.eval (z • p l).1 (opPoly w (ro l) (ka l) (tc l') (τ l'))
      * Complex.exp (∑ i, ((tt l' i : ℤ) : ℂ) * (z • p l).2 i)
  let F : ℂ → ℂ := fun z =>
    (Matrix.of fun a μ => iteratedFDeriv ℂ (σ μ) (f a) (z • ζ μ) (v μ)).det
  have hFG : ∀ z, F z = (Matrix.of fun l l' => G l l' z).det := by
    intro z
    have : (Matrix.of fun a μ => iteratedFDeriv ℂ (σ μ) (f a) (z • ζ μ) (v μ)) =
        Matrix.transpose ((Matrix.of fun l l' => G l l' z).submatrix e.symm e.symm) := by
      ext a μ
      simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply]
      refine (entry_eq w (τ (e.symm a)) (tt (e.symm a)) (tc (e.symm a))
        (fun i => by simp [tt, tc]) ψ (z • ζ μ) (σ μ) (ka (e.symm μ)) (v μ) (hv μ)).trans ?_
      rw [ψ.map_smul, hζ]
    change (Matrix.of fun a μ => iteratedFDeriv ℂ (σ μ) (f a) (z • ζ μ) (v μ)).det = _
    rw [this, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
  have hdiff : Differentiable ℂ F := by
    apply differentiable_det (fun z => Matrix.of fun a μ => iteratedFDeriv ℂ (σ μ) (f a) (z • ζ μ) (v μ))
    intro a μ
    have hc : ContDiff ℂ ((σ μ + 1 : ℕ) : WithTop ℕ∞) (f a) := (comp_analytic _ _ ψ).contDiff
    have h1 := (hc.differentiable_iteratedFDeriv (m := σ μ) (by exact_mod_cast Nat.lt_succ_self _)).comp
      (by fun_prop : Differentiable ℂ fun z : ℂ => z • ζ μ)
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (σ μ) => Fin n → ℂ) ℂ (v μ)).differentiable.comp h1
  -- the order at the origin
  have hord := interpolation_det_order f (fun a => comp_analytic _ _ ψ) ζ σ v
  set Θ := sInf {S | ∃ κ' : Fin Lnat → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i}
    with hΘ
  set S := ∑ μ, σ μ with hS
  have hS' : S ≤ Lnat * N₀ := by
    calc S ≤ ∑ _μ : Fin Lnat, N₀ := Finset.sum_le_sum fun μ _ => hro _
      _ = Lnat * N₀ := by simp
  have hT : ((Θ - S : ℕ) : ℕ∞) ≤ analyticOrderAt F 0 := by
    have h' : (Θ : ℕ∞) ≤ analyticOrderAt F 0 + (S : ℕ∞) := by simpa [S, Nat.cast_sum] using hord
    rw [ENat.natCast_sub]
    exact tsub_le_iff_right.mpr h'
  -- the bound on the circle `|z| = e`
  set β : ℝ := (N₀ : ℝ) * Real.log (H * (Fintype.card ι₀ * T₀ + Fintype.card ι₁ * T₁ + 1))
      + ((Fintype.card ι₀ : ℝ) * T₀) * Real.log (3 * E * (N₁ + 1)) + 3 * E * T₁ * N₁ with hβ
  have hB : ∀ z : ℂ, ‖z‖ = Real.exp 1 → ‖F z‖ ≤ (Lnat.factorial : ℝ) * Real.exp β ^ Lnat := by
    intro z hz
    have hz3 : ‖z‖ ≤ 3 := by
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    rw [hFG]
    have := norm_det_le (Matrix.of fun l l' => G l l' z) (Real.exp β) (fun l l' => by
      obtain ⟨hq1, hq2⟩ := p_bounds η N₁ (sv l) (hsv l)
      exact entry_norm_le w H hH hw T₀ T₁ N₀ N₁ E hE (p l) hq1 hq2 z hz3 (ro l) (hro l) (ka l) l')
    rwa [hcard] at this
  have hsch := schwarz_order_at_zero F hdiff (Θ - S) hT (Real.exp 1) _ (Real.one_le_exp zero_le_one) hB
  -- `F 1` is the determinant of the statement
  have hF1 : ∀ X : ℂ, X = F 1 →
      ‖X‖ ≤ Real.exp 1 ^ (-((Θ - S : ℕ) : ℤ)) * ((Lnat.factorial : ℝ) * Real.exp β ^ Lnat) := by
    intro X hX; rw [hX]; exact hsch
  refine (hF1 _ ?_).trans ?_
  · rw [hFG 1]
    congr 1
    ext l l'
    simp only [Matrix.of_apply, G, one_smul]
    congr 1
    · simp only [p, Prod.fst_sum, Prod.smul_fst]
      rfl
    · rw [exp_prod_eq (fun j i => (η j).2 i) (sv l) (tt l')]
      simp only [p, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- the arithmetic
  have hLpos : (0 : ℝ) < Lnat := by
    have : 0 < Lnat := by positivity
    exact_mod_cast this
  have hfac : (Lnat.factorial : ℝ) ≤ Real.exp (Real.log Lnat) ^ Lnat := by
    rw [Real.exp_log hLpos]; exact_mod_cast Nat.factorial_le_pow Lnat
  have hbig : (Lnat.factorial : ℝ) * Real.exp β ^ Lnat ≤
      Real.exp (K * Lnat * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1))) := by
    refine (mul_le_mul_of_nonneg_right hfac (by positivity)).trans ?_
    rw [← mul_pow, ← Real.exp_add, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have := hKb T₀ T₁ N₀ N₁ hT₀ hT₁
    rw [mul_comm K, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa [hLnat] using this) hLpos.le
  have hexp : Real.exp 1 ^ (-((Θ - S : ℕ) : ℤ)) = Real.exp (-((Θ - S : ℕ) : ℝ)) := by
    rw [zpow_neg, zpow_natCast, ← Real.exp_nat_mul, mul_one, Real.exp_neg]
  rw [hexp]
  have hΘS : (Θ : ℝ) - Lnat * N₀ ≤ ((Θ - S : ℕ) : ℝ) := by
    have h1 : Θ ≤ (Θ - S) + Lnat * N₀ := by omega
    have : (Θ : ℝ) ≤ ((Θ - S : ℕ) : ℝ) + ((Lnat * N₀ : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have hm : Real.exp (-((Θ - S : ℕ) : ℝ)) ≤ Real.exp (-((Θ : ℝ) - Lnat * N₀)) :=
    Real.exp_le_exp.mpr (by linarith)
  refine (mul_le_mul hm hbig (by positivity) (by positivity)).trans (le_of_eq ?_)
  rw [← Real.exp_add]
