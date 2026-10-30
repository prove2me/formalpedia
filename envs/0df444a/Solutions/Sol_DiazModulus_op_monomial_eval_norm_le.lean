-- Prove2me | solution 1 for DiazModulus.op_monomial_eval_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:21:25.146995+00:00
-- url     : https://prove2.me/submissions/fa082524-a606-46dd-9c55-d587d939a2be

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Size of `Op⋯Op X^τ` at a point

Each operator is `Op_v = Σ_h v₁(h) ∂_h + c_v` with `|v₁(h)| ≤ H` and `|c_v| = |Σ_i v₂(i) t_i| ≤ H·tb`.
We prove, by induction on `r` and for every exponent `s` at once, that
`|eval p (Op_{v_1}⋯Op_{v_r} X^s)| ≤ (H(|s| + tb + 1))^r P^{|s|}`.
The list product applies the last operator first, so the induction peels off the last factor
(`List.ofFn_succ'`). One operator sends `X^s` to `Σ_h v₁(h) s_h X^{s - e_h} + c_v X^s`
(`MvPolynomial.pderiv_monomial`). The remaining operators are linear, so the induction
hypothesis bounds every term; the exponent `s - e_h` is pointwise below `s`, and `1 ≤ P`,
`0 ≤ H` make the bound monotone in `|s|`. Summing gives `H(|s| + tb)·B ≤ H(|s| + tb + 1)·B`.
The base case is `|p^s| ≤ P^{|s|}`. Finally `∏_h X_h^{τ_h}` is the monomial of `τ`. -/

namespace C14_A7
open DiazModulus MvPolynomial

lemma eval_monomial_norm_le {ι₀ : Type} [Fintype ι₀] (p : ι₀ → ℂ) (P : ℝ)
    (hp : ∀ h, ‖p h‖ ≤ P) (s : ι₀ →₀ ℕ) :
    ‖eval p (monomial s (1 : ℂ))‖ ≤ P ^ (∑ h, s h) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), one_mul, norm_prod,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun h _ => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hp h) _

lemma key {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (Hw : ℝ) (hHw : 0 ≤ Hw)
    (hw : ∀ k, (∀ h, ‖(w k).1 h‖ ≤ Hw) ∧ ∀ i, ‖(w k).2 i‖ ≤ Hw)
    (p : ι₀ → ℂ) (P : ℝ) (hP : 1 ≤ P) (hp : ∀ h, ‖p h‖ ≤ P)
    (t : ι₁ → ℂ) (tb : ℝ) (ht : ∑ i, ‖t i‖ ≤ tb) :
    ∀ (r : ℕ) (κ : Fin r → κ₀) (s : ι₀ →₀ ℕ),
    ‖MvPolynomial.eval p ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * t i) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod (monomial s 1))‖
      ≤ (Hw * ((∑ h, s h : ℕ) + tb + 1)) ^ r * P ^ (∑ h, s h) := by
  have htb : 0 ≤ tb := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) ht
  -- monotonicity of the bound in the exponent
  have mono : ∀ (r : ℕ) (σ s : ι₀ →₀ ℕ), (∀ h, σ h ≤ s h) →
      (Hw * ((∑ h, σ h : ℕ) + tb + 1)) ^ r * P ^ (∑ h, σ h)
        ≤ (Hw * ((∑ h, s h : ℕ) + tb + 1)) ^ r * P ^ (∑ h, s h) := by
    intro r σ s hσ
    have hsum : (∑ h, σ h) ≤ ∑ h, s h := Finset.sum_le_sum fun h _ => hσ h
    have hsumR : ((∑ h, σ h : ℕ) : ℝ) ≤ ((∑ h, s h : ℕ) : ℝ) := by exact_mod_cast hsum
    gcongr
  intro r
  induction r with
  | zero =>
    intro κ s
    simpa using eval_monomial_norm_le p P hp s
  | succ r ih =>
    intro κ s
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton,
      Module.End.mul_apply]
    set M := (List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ (Fin.castSucc k))).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ (Fin.castSucc k))).2 i * t i) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod with hM
    set v := w (κ (Fin.last r)) with hv
    set B : ℝ := (Hw * ((∑ h, s h : ℕ) + tb + 1)) ^ r * P ^ (∑ h, s h) with hB
    have hB0 : 0 ≤ B := by positivity
    have hc : ‖∑ i, v.2 i * t i‖ ≤ Hw * tb := by
      calc ‖∑ i, v.2 i * t i‖ ≤ ∑ i, ‖v.2 i‖ * ‖t i‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
        _ ≤ ∑ i, Hw * ‖t i‖ := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right ((hw _).2 i) (norm_nonneg _)
        _ = Hw * ∑ i, ‖t i‖ := (Finset.mul_sum _ _ _).symm
        _ ≤ Hw * tb := mul_le_mul_of_nonneg_left ht hHw
    have hterm : ∀ h, ‖v.1 h • (s h : ℂ) • eval p (M (monomial (s - Finsupp.single h 1) 1))‖
        ≤ Hw * (s h : ℝ) * B := by
      intro h
      rw [norm_smul, norm_smul, ← mul_assoc]
      have h1 := ih (κ ∘ Fin.castSucc) (s - Finsupp.single h 1)
      have h2 := mono r (s - Finsupp.single h 1) s (fun h' => tsub_le_self)
      gcongr
      · exact (hw _).1 h
      · simp
      · exact h1.trans h2
    have hexp : eval p (M ((∑ h, v.1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, v.2 i * t i) • LinearMap.id : Module.End ℂ (MvPolynomial ι₀ ℂ))
                (monomial s 1)))
        = ∑ h, v.1 h • (s h : ℂ) • eval p (M (monomial (s - Finsupp.single h 1) 1))
          + (∑ i, v.2 i * t i) • eval p (M (monomial s 1)) := by
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.id_apply, Derivation.coeFn_coe, pderiv_monomial, one_mul, map_add,
        map_sum, map_smul, smul_eval]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [show (monomial (s - Finsupp.single h 1) (s h : ℂ)) =
          (s h : ℂ) • monomial (s - Finsupp.single h 1) 1 by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eval]
      simp only [smul_eq_mul]
    rw [hexp]
    calc _ ≤ ∑ h, ‖v.1 h • (s h : ℂ) • eval p (M (monomial (s - Finsupp.single h 1) 1))‖
            + ‖(∑ i, v.2 i * t i) • eval p (M (monomial s 1))‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
      _ ≤ ∑ h, Hw * (s h : ℝ) * B + Hw * tb * B := by
          gcongr with h
          · exact hterm h
          · rw [norm_smul]
            exact mul_le_mul hc (ih (κ ∘ Fin.castSucc) s) (norm_nonneg _)
              (mul_nonneg hHw htb)
      _ = Hw * ((∑ h, s h : ℕ) + tb) * B := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]; push_cast; ring
      _ ≤ Hw * ((∑ h, s h : ℕ) + tb + 1) * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hHw) hB0
      _ = (Hw * ((∑ h, s h : ℕ) + tb + 1)) ^ (r + 1) * P ^ (∑ h, s h) := by
          rw [hB, pow_succ]; ring

end C14_A7

open DiazModulus C14_A7 in
theorem solution {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (Hw : ℝ) (hHw : 0 ≤ Hw)
    (hw : ∀ k, (∀ h, ‖(w k).1 h‖ ≤ Hw) ∧ ∀ i, ‖(w k).2 i‖ ≤ Hw)
    (p : ι₀ → ℂ) (P : ℝ) (hP : 1 ≤ P) (hp : ∀ h, ‖p h‖ ≤ P)
    (t : ι₁ → ℂ) (tb : ℝ) (ht : ∑ i, ‖t i‖ ≤ tb) (r : ℕ) (κ : Fin r → κ₀) (τ : ι₀ → ℕ) :
    ‖MvPolynomial.eval p ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * t i) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
          (∏ h, MvPolynomial.X h ^ τ h))‖
      ≤ (Hw * ((∑ h, τ h : ℕ) + tb + 1)) ^ r * P ^ (∑ h, τ h) := by
  have hmono : (∏ h, MvPolynomial.X h ^ τ h : MvPolynomial ι₀ ℂ) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm τ) 1 := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp
  rw [hmono]
  simpa using key w Hw hHw hw p P hP hp t tb ht r κ (Finsupp.equivFunOnFinite.symm τ)
