-- Prove2me | solution 1 for DiazModulus.eval_torusDerivList_torusCoeffPoly
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:00:46.368915+00:00
-- url     : https://prove2.me/submissions/022deb8a-58ed-41ec-b034-51b595814d23

import Mathlib
import Definitions.Def_DiazMultiplicity

open Complex ComplexConjugate

/-! # The derivatives of `P_c` at a torus point

Write `ι = rename Sum.inl : K[X] → K[X, Y, Z]` and `YZ_l = Π_i Y_i^{(s_i − D₁)₊} Z_i^{(D₁ − s_i)₊}`, so that
`P_c = Σ_l c_l ι(X^τ) YZ_l`. Two facts about a single `D_w`, `w = (ξ, η)`: (i) `D_w ∘ ι = ι ∘ Σ_h ξ_h ∂/∂X_h`
(induction on the polynomial, Leibniz and `pderiv_X`); (ii) `YZ_l` is an eigenvector,
`D_w YZ_l = μ_w YZ_l` with `μ_w = Σ_i η_i (s_i − D₁)`, because `Y_i`, `Z_i` are eigenvectors with eigenvalues `η_i`,
`−η_i` and eigenvalues add over products (`Derivation.leibniz`, `Finset.induction_on`). Leibniz then gives
`D_w (ι(Q) YZ_l) = ι(Op_{w,l} Q) YZ_l` with `Op_{w,l} = Σ_h ξ_h ∂_h + μ_w`, and by induction on the list
`D_{w₁} ⋯ D_{w_r} (ι(Q) YZ_l) = ι(Op_{w₁,l} ⋯ Op_{w_r,l} Q) YZ_l`, both products in the same order
(`List.map_ofFn`). Evaluating at `(x, y, y⁻¹)`: `eval ∘ ι = eval x` (`eval_rename`) and `YZ_l ↦ Π_i y_i^{s_i − D₁}`
(a case split on `s_i ≤ D₁`). Summing over `l` with the coefficients `c_l` gives the formula. -/

namespace C13_O4
open DiazModulus MvPolynomial

variable {K A₀ A₁ : Type*} [Field K]

/-- `D_w ∘ ι = ι ∘ Σ_h ξ_h ∂/∂X_h`. -/
theorem torusDeriv_rename [Fintype A₀] [DecidableEq A₀] (w : (A₀ → K) × (A₁ → K)) (Q : MvPolynomial A₀ K) :
    torusDeriv w (rename (Sum.inl : A₀ → A₀ ⊕ (A₁ × Bool)) Q)
      = rename Sum.inl (∑ h, w.1 h • pderiv h Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p h hp =>
    rw [map_mul, rename_X, Derivation.leibniz, hp, torusDeriv_X_inl]
    simp only [Derivation.leibniz, pderiv_X, smul_add, Finset.sum_add_distrib, smul_eq_mul, map_add,
      Pi.single_apply, mul_ite, mul_one, mul_zero, map_sum]
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, rename_C, apply_ite (rename (Sum.inl : A₀ → A₀ ⊕ (A₁ × Bool))),
      map_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, rename_X]
    rw [Finset.mul_sum, mul_comm (rename _ p)]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Eigenvalues add over products. -/
theorem torusDeriv_prod_eigen {ι : Type*} (w : (A₀ → K) × (A₁ → K)) (s : Finset ι)
    (f : ι → MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (μ : ι → K) (hf : ∀ i ∈ s, torusDeriv w (f i) = C (μ i) * f i) :
    torusDeriv w (∏ i ∈ s, f i) = C (∑ i ∈ s, μ i) * ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Derivation.leibniz,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), hf j (Finset.mem_insert_self _ _), C_add, smul_eq_mul,
      smul_eq_mul]
    ring

theorem torusDeriv_pow_eigen (w : (A₀ → K) × (A₁ → K)) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (μ : K)
    (hf : torusDeriv w f = C μ * f) (n : ℕ) : torusDeriv w (f ^ n) = C ((n : K) * μ) * f ^ n := by
  have := torusDeriv_prod_eigen w (Finset.range n) (fun _ => f) (fun _ => μ) (fun _ _ => hf)
  simpa [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this

theorem natSub_cast (n D : ℕ) : ((n - D : ℕ) : K) - ((D - n : ℕ) : K) = (n : K) - D := by
  rcases le_total n D with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring

/-- `YZ_l` is an eigenvector of every `D_w`. -/
theorem torusDeriv_YZ [Fintype A₁] (w : (A₀ → K) × (A₁ → K)) (s : A₁ → ℕ) (D₁ : ℕ) :
    torusDeriv w (∏ i, (X (Sum.inr (i, true)) ^ (s i - D₁) * X (Sum.inr (i, false)) ^ (D₁ - s i) :
      MvPolynomial (A₀ ⊕ (A₁ × Bool)) K))
      = C (∑ i, w.2 i * ((s i : K) - D₁)) * ∏ i, (X (Sum.inr (i, true)) ^ (s i - D₁) *
          X (Sum.inr (i, false)) ^ (D₁ - s i)) := by
  refine torusDeriv_prod_eigen w _ _ _ fun i _ => ?_
  have hY := torusDeriv_pow_eigen w (X (Sum.inr (i, true))) (w.2 i) (by simp) (s i - D₁)
  have hZ := torusDeriv_pow_eigen w (X (Sum.inr (i, false))) (-w.2 i) (by simp) (D₁ - s i)
  rw [Derivation.leibniz, hY, hZ, ← natSub_cast (s i) D₁, smul_eq_mul, smul_eq_mul]
  simp only [C_mul, C_neg, C_sub, map_natCast]
  ring

/-- The operator `Op_{w, μ} = Σ_h ξ_h ∂_h + μ` on `K[X]`. -/
noncomputable def Op [Fintype A₀] (w : (A₀ → K) × (A₁ → K)) (μ : K) : Module.End K (MvPolynomial A₀ K) :=
  ∑ h, w.1 h • (pderiv h).toLinearMap + μ • LinearMap.id

theorem torusDeriv_rename_mul [Fintype A₀] [DecidableEq A₀] (w : (A₀ → K) × (A₁ → K)) (Q : MvPolynomial A₀ K)
    (F : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (μ : K) (hF : torusDeriv w F = C μ * F) :
    torusDeriv w (rename Sum.inl Q * F) = rename Sum.inl (Op w μ Q) * F := by
  rw [Derivation.leibniz, hF, torusDeriv_rename, Op]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Derivation.coeFn_coe, map_add, smul_eq_mul,
    MvPolynomial.smul_eq_C_mul, map_mul, rename_C]
  ring

theorem torusDerivList_rename_mul [Fintype A₀] [DecidableEq A₀] (L : List ((A₀ → K) × (A₁ → K)))
    (Q : MvPolynomial A₀ K) (F : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) (μ : ((A₀ → K) × (A₁ → K)) → K)
    (hF : ∀ w, torusDeriv w F = C (μ w) * F) :
    torusDerivList L (rename Sum.inl Q * F) = rename Sum.inl ((L.map fun w => Op w (μ w)).prod Q) * F := by
  induction L with
  | nil => simp [torusDerivList]
  | cons w L ih =>
    have : torusDerivList (w :: L) (rename Sum.inl Q * F) = torusDeriv w (torusDerivList L (rename Sum.inl Q * F)) := by
      simp [torusDerivList, Module.End.mul_apply]
    rw [this, ih, torusDeriv_rename_mul w _ F (μ w) (hF w)]
    simp [Module.End.mul_apply]

theorem eval_YZ [Fintype A₁] (y : A₁ → Kˣ) (x : A₀ → K) (s : A₁ → ℕ) (D₁ : ℕ) :
    eval (torusPoint x y) (∏ i, (X (Sum.inr (i, true)) ^ (s i - D₁) * X (Sum.inr (i, false)) ^ (D₁ - s i) :
      MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) = ∏ i, (y i : K) ^ (((s i : ℕ) : ℤ) - D₁) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, eval_X, torusPoint, Sum.elim_inr, if_true, Bool.false_eq_true, if_false,
    Units.val_inv_eq_inv_val]
  rcases le_total (s i) D₁ with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg, Nat.cast_sub h]
    congr 1; ring
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, mul_one, ← zpow_natCast, Nat.cast_sub h]

end C13_O4

open DiazModulus C13_O4 in
theorem solution {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] [DecidableEq A₀] [DecidableEq A₁]
    (D₀ D₁ : ℕ) (c : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1)) → K) (r : ℕ)
    (w : Fin r → (A₀ → K) × (A₁ → K)) (x : A₀ → K) (y : A₁ → Kˣ) :
    MvPolynomial.eval (torusPoint x y) (torusDerivList (List.ofFn w) (torusCoeffPoly D₀ D₁ c))
      = ∑ l, c l * (MvPolynomial.eval x
          ((List.ofFn fun k : Fin r =>
            ((∑ h, (w k).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w k).2 i * (((l.2 i : ℕ) : K) - D₁)) • LinearMap.id :
                Module.End K (MvPolynomial A₀ K)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (y i : K) ^ (((l.2 i : ℕ) : ℤ) - D₁)) := by
  rw [torusCoeffPoly, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hX : (∏ h, MvPolynomial.X (Sum.inl h) ^ (l.1 h : ℕ) : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
      = MvPolynomial.rename Sum.inl (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)) := by
    simp [map_prod, map_pow, MvPolynomial.rename_X]
  rw [map_smul, MvPolynomial.smul_eval, hX,
    torusDerivList_rename_mul _ _ _ (fun w => ∑ i, w.2 i * (((l.2 i : ℕ) : K) - D₁))
      (fun w => torusDeriv_YZ w (fun i => (l.2 i : ℕ)) D₁),
    map_mul, MvPolynomial.eval_rename, eval_YZ y x (fun i => (l.2 i : ℕ)) D₁, List.map_ofFn]
  rfl
