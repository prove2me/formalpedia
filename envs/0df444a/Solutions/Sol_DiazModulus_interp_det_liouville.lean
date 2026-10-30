-- Prove2me | solution 1 for DiazModulus.interp_det_liouville
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:17:57.816003+00:00
-- url     : https://prove2.me/submissions/464c2538-d3a0-466b-bd6e-d8e8c7345c27

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_op_entry_denom_house
import Theorems.Thm_Transcendence_liouville_house

open Complex ComplexConjugate

/-! # Liouville lower bound for the interpolation determinant

All data (`w`, `η.1`, `exp η.2`) are algebraic, so they lie in the number field
`F = ℚ(data) ⊆ ℂ` (`IntermediateField.finiteDimensional_adjoin`); `σ : F → ℂ` is the inclusion.
The complex matrix is `σ` applied entrywise to the same matrix over `F` (`MvPolynomial.map`
commutes with `pderiv` and evaluation), so its determinant is `σ (det M_F)`.
`op_entry_denom_house` (A8) gives `b` and `H` with `b^E · entry` integral of house
`≤ H^E (|τ|+|t|+1)^r (|s|+1)^{|τ|}`; with the uniform `E* = N₀ + |ι₀|T₀ + |ι₁|T₁·|κ₁|N₁`
every entry of `b^{E*} M_F` is integral with house `≤ Bd = H'^{E*} X₀^{N₀} Y₀^{|ι₀|T₀}`.
Then `α = det(b^{E*} M_F)` is a nonzero algebraic integer with house `≤ L!·Bd^L`, and
`Transcendence.liouville_house` (with `c = 1`) gives
`1 ≤ H'^{E* L} |Δ| (L! Bd^L)^{[F:ℚ]-1}`. Taking logarithms and using `log L! ≤ L log L`,
`log L ≤ |ι₀|T₀ + 2|ι₁|T₁`, `log(T₀+T₁+2) ≥ 1`, `log(N₁+2) ≥ 1/2` (`real_bound`) gives
`log |Δ| ≥ −C·L·Ξ`. -/

set_option linter.unusedSectionVars false

namespace C14_A10
open DiazModulus

/-- The real inequality behind the final bound. -/
lemma real_bound (a0 a1 k1 : ℕ) {G D : ℝ} (hG : 0 ≤ G) (hD : 0 ≤ D) (T₀ T₁ N₀ N₁ : ℕ)
    (h0 : 1 ≤ T₀) (h1 : 1 ≤ T₁) :
    ((N₀ + a0 * T₀ + a1 * T₁ * (k1 * N₁) : ℕ) : ℝ) * G
      + D * Real.log (((T₀ + 1) ^ a0 * (2 * T₁ + 1) ^ a1 : ℕ) : ℝ)
      + D * ((N₀ : ℝ) * Real.log ((a0 * T₀ + a1 * T₁ + 1 : ℕ) : ℝ)
        + ((a0 * T₀ : ℕ) : ℝ) * Real.log ((k1 * N₁ + 1 : ℕ) : ℝ))
    ≤ (G * (1 + 2 * a0 + a1 * k1) + D * (Real.log (a0 + a1 + 1) + 1)
        + D * a0 * (2 * Real.log (k1 + 1) + 1) + D * (2 * a0 + 2 * a1))
      * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1)) := by
  have hT0 : (1 : ℝ) ≤ T₀ := by exact_mod_cast h0
  have hT1 : (1 : ℝ) ≤ T₁ := by exact_mod_cast h1
  have hN1 : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a0 := Nat.cast_nonneg _
  have ha1 : (0 : ℝ) ≤ a1 := Nat.cast_nonneg _
  have hk1 : (0 : ℝ) ≤ k1 := Nat.cast_nonneg _
  set l1 := Real.log ((T₀ : ℝ) + T₁ + 2)
  set l2 := Real.log ((N₁ : ℝ) + 2)
  have hl1 : 1 ≤ l1 := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hl2 : 1 / 2 ≤ l2 := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ l2 := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set P := Real.log ((a0 : ℝ) + a1 + 1)
  set R := Real.log ((k1 : ℝ) + 1)
  have hP : 0 ≤ P := Real.log_nonneg (by linarith)
  have hR : 0 ≤ R := Real.log_nonneg (by linarith)
  -- the three pieces of Ξ
  set X := (N₀ : ℝ) * l1 + (T₀ : ℝ) * l2 + (T₁ : ℝ) * ((N₁ : ℝ) + 1)
  have hT0' : (0 : ℝ) ≤ T₀ := by linarith
  have hT1' : (0 : ℝ) ≤ T₁ := by linarith
  have n1 : 0 ≤ (N₀ : ℝ) * l1 := mul_nonneg hN0 (by linarith)
  have n2 : 0 ≤ (T₀ : ℝ) * l2 := mul_nonneg hT0' (by linarith)
  have n3 : 0 ≤ (T₁ : ℝ) * N₁ := mul_nonneg hT1' hN1
  have hXd : X = (N₀ : ℝ) * l1 + T₀ * l2 + (T₁ * N₁ + T₁) := by simp only [X]; ring
  have x1 : (N₀ : ℝ) * l1 ≤ X := by linarith
  have x2 : (T₀ : ℝ) * l2 ≤ X := by linarith
  have hX : 0 ≤ X := by linarith
  -- logarithmic estimates
  have L3 : Real.log ((a0 * T₀ + a1 * T₁ + 1 : ℕ) : ℝ) ≤ P + l1 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    push_cast; nlinarith
  have L4 : Real.log ((k1 * N₁ + 1 : ℕ) : ℝ) ≤ R + l2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    push_cast; nlinarith
  have L5 : Real.log (((T₀ + 1) ^ a0 * (2 * T₁ + 1) ^ a1 : ℕ) : ℝ) ≤ a0 * T₀ + a1 * (2 * T₁) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have e1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T₀ + 1)
    have e2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * T₁ + 1)
    nlinarith
  have t1 : (N₀ : ℝ) ≤ X := by linarith [mul_le_mul_of_nonneg_left hl1 hN0]
  have t2 : (T₀ : ℝ) ≤ 2 * X := by linarith [mul_le_mul_of_nonneg_left hl2 hT0']
  have t3 : (T₁ : ℝ) * N₁ ≤ X := by linarith
  have t4 : (T₁ : ℝ) ≤ X := by linarith
  clear_value X l1 l2 P R
  have E1 : ((N₀ + a0 * T₀ + a1 * T₁ * (k1 * N₁) : ℕ) : ℝ) ≤ (1 + 2 * a0 + a1 * k1) * X := by
    push_cast
    linarith [mul_le_mul_of_nonneg_left t2 ha0, mul_le_mul_of_nonneg_left t3 (mul_nonneg ha1 hk1)]
  have E2 : (N₀ : ℝ) * Real.log ((a0 * T₀ + a1 * T₁ + 1 : ℕ) : ℝ) ≤ (P + 1) * X := by
    calc _ ≤ (N₀ : ℝ) * (P + l1) := mul_le_mul_of_nonneg_left L3 hN0
      _ ≤ (P + 1) * (N₀ * l1) := by
          linarith [mul_nonneg (mul_nonneg hN0 hP) (by linarith : (0 : ℝ) ≤ l1 - 1)]
      _ ≤ (P + 1) * X := mul_le_mul_of_nonneg_left x1 (by linarith)
  have E3 : ((a0 * T₀ : ℕ) : ℝ) * Real.log ((k1 * N₁ + 1 : ℕ) : ℝ) ≤ a0 * (2 * R + 1) * X := by
    have ha0T : (0 : ℝ) ≤ a0 * T₀ := mul_nonneg ha0 hT0'
    calc _ ≤ ((a0 : ℝ) * T₀) * (R + l2) := by
          rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_left L4 ha0T
      _ ≤ a0 * (2 * R + 1) * (T₀ * l2) := by
          linarith [mul_nonneg (mul_nonneg ha0T hR) (by linarith : (0 : ℝ) ≤ 2 * l2 - 1)]
      _ ≤ a0 * (2 * R + 1) * X := mul_le_mul_of_nonneg_left x2 (by positivity)
  have E4 : (a0 : ℝ) * T₀ + a1 * (2 * T₁) ≤ (2 * a0 + 2 * a1) * X := by
    linarith [mul_le_mul_of_nonneg_left t2 ha0, mul_le_mul_of_nonneg_left t4 ha1]
  have F1 := mul_le_mul_of_nonneg_left E1 hG
  have F2 := mul_le_mul_of_nonneg_left E2 hD
  have F3 := mul_le_mul_of_nonneg_left E3 hD
  have F4 := mul_le_mul_of_nonneg_left (L5.trans E4) hD
  have F5 := mul_le_mul_of_nonneg_left (add_le_add E2 E3) hD
  calc _ = ((N₀ + a0 * T₀ + a1 * T₁ * (k1 * N₁) : ℕ) : ℝ) * G
      + D * Real.log (((T₀ + 1) ^ a0 * (2 * T₁ + 1) ^ a1 : ℕ) : ℝ)
      + D * ((N₀ : ℝ) * Real.log ((a0 * T₀ + a1 * T₁ + 1 : ℕ) : ℝ)
        + ((a0 * T₀ : ℕ) : ℝ) * Real.log ((k1 * N₁ + 1 : ℕ) : ℝ)) := rfl
    _ ≤ G * ((1 + 2 * a0 + a1 * k1) * X) + D * ((2 * a0 + 2 * a1) * X)
        + D * ((P + 1) * X + a0 * (2 * R + 1) * X) := by
        rw [mul_comm _ G]; linarith
    _ = _ := by ring

lemma map_ops {F : Type*} [Field F] {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (σ : F →+* ℂ) :
    ∀ (r : ℕ) (c1 : Fin r → ι₀ → F) (c : Fin r → F) (P : MvPolynomial ι₀ F),
    MvPolynomial.map σ ((List.ofFn fun k => (∑ h, c1 k h • (MvPolynomial.pderiv h).toLinearMap
      + c k • LinearMap.id : Module.End F (MvPolynomial ι₀ F))).prod P)
    = (List.ofFn fun k => (∑ h, σ (c1 k h) • (MvPolynomial.pderiv h).toLinearMap
      + σ (c k) • LinearMap.id : Module.End ℂ (MvPolynomial ι₀ ℂ))).prod (MvPolynomial.map σ P)
  | 0, _, _, P => by simp
  | r + 1, c1, c, P => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, ← map_ops σ r (fun k => c1 k.succ) (fun k => c k.succ) P]
    simp [MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_map]

lemma map_eval' {F : Type*} [Field F] {ι₀ : Type} (σ : F →+* ℂ) (p : ι₀ → F)
    (P : MvPolynomial ι₀ F) : σ (MvPolynomial.eval p P) = MvPolynomial.eval (σ ∘ p) (MvPolynomial.map σ P) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_comp]

lemma house_prod_le' {F : Type*} [Field F] [NumberField F] {ι : Type*} (s : Finset ι) (f : ι → F) :
    NumberField.house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, NumberField.house (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using le_of_eq (NumberField.house_intCast (K := F) 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (NumberField.house_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (NumberField.house_nonneg _))

lemma house_det_le {F : Type*} [Field F] [NumberField F] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (B : ℝ) (hB : ∀ i j, NumberField.house (M i j) ≤ B) :
    NumberField.house M.det ≤ (Fintype.card n).factorial * B ^ Fintype.card n := by
  rw [Matrix.det_apply']
  refine (NumberField.house_sum_le_sum_house _ _).trans ?_
  have hterm : ∀ τ : Equiv.Perm n, NumberField.house (((Equiv.Perm.sign τ : ℤ) : F) *
      ∏ i, M (τ i) i) ≤ B ^ Fintype.card n := by
    intro τ
    refine (NumberField.house_mul_le _ _).trans ?_
    rw [NumberField.house_intCast]
    have h1 : |((Equiv.Perm.sign τ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with e | e <;> simp [e]
    rw [Int.cast_abs, h1, one_mul]
    refine (house_prod_le' _ _).trans ?_
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => NumberField.house_nonneg _) fun i _ => hB _ _
  refine (Finset.sum_le_sum fun τ _ => hterm τ).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

lemma det_lower {F : Type*} [Field F] [NumberField F] (σ : F →+* ℂ) {b : F} (hb0 : b ≠ 0)
    {H : ℝ} (hbH : NumberField.house b ≤ H) {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (E : ℕ) (Bd : ℝ)
    (hent : ∀ i j, IsIntegral ℤ (b ^ E * M i j) ∧ NumberField.house (b ^ E * M i j) ≤ Bd)
    (hdet : (σ.mapMatrix M).det ≠ 0) :
    1 ≤ H ^ (E * Fintype.card n) * ‖(σ.mapMatrix M).det‖
      * ((Fintype.card n).factorial * Bd ^ Fintype.card n) ^ (Module.finrank ℚ F - 1) := by
  set α := (b ^ E • M).det
  have hα : α = b ^ (E * Fintype.card n) * M.det := by
    simp only [α, Matrix.det_smul, pow_mul]
  have hMdet : M.det ≠ 0 := by
    intro h; apply hdet; rw [← RingHom.map_det, h, map_zero]
  have hα0 : α ≠ 0 := by rw [hα]; exact mul_ne_zero (pow_ne_zero _ hb0) hMdet
  have hαint : IsIntegral ℤ α := IsIntegral.det fun i j => by simpa using (hent i j).1
  have hαh : NumberField.house α ≤ (Fintype.card n).factorial * Bd ^ Fintype.card n :=
    house_det_le _ Bd fun i j => by simpa using (hent i j).2
  have hσα : ‖σ α‖ ≤ H ^ (E * Fintype.card n) * ‖(σ.mapMatrix M).det‖ := by
    rw [hα, map_mul, map_pow, norm_mul, norm_pow, RingHom.map_det]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) ((NumberField.norm_embedding_le_house _ _).trans hbH) _)
      (norm_nonneg _)
  have hL := Transcendence.liouville_house hα0 (c := 1) one_ne_zero (by simpa using hαint) σ
  simp only [Int.cast_one, abs_one, one_pow, one_mul] at hL
  calc (1 : ℝ) ≤ ‖σ α‖ * NumberField.house α ^ (Module.finrank ℚ F - 1) := hL
    _ ≤ _ := mul_le_mul hσα (pow_le_pow_left₀ (NumberField.house_nonneg _) hαh _)
        (pow_nonneg (NumberField.house_nonneg _) _)
        (mul_nonneg (pow_nonneg ((NumberField.house_nonneg b).trans hbH) _) (norm_nonneg _))

end C14_A10

open DiazModulus C14_A10 in
theorem solution {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwalg : ∀ k, (∀ h, (w k).1 h ∈ Qbar) ∧ ∀ i, (w k).2 i ∈ Qbar)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηalg : ∀ j, (∀ h, (η j).1 h ∈ Qbar) ∧ ∀ i, (η j).2 i ∈ LogAlg) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ T₁ N₀ N₁ : ℕ, 1 ≤ T₀ → 1 ≤ T₁ →
    ∀ (ro : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℕ) (ka : (l : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → Fin (ro l) → κ₀)
      (sv : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → κ₁ → ℤ), (∀ l, ro l ≤ N₀) → (∀ l j, |sv l j| ≤ (N₁ : ℤ)) →
      (Matrix.of fun l l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) =>
        MvPolynomial.eval (∑ j, (((sv l) j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin (ro l) =>
            ((∑ h, (w ((ka l) k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w ((ka l) k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ (sv l) j) ^ (((l'.2 i : ℕ) : ℤ) - T₁)).det ≠ 0 →
      -(C * (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1)))
        ≤ Real.log ‖(Matrix.of fun l l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) =>
        MvPolynomial.eval (∑ j, (((sv l) j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin (ro l) =>
            ((∑ h, (w ((ka l) k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w ((ka l) k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ (sv l) j) ^ (((l'.2 i : ℕ) : ℤ) - T₁)).det‖ := by
  classical
  let θ : (κ₀ × ι₀) ⊕ (κ₀ × ι₁) ⊕ (κ₁ × ι₀) ⊕ (κ₁ × ι₁) → ℂ :=
    Sum.elim (fun p => (w p.1).1 p.2) (Sum.elim (fun p => (w p.1).2 p.2)
      (Sum.elim (fun p => (η p.1).1 p.2) (fun p => Complex.exp ((η p.1).2 p.2))))
  have hθ : ∀ i, IsIntegral ℚ (θ i) := by
    rintro (p | p | p | p)
    · exact (mem_Qbar_iff.mp ((hwalg p.1).1 p.2)).isIntegral
    · exact (mem_Qbar_iff.mp ((hwalg p.1).2 p.2)).isIntegral
    · exact (mem_Qbar_iff.mp ((hηalg p.1).1 p.2)).isIntegral
    · exact ((hηalg p.1).2 p.2 : IsAlgebraic ℚ _).isIntegral
  let F := IntermediateField.adjoin ℚ (Set.range θ)
  have : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact hθ i)
  have : NumberField F := ⟨⟩
  let ψ : _ → F := fun i => ⟨θ i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  let σ : F →+* ℂ := algebraMap F ℂ
  let wK : κ₀ → (ι₀ → F) × (ι₁ → F) := fun k =>
    (fun h => ψ (Sum.inl (k, h)), fun i => ψ (Sum.inr (Sum.inl (k, i))))
  let uK : κ₁ → ι₀ → F := fun j h => ψ (Sum.inr (Sum.inr (Sum.inl (j, h))))
  let aK : κ₁ → ι₁ → F := fun j i => ψ (Sum.inr (Sum.inr (Sum.inr (j, i))))
  have haK : ∀ j i, aK j i ≠ 0 := by
    intro j i e
    have : σ (aK j i) = 0 := by rw [e, map_zero]
    exact Complex.exp_ne_zero _ this
  obtain ⟨b, hb0, hb, H, hH, hA8⟩ := DiazModulus.op_entry_denom_house wK uK aK
  set H' := max H (NumberField.house b)
  have hH' : 1 ≤ H' := le_max_of_le_left hH
  have hbH : NumberField.house b ≤ H' := le_max_right _ _
  set Dm : ℝ := ((Module.finrank ℚ F - 1 : ℕ) : ℝ) with hDmdef
  have hDm : 0 ≤ Dm := Nat.cast_nonneg _
  set a0 := Fintype.card ι₀
  set a1 := Fintype.card ι₁
  set k1 := Fintype.card κ₁
  set G := (1 + Dm) * Real.log H'
  have hG : 0 ≤ G := mul_nonneg (by linarith) (Real.log_nonneg hH')
  set C0 := G * (1 + 2 * a0 + a1 * k1) + Dm * (Real.log (a0 + a1 + 1) + 1)
        + Dm * a0 * (2 * Real.log (k1 + 1) + 1) + Dm * (2 * a0 + 2 * a1)
  have hC0 : 0 ≤ C0 := by
    have := Real.log_nonneg (by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ a0),
      (Nat.cast_nonneg _ : (0:ℝ) ≤ a1)] : (1:ℝ) ≤ a0 + a1 + 1)
    have := Real.log_nonneg (by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ k1)] : (1:ℝ) ≤ k1 + 1)
    positivity
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro T₀ T₁ N₀ N₁ h0 h1 ro ka sv hro hsv hdet
  let tt : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ι₁ → ℤ :=
    fun l' i => ((l'.2 i : ℕ) : ℤ) - T₁
  let MK : Matrix ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)))
      ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) F := Matrix.of fun l l' =>
    MvPolynomial.eval (∑ j, (sv l j : F) • uK j) ((List.ofFn fun k : Fin (ro l) =>
      ((∑ h, (wK (ka l k)).1 h • (MvPolynomial.pderiv h).toLinearMap
        + (∑ i, (wK (ka l k)).2 i * (tt l' i : F)) • LinearMap.id :
          Module.End F (MvPolynomial ι₀ F)))).prod
      (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ))) * ∏ i, (∏ j, aK j i ^ sv l j) ^ tt l' i
  have hmap : σ.mapMatrix MK = (Matrix.of fun l l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) =>
            MvPolynomial.eval (∑ j, (((sv l) j : ℤ) : ℂ) • (fun j => (η j).1) j)
              ((List.ofFn fun k : Fin (ro l) =>
                ((∑ h, (w ((ka l) k)).1 h • (MvPolynomial.pderiv h).toLinearMap
                  + (∑ i, (w ((ka l) k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                    Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
                (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ)))
            * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ (sv l) j) ^ (((l'.2 i : ℕ) : ℤ) - T₁)) := by
    ext l l'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MK, map_mul, map_prod,
      map_zpow₀, map_eval', map_ops]
    congr 1
    have e1 : ⇑σ ∘ (∑ j, (sv l j : F) • uK j) = ∑ j, ((sv l j : ℤ) : ℂ) • (η j).1 := by
      funext h; simp [Finset.sum_apply, uK, ψ, θ, σ]
    have e2 : ∀ k, σ (∑ i, (wK (ka l k)).2 i * (tt l' i : F))
        = ∑ i, (w (ka l k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁) := by
      intro k; simp [wK, ψ, θ, σ, tt]
    have e3 : ∀ k h, σ ((wK (ka l k)).1 h) = (w (ka l k)).1 h := fun _ _ => rfl
    simp only [e1, e2, e3, map_pow, MvPolynomial.map_X]
  rw [← hmap] at hdet ⊢
  set Es := N₀ + a0 * T₀ + a1 * T₁ * (k1 * N₁)
  set X0 : ℝ := ((a0 * T₀ + a1 * T₁ + 1 : ℕ) : ℝ)
  set Y0 : ℝ := ((k1 * N₁ + 1 : ℕ) : ℝ)
  have hX0 : 1 ≤ X0 := by simp [X0]; positivity
  have hY0 : 1 ≤ Y0 := by simp [Y0]; positivity
  set Bd := H' ^ Es * X0 ^ N₀ * Y0 ^ (a0 * T₀)
  have hent : ∀ l l', IsIntegral ℤ (b ^ Es * MK l l') ∧
      NumberField.house (b ^ Es * MK l l') ≤ Bd := by
    intro l l'
    obtain ⟨hi, hh⟩ := hA8 (ro l) (ka l) (sv l) (fun h => (l'.1 h : ℕ)) (tt l')
    have hτ : ∑ h, (l'.1 h : ℕ) ≤ a0 * T₀ := by
      calc _ ≤ ∑ _h : ι₀, T₀ := Finset.sum_le_sum fun h _ => Nat.lt_succ_iff.mp (l'.1 h).isLt
        _ = a0 * T₀ := by simp [a0]
    have ht : ∑ i, (tt l' i).natAbs ≤ a1 * T₁ := by
      calc _ ≤ ∑ _i : ι₁, T₁ := Finset.sum_le_sum fun i _ => by
            have := (l'.2 i).isLt; simp only [tt]; omega
        _ = a1 * T₁ := by simp [a1]
    have hs : ∑ j, (sv l j).natAbs ≤ k1 * N₁ := by
      calc _ ≤ ∑ _j : κ₁, N₁ := Finset.sum_le_sum fun j _ => by
            have := hsv l j
            have e := Int.natCast_natAbs (sv l j)
            omega
        _ = k1 * N₁ := by simp [k1]
    have hE : ro l + ∑ h, (l'.1 h : ℕ) + (∑ i, (tt l' i).natAbs) * ∑ j, (sv l j).natAbs ≤ Es :=
      add_le_add (add_le_add (hro l) hτ) (Nat.mul_le_mul ht hs)
    have e : b ^ Es * MK l l' = b ^ (Es - (ro l + ∑ h, (l'.1 h : ℕ)
        + (∑ i, (tt l' i).natAbs) * ∑ j, (sv l j).natAbs)) * (b ^ (ro l + ∑ h, (l'.1 h : ℕ)
        + (∑ i, (tt l' i).natAbs) * ∑ j, (sv l j).natAbs) * MK l l') := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hE]
    rw [e]
    refine ⟨(hb.pow _).mul hi, ?_⟩
    refine (NumberField.house_mul_le _ _).trans ?_
    have hXl : (((∑ h, (l'.1 h : ℕ) : ℕ) : ℝ) + ((∑ i, (tt l' i).natAbs : ℕ) : ℝ) + 1) ≤ X0 := by
      simp only [X0]; exact_mod_cast (by omega : _ + _ + 1 ≤ a0 * T₀ + a1 * T₁ + 1)
    have hYl : (((∑ j, (sv l j).natAbs : ℕ) : ℝ) + 1) ≤ Y0 := by
      simp only [Y0]; exact_mod_cast (by omega : _ + 1 ≤ k1 * N₁ + 1)
    have hp1 := (NumberField.house_pow_le b (Es - (ro l + ∑ h, (l'.1 h : ℕ)
        + (∑ i, (tt l' i).natAbs) * ∑ j, (sv l j).natAbs))).trans
      (pow_le_pow_left₀ (NumberField.house_nonneg _) hbH _)
    have hp2 := pow_le_pow_left₀ (by positivity) hXl (ro l)
    have hp3 := pow_le_pow_left₀ (by positivity) hYl (∑ h, (l'.1 h : ℕ))
    have hp4 := pow_le_pow_right₀ hX0 (hro l)
    have hp5 := pow_le_pow_right₀ hY0 hτ
    have hp6 := pow_le_pow_left₀ (by linarith) (le_max_left H (NumberField.house b))
      (ro l + ∑ h, (l'.1 h : ℕ) + (∑ i, (tt l' i).natAbs) * ∑ j, (sv l j).natAbs)
    calc _ ≤ H' ^ (Es - (ro l + ∑ h, (l'.1 h : ℕ) + (∑ i, (tt l' i).natAbs) * ∑ j, (sv l j).natAbs))
          * (H' ^ (ro l + ∑ h, (l'.1 h : ℕ) + (∑ i, (tt l' i).natAbs) * ∑ j, (sv l j).natAbs)
            * X0 ^ N₀ * Y0 ^ (a0 * T₀)) := by
          refine mul_le_mul hp1 (hh.trans ?_) (NumberField.house_nonneg _) (by positivity)
          gcongr
          · exact hp2.trans hp4
          · exact hp3.trans hp5
      _ = Bd := by rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hE]
  have hL := det_lower σ hb0 hbH MK Es Bd hent hdet
  have hcard : Fintype.card ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)))
      = (T₀ + 1) ^ a0 * (2 * T₁ + 1) ^ a1 := by simp [Fintype.card_prod, a0, a1]
  rw [hcard] at hL
  set n := (T₀ + 1) ^ a0 * (2 * T₁ + 1) ^ a1 with hn
  have hx : 0 < ‖(σ.mapMatrix MK).det‖ := norm_pos_iff.mpr hdet
  have hH'0 : 0 < H' := by linarith
  have hnf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hBd : 0 < Bd := by positivity
  have hlog := Real.log_le_log one_pos hL
  rw [Real.log_one, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hx.ne',
    Real.log_pow, Real.log_pow, Real.log_mul hnf.ne' (by positivity), Real.log_pow, ← hDmdef] at hlog
  have hfact : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log hnf (by exact_mod_cast Nat.factorial_le_pow n)
  have hlogBd : Real.log Bd = Es * Real.log H' + N₀ * Real.log X0
      + ((a0 * T₀ : ℕ) : ℝ) * Real.log Y0 := by
    simp only [Bd]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hlogBd] at hlog
  push_cast at hlog
  have hRB : (Es : ℝ) * ((1 + Dm) * Real.log H') + Dm * Real.log (n : ℝ)
      + Dm * ((N₀ : ℝ) * Real.log X0 + ((a0 * T₀ : ℕ) : ℝ) * Real.log Y0)
      ≤ C0 * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1)) :=
    real_bound a0 a1 k1 hG hDm T₀ T₁ N₀ N₁ h0 h1
  have hΞ : 0 ≤ (N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
      + (T₁ : ℝ) * ((N₁ : ℝ) + 1) := by
    have : 0 ≤ Real.log ((T₀ : ℝ) + T₁ + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ T₀), (Nat.cast_nonneg _ : (0:ℝ) ≤ T₁)])
    have : 0 ≤ Real.log ((N₁ : ℝ) + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ N₁)])
    positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  push_cast at hRB ⊢
  linarith [mul_le_mul_of_nonneg_left hRB hn0, mul_le_mul_of_nonneg_left hfact hDm,
    mul_nonneg hn0 hΞ]
