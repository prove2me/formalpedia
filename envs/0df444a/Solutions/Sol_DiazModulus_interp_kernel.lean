-- Prove2me | solution 1 for DiazModulus.interp_kernel
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:14:38.260997+00:00
-- url     : https://prove2.me/submissions/f78b5097-cc86-4cf4-ae33-5df0ce1c6343

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_thetaN_ge_mul_sub
import Theorems.Thm_DiazModulus_interp_det_upper
import Theorems.Thm_DiazModulus_interp_det_liouville
import Theorems.Thm_DiazModulus_exists_ne_zero_mulVec_eq_zero_of_minors

open Complex ComplexConjugate

/-! # The interpolation kernel (Steps 3–5 of the C1.4 route)

Index the rows by the finite box `ρ` of row data `(r, k, s)` with `r ≤ N₀`, `k : Fin r → κ₀` and
`|s_j| ≤ N₁`, and the columns by the coefficient box (`L` of them). Let `M` be the matrix whose
entries are the summands of the conclusion. If some maximal minor `M.submatrix f id` had a nonzero
determinant `Δ`, then `interp_det_liouville` (A10) gives `log ‖Δ‖ ≥ −C₁₀·L·Ξ` and
`interp_det_upper` (A9) gives `‖Δ‖ ≤ exp(−(Θₙ(L) − L·N₀) + C₉·L·Ξ)`, with `n = dim V`. Hence
`Θₙ(L) ≤ L·N₀ + (C₉+C₁₀)·L·Ξ`. With `A = ⌊L^{1/n}/2⌋` we have `2Aⁿ ≤ L`, so `thetaN_ge_mul_sub`
(A1) gives `A·L ≤ 2Θₙ(L)`; since `N₀ ≤ Ξ` and `1 ≤ Ξ`, the hypothesis `C·Ξ ≤ L^{1/n}` with
`C = 8 + 4(C₉+C₁₀)` makes this impossible. So every maximal minor vanishes, and
`exists_ne_zero_mulVec_eq_zero_of_minors` (A11) gives a nonzero kernel vector `c`, which is the
conclusion row by row. -/

namespace C14_kernel
open DiazModulus

/-- The entry of the interpolation matrix in row data `(r, k, s)` and column `l`. -/
noncomputable def entry {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (T₀ T₁ : ℕ)
    (r : ℕ) (k : Fin r → κ₀) (s : κ₁ → ℤ) (l : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) : ℂ :=
  MvPolynomial.eval (∑ j, ((s j : ℤ) : ℂ) • (fun j => (η j).1) j)
    ((List.ofFn fun k' : Fin r =>
      ((∑ h, (w (k k')).1 h • (MvPolynomial.pderiv h).toLinearMap
        + (∑ i, (w (k k')).2 i * (((l.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
          Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
      (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
  * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ s j) ^ (((l.2 i : ℕ) : ℤ) - T₁)

/-- `Ξ ≥ 1` and `N₀ ≤ Ξ`. -/
lemma xi_facts (T₀ T₁ N₀ N₁ : ℕ) (hT₀ : 1 ≤ T₀) (hT₁ : 1 ≤ T₁) :
    1 ≤ (N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1) ∧
    (N₀ : ℝ) ≤ (N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1) := by
  have hT₀' : (1 : ℝ) ≤ T₀ := by exact_mod_cast hT₀
  have hT₁' : (1 : ℝ) ≤ T₁ := by exact_mod_cast hT₁
  have hl1 : 1 ≤ Real.log ((T₀ : ℝ) + T₁ + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hl2 : 0 ≤ Real.log ((N₁ : ℝ) + 2) := Real.log_nonneg (by linarith [N₁.cast_nonneg (α := ℝ)])
  have hN₀ : (0 : ℝ) ≤ N₀ := N₀.cast_nonneg
  have hN₁ : (0 : ℝ) ≤ N₁ := N₁.cast_nonneg
  have h1 : (N₀ : ℝ) ≤ N₀ * Real.log ((T₀ : ℝ) + T₁ + 2) := by nlinarith
  have h2 : 0 ≤ (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2) := by positivity
  have h3 : 1 ≤ (T₁ : ℝ) * ((N₁ : ℝ) + 1) := by nlinarith
  constructor <;> nlinarith

/-- The arithmetic contradiction of Step 5. -/
lemma no_large_theta (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) (Ξ N₀ C' : ℝ) (hΞ : 1 ≤ Ξ)
    (hN₀ : N₀ ≤ Ξ) (_hC' : 0 ≤ C') (hcon : (8 + 4 * C') * Ξ ≤ (L : ℝ) ^ ((1 : ℝ) / n))
    (hΘ : ((sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧
        S = ∑ l, ∑ i, κ' l i} : ℕ) : ℝ) ≤ L * N₀ + C' * L * Ξ) : False := by
  set Θ := sInf {S | ∃ κ' : Fin L → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i}
  set y : ℝ := (L : ℝ) ^ ((1 : ℝ) / n) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyn : y ^ n = L := by
    rw [hy, one_div]; exact Real.rpow_inv_natCast_pow L.cast_nonneg (by omega)
  set A := ⌊y / 2⌋₊ with hA
  have hA1 : (A : ℝ) ≤ y / 2 := Nat.floor_le (by positivity)
  have hA2 : y / 2 - 1 < A := Nat.sub_one_lt_floor _
  have hAn : 2 * A ^ n ≤ L := by
    have h1 : (A : ℝ) ^ n ≤ (y / 2) ^ n := pow_le_pow_left₀ A.cast_nonneg hA1 n
    have h2 : (y / 2) ^ n = L / 2 ^ n := by rw [div_pow, hyn]
    have h3 : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h4 : (L : ℝ) / 2 ^ n ≤ L / 2 := div_le_div_of_nonneg_left L.cast_nonneg (by norm_num) h3
    have : (2 * A ^ n : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hθ : A * L ≤ 2 * Θ := by
    have := thetaN_ge_mul_sub n L A hn
    have h5 : L ≤ 2 * (L - A ^ n) := by omega
    calc A * L ≤ A * (2 * (L - A ^ n)) := Nat.mul_le_mul_left _ h5
      _ = 2 * (A * (L - A ^ n)) := by ring
      _ ≤ 2 * Θ := Nat.mul_le_mul_left _ this
  have hθ' : (A : ℝ) * L ≤ 2 * Θ := by exact_mod_cast hθ
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have h6 : (A : ℝ) * L ≤ L * (2 * (1 + C') * Ξ) := by nlinarith
  have h7 : (A : ℝ) ≤ 2 * (1 + C') * Ξ := by
    exact le_of_mul_le_mul_left (by linarith [h6]) hLpos
  nlinarith

end C14_kernel

open DiazModulus C14_kernel in
theorem solution {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (V : Submodule ℂ ((ι₀ → ℂ) × (ι₁ → ℂ))) (hV : 1 ≤ Module.finrank ℂ ↥V)
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwV : ∀ k, w k ∈ V) (hwalg : ∀ k, (∀ h, (w k).1 h ∈ Qbar) ∧ ∀ i, (w k).2 i ∈ Qbar)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηV : ∀ j, η j ∈ V) (hηalg : ∀ j, (∀ h, (η j).1 h ∈ Qbar) ∧ ∀ i, (η j).2 i ∈ LogAlg) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ T₁ N₀ N₁ : ℕ, 1 ≤ T₀ → 1 ≤ T₁ →
      C * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1))
        ≤ (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℂ ↥V) →
      ∃ c : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℂ, c ≠ 0 ∧
        ∀ (rₑ : ℕ) (kₑ : Fin rₑ → κ₀) (sₑ : κ₁ → ℤ), rₑ ≤ N₀ → (∀ j, |sₑ j| ≤ ((N₁ : ℕ) : ℤ)) →
        ∑ l, c l * (MvPolynomial.eval (∑ j, ((sₑ j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin rₑ =>
            ((∑ h, (w (kₑ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (kₑ k)).2 i * (((l.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ sₑ j) ^ (((l.2 i : ℕ) : ℤ) - T₁)) = 0 := by
  obtain ⟨C₉, hC₉, h9⟩ := DiazModulus.interp_det_upper V w hwV η hηV
  obtain ⟨C₁₀, hC₁₀, h10⟩ := DiazModulus.interp_det_liouville w hwalg η hηalg
  refine ⟨8 + 4 * (C₉ + C₁₀), by positivity, ?_⟩
  intro T₀ T₁ N₀ N₁ hT₀ hT₁ hcon
  classical
  let ρ := Σ r : Fin (N₀ + 1), (Fin r → κ₀) × (κ₁ → Fin (2 * N₁ + 1))
  let sv : ρ → κ₁ → ℤ := fun x j => ((x.2.2 j : ℕ) : ℤ) - N₁
  let M : Matrix ρ ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) ℂ :=
    Matrix.of fun x l => entry w η T₀ T₁ x.1.val x.2.1 (sv x) l
  have hsv : ∀ x j, |sv x j| ≤ (N₁ : ℤ) := by
    intro x j
    have := (x.2.2 j).isLt
    simp only [sv, abs_le]; omega
  obtain ⟨hΞ1, hΞN⟩ := xi_facts T₀ T₁ N₀ N₁ hT₀ hT₁
  have hminors : ∀ f : ((ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → ρ,
      (M.submatrix f id).det = 0 := by
    intro f
    by_contra hne
    have hro : ∀ l, (f l).1.val ≤ N₀ := fun l => Nat.lt_succ_iff.mp (f l).1.isLt
    have u := h9 T₀ T₁ N₀ N₁ hT₀ hT₁ (fun l => (f l).1.val) (fun l => (f l).2.1)
      (fun l => sv (f l)) hro (fun l j => hsv (f l) j)
    have lo := h10 T₀ T₁ N₀ N₁ hT₀ hT₁ (fun l => (f l).1.val) (fun l => (f l).2.1)
      (fun l => sv (f l)) hro (fun l j => hsv (f l) j) hne
    change ‖(M.submatrix f id).det‖ ≤ _ at u
    change _ ≤ Real.log ‖(M.submatrix f id).det‖ at lo
    have hpos : 0 < ‖(M.submatrix f id).det‖ := norm_pos_iff.mpr hne
    rw [← Real.log_le_iff_le_exp hpos] at u
    have hL : 1 ≤ (T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    refine no_large_theta _ _ hV hL _ _ (C₉ + C₁₀) hΞ1 hΞN (by positivity) hcon ?_
    nlinarith
  obtain ⟨c, hc0, hc⟩ := DiazModulus.exists_ne_zero_mulVec_eq_zero_of_minors M hminors
  refine ⟨c, hc0, ?_⟩
  intro rₑ kₑ sₑ hr hs
  let x : ρ := ⟨⟨rₑ, by omega⟩, kₑ, fun j => ⟨(sₑ j + N₁).toNat, by
    have := hs j; rw [abs_le] at this; omega⟩⟩
  have hsx : sv x = sₑ := by
    funext j
    have := hs j; rw [abs_le] at this
    simp only [sv, x]; omega
  have := congrFun hc x
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply] at this
  rw [hsx] at this
  change ∑ l, c l * entry w η T₀ T₁ rₑ kₑ sₑ l = 0
  rw [← this]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _
