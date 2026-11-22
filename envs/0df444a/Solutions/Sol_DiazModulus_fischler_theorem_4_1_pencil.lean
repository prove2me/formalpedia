-- Prove2me | solution 1 for DiazModulus.fischler_theorem_4_1_pencil
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T08:58:00.652673+00:00
-- url     : https://prove2.me/submissions/18567cca-89ab-4eaa-979c-54c8e42efb6b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_prop_3_1_pencil

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 4.1 in pencil form

Write `M_α` for the `d × l` matrix with columns `F_a α`, `r = rk M_x`, and suppose `x` lies in no hyperplane
defined over `Q̄`. The pencil form of Proposition 3.1 gives `S ⊂ ℂˡ`, `T ⊂ ℂᵈ` of codimensions `l₁, d₁ ≥ 1` with
`(Σ s_a F_a)(ℂᵈ) ⊂ T` for `s ∈ S`, and `r₁ ≥ 1` with `r₁d < rd₁` and `l₁d₁ ≤ r₁(l₁ + d₁)`. Since
`M_α s = (Σ s_a F_a)α`, `M_α` maps `S` into `T`, and rank–nullity (split `ℂˡ = S ⊕ S'`) gives
`d₁ ≤ l₁ + (d − rk M_α) ≤ l₁ + k − 1`. From `kr ≤ d`: `kr₁r ≤ r₁d < rd₁`, so `kr₁ < d₁`. Multiplying
`r₁d < rd₁` by `l₁ + d₁` and using `l₁d₁ ≤ r₁(l₁ + d₁)` gives `dl₁ < r(l₁ + d₁)`, so `kl₁ < l₁ + d₁`. If
`l₁ = 1` then `k ≤ kr₁ < d₁ ≤ k`. If `l₁ ≥ 2`, then `kl₁ < l₁ + d₁ ≤ 2l₁ + k − 1` forces `k = 2`; then
`d₁ = l₁ + 1` and `2r₁ ≤ l₁`, and `l₁(l₁ + 1) ≤ r₁(2l₁ + 1) ≤ l₁(2l₁ + 1)/2` fails. So `x` lies in a hyperplane
defined over `Q̄`. -/

namespace RC10_Th41P
open DiazModulus

/-- The columns of `M_α` are the `F_a α`, so `M_α s = (Σ s_a F_a) α`. -/
theorem pencil_mulVec {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ) (α : Fin d → ℂ)
    (s : Fin l → ℂ) :
    (Matrix.of fun i a => ((F a).mulVec α) i).mulVec s = (∑ a, s a • F a).mulVec α := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

/-- Rank–nullity for a matrix mapping `S` into `T`: `dim S + rk M ≤ dim T + l`. -/
theorem finrank_add_rank_le {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ))
    (h : ∀ s ∈ S, M.mulVec s ∈ T) :
    Module.finrank ℂ S + M.rank ≤ Module.finrank ℂ T + l := by
  obtain ⟨S', hS'⟩ := Submodule.exists_isCompl S
  have hc := Submodule.finrank_add_eq_of_isCompl hS'
  have hrange : LinearMap.range M.mulVecLin = S.map M.mulVecLin ⊔ S'.map M.mulVecLin := by
    rw [LinearMap.range_eq_map, ← Submodule.map_sup, hS'.sup_eq_top]
  have h1 : Module.finrank ℂ (S.map M.mulVecLin) ≤ Module.finrank ℂ T :=
    Submodule.finrank_mono (Submodule.map_le_iff_le_comap.2 fun s hs => h s hs)
  have h2 := Submodule.finrank_map_le M.mulVecLin S'
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (S.map M.mulVecLin) (S'.map M.mulVecLin)
  have hl : Module.finrank ℂ (Fin l → ℂ) = l := Module.finrank_fin_fun ℂ
  rw [Matrix.rank, hrange]
  omega

/-- The arithmetic of the printed proof, cleared to `ℕ`. -/
theorem arith {d k r r₁ l₁ d₁ : ℕ} (hk : 2 ≤ k) (hl₁ : 1 ≤ l₁) (hr₁ : 1 ≤ r₁)
    (h2 : r₁ * d < r * d₁) (h3 : l₁ * d₁ ≤ r₁ * (l₁ + d₁)) (hrk : k * r ≤ d)
    (hdl : d₁ + 1 ≤ l₁ + k) : False := by
  -- `k r₁ < d₁`
  have hA : k * r₁ < d₁ := by
    have : r * (k * r₁) < r * d₁ := by nlinarith [Nat.mul_le_mul_right r₁ hrk]
    exact Nat.lt_of_mul_lt_mul_left this
  -- `d l₁ < r (l₁ + d₁)`
  have hB : d * l₁ < r * (l₁ + d₁) := by
    have hpos : 0 < l₁ + d₁ := by omega
    have e1 : r₁ * d * (l₁ + d₁) < r * d₁ * (l₁ + d₁) := Nat.mul_lt_mul_of_pos_right h2 hpos
    have e2 : d * (l₁ * d₁) ≤ d * (r₁ * (l₁ + d₁)) := Nat.mul_le_mul_left d h3
    have : d₁ * (d * l₁) < d₁ * (r * (l₁ + d₁)) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  -- `k l₁ < l₁ + d₁`
  have hC : k * l₁ < l₁ + d₁ := by
    have : r * (k * l₁) < r * (l₁ + d₁) := by nlinarith [Nat.mul_le_mul_right l₁ hrk]
    exact Nat.lt_of_mul_lt_mul_left this
  rcases Nat.lt_or_ge l₁ 2 with hl | hl
  · have : l₁ = 1 := by omega
    subst this
    nlinarith
  · have hk2 : k = 2 := by
      by_contra hne
      have : 3 ≤ k := by omega
      nlinarith [Nat.mul_le_mul this hl]
    subst hk2
    have hd₁ : d₁ = l₁ + 1 := by omega
    subst hd₁
    nlinarith

end RC10_Th41P

open DiazModulus RC10_Th41P in
theorem solution {d l k : ℕ} (hk : 2 ≤ k) (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (hinj : LinearIndependent (↥Qbar) F)
    (hfix : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → (∀ a, Matrix.vecMul φ (F a) = 0) → φ = 0)
    (α : Fin d → ℂ) (hα : d < (Matrix.of fun i a => ((F a).mulVec α) i).rank + k)
    (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde)
    (hr : (d + l) * (Matrix.of fun i a => ((F a).mulVec x) i).rank < d * l)
    (hrk : k * (Matrix.of fun i a => ((F a).mulVec x) i).rank ≤ d) :
    ∃ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) ∧ φ ≠ 0 ∧ φ ⬝ᵥ x = 0 := by
  by_contra hcon
  have hhyp : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → φ ⬝ᵥ x = 0 → φ = 0 := fun φ hφ h0 =>
    by_contra fun hne => hcon ⟨φ, hφ, hne, h0⟩
  obtain ⟨S, T, r₁, hl₁, hd₁, hST, hr₁, h2, h3⟩ :=
    DiazModulus.fischler_prop_3_1_pencil F hF hinj hfix x hx hhyp hr
  have hle := Matrix.rank_le_card_height (Matrix.of fun i a => ((F a).mulVec α) i)
  simp only [Fintype.card_fin] at hle
  have key := finrank_add_rank_le (Matrix.of fun i a => ((F a).mulVec α) i) S T
    (fun s hs => by rw [pencil_mulVec]; exact hST s hs α)
  have hS : Module.finrank ℂ S ≤ l := by
    simpa using Submodule.finrank_le S
  have hT : Module.finrank ℂ T ≤ d := by
    simpa using Submodule.finrank_le T
  generalize (Matrix.of fun i a => ((F a).mulVec α) i).rank = ρ at hα hle key
  generalize (Matrix.of fun i a => ((F a).mulVec x) i).rank = r at hrk h2
  generalize hL : l - Module.finrank ℂ S = l₁ at hl₁ h3
  generalize hD : d - Module.finrank ℂ T = d₁ at hd₁ h2 h3
  exact arith hk hl₁ hr₁ h2 h3 hrk (by omega)
