-- Prove2me | solution 1 for CuspForm.exists_differentiable_eq_lSeries_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T21:41:22.46226+00:00
-- url     : https://prove2.me/submissions/0965d476-e539-4b40-8297-85b3fa28ceff

import Definitions.Def_FLTPrelim_Modularity
import Mathlib

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Matrix

/-- Hecke's theorem for weight-two cusp forms on `Γ₀(N)`.

Mathlib already contains the analytic continuation: `ModularForm.L hk f` is defined for every
modular form via the Mellin transform of the associated `WeakFEPair`, is entire when `f` is a
cusp form (`CuspForm.differentiable_L`), and satisfies the Dirichlet-series expansion
`CuspForm.hasSum_L : k / 2 + 1 < s.re → HasSum (fun n ↦ (qExpansion (width Γ) f).coeff n / n ^ s)
  (width Γ ^ (-s) * L hk f s)`.

For `k = 2` the condition `k / 2 + 1 < s.re` is exactly `2 < s.re`, and the width of `Γ₀(N)` at
the cusp `∞` is `1` (`CongruenceSubgroup.strictWidthInfty_Gamma0`), so the coefficients appearing
there are literally `ModularFormClass.qCoeff f n = (UpperHalfPlane.qExpansion 1 f).coeff n`. -/
theorem solution {N : ℕ} (hN : 0 < N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, 2 < s.re → Λ s = LSeries (ModularFormClass.qCoeff f) s := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hk : (0 : ℤ) < 2 := by norm_num
  refine ⟨ModularForm.L hk f,
    CuspForm.differentiable_L
      (Γ := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (hk := hk) (f := f), ?_⟩
  intro s hs
  -- `2 < s.re` forces `s ≠ 0`
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Complex.zero_re] at hs
    linarith
  -- the hypothesis of `CuspForm.hasSum_L`, specialised to `k = 2`
  have hsre : ((2 : ℤ) : ℝ) / 2 + 1 < s.re := by
    have h2 : ((2 : ℤ) : ℝ) / 2 + 1 = 2 := by norm_num
    rw [h2]
    exact hs
  have key := CuspForm.hasSum_L
    (Γ := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (hk := hk) (f := f) (hs := hsre)
  -- the width of `Γ₀(N)` at `∞` is `1`
  have hw : Subgroup.strictWidthInfty
      ((CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) = 1 :=
    CongruenceSubgroup.strictWidthInfty_Gamma0 N
  rw [hw] at key
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at key
  -- `qCoeff` is by definition the coefficient of the `q`-expansion of width `1`
  have hq : ∀ n : ℕ, ModularFormClass.qCoeff f n
      = (UpperHalfPlane.qExpansion 1 f).coeff n := by
    intro n
    first
      | rfl
      | simp [ModularFormClass.qCoeff]
      | simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion]
  have hfun : LSeries.term (ModularFormClass.qCoeff f) s
      = fun n : ℕ => (UpperHalfPlane.qExpansion 1 f).coeff n / (n : ℂ) ^ s := by
    funext n
    rw [LSeries.term_of_ne_zero' hs0, hq n]
  have hterm : HasSum (LSeries.term (ModularFormClass.qCoeff f) s)
      (ModularForm.L hk f s) := by
    rw [hfun]
    exact key
  have hsum : LSeriesHasSum (ModularFormClass.qCoeff f) s (ModularForm.L hk f s) := hterm
  exact hsum.LSeries_eq.symm

end