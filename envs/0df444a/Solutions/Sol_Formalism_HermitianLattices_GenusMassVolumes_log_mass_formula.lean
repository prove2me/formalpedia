-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.log_mass_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:45.571043+00:00
-- url     : https://prove2.me/submissions/5ffd3916-8e17-4544-b22f-4bc8bf606fe7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OneAddInvPowLeExpOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma sum_Ico_cast_eq_mul_add_triangular (k j : ℕ) :
    ∑ M ∈ Ico (k + 1) (k + j + 1), (M : ℝ) = (j : ℝ) * k + ((j : ℝ) + 1) * j / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) + 1 = k + j + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    ring
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : LogMassFormula := by
  intro f m k vE massk massr Lval hf hm hk hvE hmk hL hmass
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hI : k - 1 + (j + 1) + 1 = k + j + 1 := by omega
  rw [hI] at hL hmass ⊢
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hpi : 0 < vE / Real.pi := div_pos hvE Real.pi_pos
  have h2v : 0 < 2 * vE := by linarith
  have hs : 0 < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.2 (pow_pos h2v f)
  have hA : ∀ M : ℕ, 0 < (((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M := fun M =>
    mul_pos (by exact_mod_cast Nat.factorial_pos _) (pow_pos hpi M)
  have hpos : ∀ M ∈ Finset.Ico (k + 1) (k + j + 1),
      0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M :=
    fun M hM => mul_pos (div_pos (pow_pos (hA M) f) hs) (hL M hM)
  have hterm : ∀ M ∈ Finset.Ico (k + 1) (k + j + 1),
      Real.log (((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) =
        f * Real.log (((M - 1).factorial : ℕ) : ℝ) + f * Real.log (vE / Real.pi) * (M : ℝ)
          - f / 2 * Real.log (2 * vE) + Real.log (Lval M) := by
    intro M hM
    have hfac : (0:ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [Real.log_mul (div_pos (pow_pos (hA M) f) hs).ne' (hL M hM).ne',
      Real.log_div (pow_pos (hA M) f).ne' hs.ne', Real.log_pow, Real.log_mul hfac.ne' (pow_pos hpi M).ne',
      Real.log_pow, Real.log_sqrt (pow_pos h2v f).le, Real.log_pow]
    ring
  have hprod : massr / massk = ∏ M ∈ Finset.Ico (k + 1) (k + j + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M := by
    rw [hmass, mul_div_cancel_left₀ _ hmk.ne']
  have hc : (Finset.Ico (k + 1) (k + j + 1)).card = j := by rw [Nat.card_Ico]; omega
  rw [hprod, Real.log_prod (fun M hM => (hpos M hM).ne'), Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, hc, nsmul_eq_mul, sum_Ico_cast_eq_mul_add_triangular]
  push_cast
  field_simp
  ring
end Formalism.HermitianLattices.GenusMassVolumes
