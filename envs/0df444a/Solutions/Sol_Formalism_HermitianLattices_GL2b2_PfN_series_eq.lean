-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.series_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:29.271343+00:00
-- url     : https://prove2.me/submissions/06549a19-ad50-41ce-82cf-c4cd205c1d71

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_chi8_value_shift
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_v4
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution (s : ℂ) (hs : 1 < s.re) :
    DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 s = ∑' k, tt k s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re ZeroFreeRegionGL2.chi8 hs
  unfold LSeriesSummable at hsum
  unfold LSeries
  rw [← (Nat.divModEquiv 8).symm.tsum_eq]
  have hsum' := (Nat.divModEquiv 8).symm.summable_iff.2 hsum
  have h3 : ∑' c : ℕ × Fin 8, LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s
      ((Nat.divModEquiv 8).symm c) = ∑' k : ℕ, ∑' j : Fin 8,
        LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s ((Nat.divModEquiv 8).symm (k, j)) :=
    hsum'.tsum_prod
  rw [h3]
  congr 1
  ext k
  rw [tsum_fintype, Fin.sum_univ_eight]
  have hf0 : (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) 0 = 0 := by
    have := chi8_value_shift 0 0
    simp only [zero_mul, add_zero] at this
    show ZeroFreeRegionGL2.chi8 ((0 : ℕ) : ZMod 8) = 0
    rw [this]
    have : ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 := by decide
    rw [this]; simp
  have hterm : ∀ j : ℕ, LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + j) =
      ((ZMod.χ₈ (j : ZMod 8) : ℤ) : ℂ) * ((8 * (k : ℝ) + (j : ℝ) : ℝ) : ℂ) ^ (-s) := by
    intro j
    rw [LSeries.term_def₀ hf0, chi8_value_shift]
    congr 2
    push_cast; ring
  show LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 0) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 1) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 2) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 3) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 4) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 5) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 6) +
    LSeries.term (fun n : ℕ => ZeroFreeRegionGL2.chi8 (n : ZMod 8)) s (k * 8 + 7) = tt k s
  rw [hterm 0, hterm 1, hterm 2, hterm 3, hterm 4, hterm 5, hterm 6, hterm 7]
  have v0 : ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 := by decide
  have v1 : ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 := by decide
  have v2 : ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0 := by decide
  have v3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 := by decide
  have v4 : ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0 := by decide
  have v5 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
  have v6 : ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0 := by decide
  have v7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 := by decide
  rw [v0, v1, v2, v3, v4, v5, v6, v7]
  unfold tt
  push_cast
  ring
end Formalism.HermitianLattices.GL2b2.PfN
