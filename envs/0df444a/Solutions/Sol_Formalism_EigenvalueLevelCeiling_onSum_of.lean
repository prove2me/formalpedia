-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.onSum_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:15.025136+00:00
-- url     : https://prove2.me/submissions/0599e3a2-13dd-47a3-8b1b-3eeecbfa851e

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_errGood_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGood) : OnSum := by
  unfold OnSum
  intro K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
    errl herr
  set X : ℕ → ℝ := fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p with hX
  have hX0 : ∀ p, 0 ≤ X p := fun p => by
    simp only [hX]
    split_ifs
    · exact heb p
    · exact errGood_nonneg Y X2 A1 A2 kw T th add hA1 hA2 hkw hT hth hadd p
  have hlw : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ lw w := fun w => by
    unfold lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hram : ∀ w : HeightOneSpectrum (𝓞 K), (0:ℝ) ≤ (ramw w : ℝ) := fun w => by
    have h1 := (hR K w).2.1
    exact_mod_cast (le_trans (by norm_num) h1)
  have step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * X (plc w)) :=
    Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (herr w hw) (hram w)) (hlw w)
  have step2 := hP K S X hX0
  have hsplit := Finset.sum_filter_add_sum_filter_not (S.image plc) (fun p => p ∈ Bad)
    (fun p => Real.log (p : ℝ) * X p)
  have step3 : ∑ p ∈ (S.image plc).filter (fun p => p ∈ Bad), Real.log (p : ℝ) * X p ≤
      ∑ p ∈ Bad, Real.log (p : ℝ) * eb p := by
    calc _ = ∑ p ∈ (S.image plc).filter (fun p => p ∈ Bad), Real.log (p : ℝ) * eb p :=
          Finset.sum_congr rfl fun p hp => by
            rw [Finset.mem_filter] at hp
            simp only [hX, if_pos hp.2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
          (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))
  have step4 : ∑ p ∈ (S.image plc).filter (fun p => p ∉ Bad), Real.log (p : ℝ) * X p ≤
      2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + 1.02 * Y) := by
    have hprime : ∀ p ∈ (S.image plc).filter (fun p => p ∉ Bad), p.Prime := by
      intro p hp
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp).1
      exact (hR K w).1
    calc _ = ∑ p ∈ (S.image plc).filter (fun p => p ∉ Bad),
            Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p :=
          Finset.sum_congr rfl fun p hp => by
            rw [Finset.mem_filter] at hp
            simp only [hX, if_neg hp.2]
      _ ≤ _ := hE _ hprime Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
  linarith
end Formalism.EigenvalueLevelCeiling
