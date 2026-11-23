-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digitDoubleCount_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:13.887776+00:00
-- url     : https://prove2.me/submissions/b18fc5da-20d9-438c-a7be-817aad6d2779

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (h : DigitVectorsCount) : DigitDoubleCount := by
  intro s m P I R _ M hP
  have hswap : ∑ ρ : DigitVec s m P,
      (((Fintype.piFinset fun _ : Fin (s+1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ) =
      ∑ aa ∈ Fintype.piFinset (fun _ : Fin (s+1) => I),
        ((((univ : Finset (DigitVec s m P)).filter (fun ρ => DigitCompat ρ aa)).card : ℕ) : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_comm
  have hcount : ∀ aa : Fin (s+1) → ℕ,
      ((((univ : Finset (DigitVec s m P)).filter (fun ρ => DigitCompat ρ aa)).card : ℕ) : ℝ) =
        ((∏ i, P i ^ m : ℕ) : ℝ) := fun aa => by rw [h s m P aa hP]
  have hsplit : (∑ ρ : DigitVec s m P, ∑ q : R,
      (((Fintype.piFinset fun _ : Fin (s + 1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ) * M q) =
      (∑ ρ : DigitVec s m P,
        (((Fintype.piFinset fun _ : Fin (s + 1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ)) *
        ∑ q : R, M q := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [hsplit, hswap, Finset.sum_congr rfl (fun aa _ => hcount aa), Finset.sum_const,
    Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end Formalism.CountingSumsFrames
