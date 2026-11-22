-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.pderiv_inr_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:30.418193+00:00
-- url     : https://prove2.me/submissions/d5339805-b904-45e0-9f50-98f3b8feb365

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_monomial_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_lin_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_xDeg_add
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_yDeg_add
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_xDeg_inr
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_yDeg_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem xDeg_yDeg_sub_single_add_single (m : XY k →₀ ℕ) (v : XY k) (hv : 1 ≤ m v) :
    xDeg (m - Finsupp.single v 1) + xDeg (Finsupp.single v 1) = xDeg m ∧
    yDeg (m - Finsupp.single v 1) + yDeg (Finsupp.single v 1) = yDeg m := by
  have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.2 hv
  rw [← xDeg_add, ← yDeg_add, tsub_add_cancel_of_le hle]
  exact ⟨rfl, rfl⟩
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution {A B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    pderiv (Sum.inr i) f ∈ PolAB K k A (B - 1) := by
  have key := lin_mem (A := A) (B := B) (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap
    (PolAB K k A (B - 1)) (fun m c hx hy => by
      change pderiv (Sum.inr i) (monomial m c) ∈ PolAB K k A (B - 1)
      rw [pderiv_monomial]
      by_cases h0 : m (Sum.inr i) = 0
      · rw [h0, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
      · obtain ⟨h1, h2⟩ := xDeg_yDeg_sub_single_add_single m (Sum.inr i) (Nat.one_le_iff_ne_zero.2 h0)
        rw [xDeg_inr] at h1; rw [yDeg_inr] at h2
        exact monomial_mem _ (by omega) (by omega)) hf
  exact key
end Formalism.CountingSumsFrames.Har2
