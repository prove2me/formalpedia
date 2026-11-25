-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_gateTerm_mul_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:58.093542+00:00
-- url     : https://prove2.me/submissions/09e31c88-7db9-44bc-ac44-b87af608f0a0

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_h_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_eight_lt_lJ
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_floor_h_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_toNat_xlo_sub_maxB_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_gatedPrimeSum_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) :
    ∑ l ∈ R, gatedCoefficientTerm D P τ l * Real.log (l : ℝ) ≤
      (D.q τ : ℝ) * P.h * (1 + Real.log P.h) * Real.log P.h := by
  obtain ⟨e, h1, h2⟩ := toNat_xlo_sub_maxB_bounds H hT hτ
  obtain ⟨f1, f2, f3, f4, f5⟩ := floor_h_bounds H G
  obtain ⟨c1, _⟩ := log_h_bounds H G
  have hJ8 := eight_lt_lJ H G
  have hA0 : 0 ≤ (D.q τ : ℝ) * P.h := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hk0 : 0 ≤ min (P.k : ℝ) (P.t : ℝ) := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have key := Formalism.CohomologicalDescent.gatedPrimeSum_holds (D.xlo τ - D.maxB τ).toNat ⌊P.h⌋₊ P.lJ ((D.q τ : ℝ) * P.h)
    (min (P.k : ℝ) (P.t : ℝ)) R h1 h2 hA0 hk0 f3 (by linarith)
    (fun l hl => ⟨(hR l hl).1, (hR l hl).2.1⟩)
  rw [e] at key
  have key2 : ∑ l ∈ R, gatedCoefficientTerm D P τ l * Real.log (l : ℝ) ≤
      (D.q τ : ℝ) * P.h * (1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ) := key
  have hm : (1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ) ≤ (1 + Real.log P.h) * Real.log P.h :=
    mul_le_mul (by linarith) f5 f4 (by linarith)
  calc ∑ l ∈ R, gatedCoefficientTerm D P τ l * Real.log (l : ℝ)
      ≤ (D.q τ : ℝ) * P.h * (1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ) := key2
    _ = (D.q τ : ℝ) * P.h * ((1 + Real.log (⌊P.h⌋₊ : ℝ)) * Real.log (⌊P.h⌋₊ : ℝ)) := by ring
    _ ≤ (D.q τ : ℝ) * P.h * ((1 + Real.log P.h) * Real.log P.h) := mul_le_mul_of_nonneg_left hm hA0
    _ = (D.q τ : ℝ) * P.h * (1 + Real.log P.h) * Real.log P.h := by ring
end Formalism.CohomologicalDescent.LogSmallConstantBounds
