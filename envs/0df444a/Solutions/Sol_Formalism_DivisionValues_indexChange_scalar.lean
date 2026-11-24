-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:23.45548+00:00
-- url     : https://prove2.me/submissions/15fde5bc-02fd-42c8-bb63-3c4c869070b0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_nonneg
import Theorems.Thm_Formalism_DivisionValues_indexChange_cancel
import Theorems.Thm_Formalism_DivisionValues_indexChange_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (v : HeightOneSpectrum R) (i : Fin d) {x : K} (hx : x ≠ 0) :
    IdxChangeP v (idxChangeDg i x) := by
  have hinj := IsFractionRing.injective R K
  have hne : ∀ b : R, b ≠ 0 → algebraMap R K b ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).mpr hb
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp
  have hP : ∀ c : R, c ≠ 0 → IdxChangeP v (idxChangeDg i (algebraMap R K c)) := fun c hc =>
    indexChange_integral v i _ c hc (Int.toNat_of_nonneg (idxChange_cnt_nonneg v c)).symm
  have Pbx : IdxChangeP v
      (idxChangeDg i (algebraMap R K b * (algebraMap R K a / algebraMap R K b))) := by
    rw [mul_div_cancel₀ _ (hne b hb0)]; exact hP a ha0
  exact indexChange_cancel v i (hne b hb0) hx (hP b hb0) Pbx
end Formalism.DivisionValues
