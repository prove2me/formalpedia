-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.absNorm_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:03.524817+00:00
-- url     : https://prove2.me/submissions/560e9a75-0538-49c9-b101-550abf946ee0

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_absNorm_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution (P : Ideal (𝓞 K)) [hP : P.IsMaximal] {l : ℕ} (hl : l.Prime) (hlP : (l : 𝓞 K) ∈ P) :
    Ideal.absNorm P ∣ l ^ Module.finrank ℚ K ∧ l ≤ Ideal.absNorm P := by
  have hle : Ideal.span {(l : 𝓞 K)} ≤ P := by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hlP
  have hd : Ideal.absNorm P ∣ l ^ Module.finrank ℚ K := by
    rw [← absNorm_nat]; exact Ideal.absNorm_dvd_absNorm_of_le hle
  refine ⟨hd, ?_⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).1 hd
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  rw [hk] at h1 ⊢
  rcases k with _ | k
  · simp at h1
  · calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ (k + 1) := Nat.pow_le_pow_right hl.pos (by omega)
end Formalism.MainNotions.MassRatioZetaBound
