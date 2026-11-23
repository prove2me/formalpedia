-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_locS_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:47.306061+00:00
-- url     : https://prove2.me/submissions/985f6525-e9a8-407c-a8cc-bc0e84c800ba

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS


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
theorem _root_.solution {S T : Submonoid R} (hTS : T ≤ S) {L M : Submodule R (Fin d → K)}
    (h : locS T L = locS T M) : locS S L = locS S M := by
  have key : ∀ N : Submodule R (Fin d → K), locS S N = locS S (locS T N) := by
    intro N
    apply le_antisymm
    · exact locBasic_locS_mono S (locBasic_le_locS T N)
    · intro x hx
      obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
      obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp hsx
      exact locBasic_mem_locS.mpr ⟨t * s, S.mul_mem (hTS ht) hs, by rwa [mul_smul]⟩
  rw [key L, key M, h]
end Formalism.DivisionValues
