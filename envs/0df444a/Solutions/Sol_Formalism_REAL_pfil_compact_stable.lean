-- Prove2me | solution 1 for Formalism.REAL.pfil_compact_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:24.117711+00:00
-- url     : https://prove2.me/submissions/dd448c7f-d606-4efd-89b0-7fa7cfa53285

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_pfil_monotone_in_length
import Theorems.Thm_Formalism_REAL_compact_generator_word_mem_pfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (hE : GlRel E) (j : ℕ) : KStable ε E (pfil ε E u j) := by
  intro a b hab x hx
  have key : pfil ε E u j ≤ (pfil ε E u j).comap (E a b) :=
    Submodule.span_le.mpr (by
      rintro z ⟨w, hw, hnc, y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      exact pfil_monotone_in_length ε E u hw (compact_generator_word_mem_pfil ε E u hE a b hab y hy w hnc))
  exact key hx
end Formalism.REAL
