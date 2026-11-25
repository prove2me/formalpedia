-- Prove2me | solution 1 for Formalism.L2.Th1.E.ptOf_add_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:17:45.814065+00:00
-- url     : https://prove2.me/submissions/1818a624-4e5d-4aa2-9d4d-6ac6a5bf5403

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Theorems.Thm_Formalism_L2_Th1_E_ptOf_some
import Theorems.Thm_Formalism_L2_Th1_E_ptOf_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
namespace Formalism.L2.Th1.E
theorem _root_.solution (t ω : ℂ) (hω : ω ∈ L.lattice) : ptOf l L ι (t + ω) = ptOf l L ι t := by
  have h1 : L.weierstrassP (t + ω) = L.weierstrassP t := L.weierstrassP_add_coe t ⟨ω, hω⟩
  have h2 : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
  have h3 : t + ω ∈ L.lattice ↔ t ∈ L.lattice := L.lattice.add_mem_iff_left hω
  by_cases ht : t ∈ L.lattice
  · rw [ptOf_lattice l L ι t ht, ptOf_lattice l L ι (t + ω) (h3.mpr ht)]
  · rw [ptOf_some l L ι t ht, ptOf_some l L ι (t + ω) (fun h => ht (h3.mp h))]
    simp only [WeierstrassCurve.Affine.Point.some.injEq, h1, h2, and_self]
end Formalism.L2.Th1.E
