-- Prove2me | solution 1 for Formalism.L2.Th1.F.Ker.mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:31.53585+00:00
-- url     : https://prove2.me/submissions/8105628a-85b1-4f81-bd80-a7ff7573929c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Ker
namespace Formalism.L2.Th1.F.Ker
theorem _root_.solution (L : PeriodPair) (α : ℂ) (h : MulStable L α) (u v : L.lattice) :
    (Submodule.Quotient.mk u : L.lattice ⧸ LinearMap.range (mulEnd L α h)) = Submodule.Quotient.mk v ↔
      ∃ x ∈ L.lattice, (u : ℂ) - v = α * x := by
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, x.2, ?_⟩
    have := congrArg Subtype.val hx
    simpa [mulEnd] using this.symm
  · rintro ⟨x, hx, hxe⟩
    exact ⟨⟨x, hx⟩, Subtype.ext (by simp [mulEnd, hxe])⟩
end Formalism.L2.Th1.F.Ker
