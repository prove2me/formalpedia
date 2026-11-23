-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BasisReduction.q_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:24.491921+00:00
-- url     : https://prove2.me/submissions/efed356f-c267-4d62-8a07-09779edfcdd6

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BasisReduction
open Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
namespace Formalism.LatticeBaseChangeAlt.BasisReduction
theorem _root_.solution (A : Submodule O X) {B B' : Submodule O X} (h : A ⊓ B = A ⊓ B') :
    q A B = q A B' := by
  have e : B.comap A.subtype = B'.comap A.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro hx
      have : (x : X) ∈ A ⊓ B' := h ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
    · intro hx
      have : (x : X) ∈ A ⊓ B := h.symm ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
  unfold q
  rw [e]
end Formalism.LatticeBaseChangeAlt.BasisReduction
