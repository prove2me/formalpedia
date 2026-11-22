-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.I_onto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:32.394556+00:00
-- url     : https://prove2.me/submissions/aaae9378-3401-473a-9fe1-9d18caa9ab58

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_I_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (f : S.Cl → S.V) : (∃ x, S.I x = f) ↔ ∀ c (γ : S.Gam c), S.ρ c γ (f c) = f c := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (S.basis.equivFun.symm x).2
  · intro h
    exact ⟨S.basis.equivFun ⟨f, h⟩, by simp [I_apply]⟩
end Formalism.L2.DIV.CSD
