-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.sumAlgEquiv_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:33.731597+00:00
-- url     : https://prove2.me/submissions/ee5c9c00-05c8-4e41-94c4-47d354a10f3b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution (a : MvPolynomial S₁ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inl a) = map (C : K →+* MvPolynomial S₂ K) a := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl K S₁ S₂) a
  simpa [MvPolynomial.algebraMap_eq] using h
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
