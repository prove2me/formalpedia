-- Prove2me | solution 1 for Formalism.NG.splitAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:51.468071+00:00
-- url     : https://prove2.me/submissions/145e7a64-ebd0-4cfd-a8d1-a37c1fa289d6

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SplitFibre
import Theorems.Thm_Formalism_NG_splitAux

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
universe u
namespace Formalism.NG
theorem _root_.solution : StatSplitAlg := by
  unfold StatSplitAlg
  intro T _ P hP
  obtain ⟨T', i', a', rr, h1, h2, h3, h4, h5, h6⟩ := splitAux P.natDegree T P hP rfl
  refine ⟨T', i', a', rr, h1, h2, h3, h4, h5, fun B _ _ a ha => ?_⟩
  obtain ⟨φ, hφ⟩ := h6 B a ha
  refine ⟨φ, hφ, fun ψ hψ => ?_⟩
  refine AlgHom.ext_of_adjoin_eq_top h5 ?_
  rintro _ ⟨i, rfl⟩
  rw [hψ i, hφ i]
end Formalism.NG
