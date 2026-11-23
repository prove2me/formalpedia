-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.top_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:35.3378+00:00
-- url     : https://prove2.me/submissions/811fb633-88cb-4ae2-a9ea-8be05ec576fc

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
namespace Formalism.G0.WalkSharpP
theorem _root_.solution {V : ℕ} {B : Finset (Fin V)} (h : B.Nonempty) : ∃ t ∈ B, (t : ℕ) = top B := by

  obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup B h (fun u : Fin V => (u : ℕ))
  exact ⟨t, ht, he.symm⟩
end Formalism.G0.WalkSharpP
