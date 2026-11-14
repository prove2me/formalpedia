-- Prove2me | solution 1 for BCFGJPSSV26.Stable.gfun_isSubmod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:02:21.831599+00:00
-- url     : https://prove2.me/submissions/8ecc407f-eaa0-4043-b65d-f49e499bbaaf

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
import all Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

/-- `g(∅) - g` is submodular. -/
theorem gfun_isSubmod (hv : I.Valid) (LS' : Finset (Fin I.m)) (Λ : List (Dummy I))
    (red blue : Finset (Fin I.m)) (z : ℕ) :
    IsSubmod fun Y ↦ gfun I LS' Λ red blue z ∅ - gfun I LS' Λ red blue z Y := by
  intro A B h e
  have := gfun_supermod hv LS' Λ red blue z h e
  simp only
  linarith

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

end Partition

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.gfun_isSubmod := @BCFGJPSSV26.Stable.gfun_isSubmod
