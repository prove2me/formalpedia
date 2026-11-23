-- Prove2me | solution 1 for Formalism.L2.Th1.H.InterClass_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:46.33286+00:00
-- url     : https://prove2.me/submissions/55b2927b-c221-4f60-a0a1-cc08fd535a6b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : SemiHom) : InterClass := by
  intro V _ _ H hH Λ₁ Λ₂ α hα F hF x hx y hy hy1 z
  have hF' : ∀ w ∈ Λ₁, ∀ v, α w * opU H w F v = F v := hF
  have hfun : (fun v => α y * opU H y F v) = F := funext fun v => hF' y hy1 v
  have e := h V H hH Λ₂ α hα x hx y hy F z
  exact e.symm.trans (congrArg (fun G => α x * opU H x G z) hfun)
end Formalism.L2.Th1.H
