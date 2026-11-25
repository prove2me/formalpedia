-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.IsDer.der_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:42.775745+00:00
-- url     : https://prove2.me/submissions/cd912973-3df3-454f-8cff-1d9e32b93d43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}
namespace Formalism.L2.Pj.GenericSectionMinimum.IsDer
theorem _root_.solution (h : IsDer δ) {ι : Type*} (s : Finset ι) (f : ι → A) : δ (∑ i ∈ s, f i) = ∑ i ∈ s, δ (f i) := by
  exact map_sum (AddMonoidHom.mk' δ h.add) f s
end Formalism.L2.Pj.GenericSectionMinimum.IsDer
