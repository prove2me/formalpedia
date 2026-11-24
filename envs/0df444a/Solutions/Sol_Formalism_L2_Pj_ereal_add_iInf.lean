-- Prove2me | solution 1 for Formalism.L2.Pj.ereal_add_iInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:47.649338+00:00
-- url     : https://prove2.me/submissions/580375f4-b532-4b26-af88-b2c7efe27681

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
variable {v : R → EReal}
namespace Formalism.L2.Pj
theorem _root_.solution {ι : Type} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + ⨅ i, f i = ⨅ i, ((c : EReal) + f i) := by
  have hc : ∀ x : EReal, ((-c : ℝ) : EReal) + ((c : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  have hc' : ∀ x : EReal, (c : EReal) + (((-c : ℝ) : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h1 : ((-c : ℝ) : EReal) + ⨅ i, ((c : EReal) + f i) ≤ ⨅ i, f i :=
      le_iInf fun i => (add_le_add le_rfl (iInf_le (fun i => (c : EReal) + f i) i)).trans (hc (f i)).le
    have h2 := add_le_add (le_refl (c : EReal)) h1
    rwa [hc'] at h2
end Formalism.L2.Pj
