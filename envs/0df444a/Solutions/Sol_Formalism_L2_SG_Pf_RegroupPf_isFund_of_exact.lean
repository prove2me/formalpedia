-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RegroupPf.isFund_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:34.762377+00:00
-- url     : https://prove2.me/submissions/3f03d0ce-1ff8-4f48-bfca-c1111c92671f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RegroupPfUnfold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RegroupPf
variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
namespace Formalism.L2.SG.Pf.RegroupPf
theorem _root_.solution (μ : Measure H) (R : Subgroup H) (W : Set H) (hm : MeasurableSet W)
    (hc : ∀ x, ∃ g ∈ R, g * x ∈ W) (hu : ∀ x ∈ W, ∀ g ∈ R, g * x ∈ W → g = 1) :
    IsFundamentalDomain R W μ := by
  refine IsFundamentalDomain.mk' hm.nullMeasurableSet fun x => ?_
  obtain ⟨g, hg, hgx⟩ := hc x
  refine ⟨⟨g, hg⟩, hgx, ?_⟩
  rintro ⟨k, hk⟩ hkx
  have hkx' : k * x ∈ W := hkx
  have h := hu (g * x) hgx (k * g⁻¹) (R.mul_mem hk (R.inv_mem hg))
    (by rwa [mul_assoc, inv_mul_cancel_left])
  exact Subtype.ext (mul_inv_eq_one.mp h)
end Formalism.L2.SG.Pf.RegroupPf
