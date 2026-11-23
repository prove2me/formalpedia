-- Prove2me | solution 1 for Formalism.L2.Th1.A.subst_injective_of_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:25.73169+00:00
-- url     : https://prove2.me/submissions/95512d83-e890-4006-b913-3e318fcebb42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
section SlopeTestRemainingChoices
variable {R : Type u} [CommRing R]
private theorem powerSeries_subst_subst_eq_subst_subst {a b f : R⟦X⟧} (ha : HasSubst a) (hb : HasSubst b) :
    PowerSeries.subst b (PowerSeries.subst a f : R⟦X⟧)
      = PowerSeries.subst (PowerSeries.subst b a : R⟦X⟧) f := by
  first
  | exact PowerSeries.subst_comp_subst_apply ha hb f
  | exact (PowerSeries.subst_comp_subst_apply ha hb f).symm
  | rw [PowerSeries.subst_comp_subst_apply ha hb]
end SlopeTestRemainingChoices
end Formalism.L2.Th1.A
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution {l e a b : R⟦X⟧} (hl : HasSubst l) (ha : HasSubst a)
    (hb : HasSubst b) (hel : e.subst l = X) (h : l.subst a = l.subst b) : a = b := by
  calc a = e.subst (l.subst a) := by
        rw [← powerSeries_subst_subst_eq_subst_subst hl ha, hel, PowerSeries.subst_X ha]
    _ = e.subst (l.subst b) := by rw [h]
    _ = b := by rw [← powerSeries_subst_subst_eq_subst_subst hl hb, hel, PowerSeries.subst_X hb]
end Formalism.L2.Th1.A
