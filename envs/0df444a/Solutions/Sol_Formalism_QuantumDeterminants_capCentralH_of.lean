-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capCentralH_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:35:07.358959+00:00
-- url     : https://prove2.me/submissions/f1438e5a-70f3-4bff-a48b-68bfdbe7060f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_eq
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_fun
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUJ
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_smooth
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_repr
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_gl
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor_fun
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_mk
import Theorems.Thm_Formalism_REAL_qDetCentral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution (hAd : GlRelAd) : CapCentralH := by
  intro n ε E _ _ H P Q f u c d g hQP hPQ hH hf hg
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have hR := ioh_repr (ε := ε) (E := E) P Q
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_EabH_fun ε H P Q f c d hQP hPQ hH,
    ioh_EabH_eq ε H P Q _ c d hQP hPQ hH g, ioh_qminor_fun ε H P Q hQP hPQ hH]
  have h1 := ioh_qminor_rep hR id id u (hR c d _ x hx) _ hg'
  have h2 := hR c d _ _ (ioh_qminor_rep hR id id u hx) _ hg'
  have hc := qDetCentral (Module.End ℂ (ioS ε E)) n (iohE ε E P Q) (ioh_gl hAd P Q hQP) u c d
  dsimp only at h1 h2
  rw [h1, h2]
  unfold qdet at hc
  exact congrArg (fun T : Module.End ℂ (ioS ε E) => (T x).1 ⟨_, hg'⟩) hc
end Formalism.QuantumDeterminants
