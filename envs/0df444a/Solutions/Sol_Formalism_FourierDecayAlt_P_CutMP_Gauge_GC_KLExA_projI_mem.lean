-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.projI_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:14.605469+00:00
-- url     : https://prove2.me/submissions/1d63f0f4-f009-4ae8-856d-a36120a95e9a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_projI_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
theorem _root_.solution (h : DirectSum.IsInternal S) {i : ι} {v : V} (hv : v ∈ S i) : projI h i v = ⟨v, hv⟩ :=
  projI_self h ⟨v, hv⟩
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
