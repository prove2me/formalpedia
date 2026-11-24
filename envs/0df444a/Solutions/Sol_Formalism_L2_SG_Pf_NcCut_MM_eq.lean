-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcCut.MM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:30.554334+00:00
-- url     : https://prove2.me/submissions/e5f48b3b-717b-4092-b13c-43a3f29cec2a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NormalizingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcCut
open Formalism.FourierDecayAlt.S3
variable {P : Type} [Fintype P] (B : MassData P)
namespace Formalism.L2.SG.Pf.NcCut
theorem _root_.solution (hP : B.Pos) (hO : B.InOrdinary) (hT : B.InTyped) :
    B.MM = B.unitLevelVolume * B.μK * B.μKnat / (B.μS * B.μS') := by
  obtain ⟨hp, -, -, -, -, hU0, -⟩ := hP
  have h0 : B.Mo = B.localVolumeArchimedean * (B.μKo * B.μKo) / (B.μSo * B.μSo') := by
    have h := hO
    unfold MassData.InOrdinary at h
    rw [div_eq_iff hU0.ne'] at h
    rw [h]
    ring
  have h1 : ∀ p, B.Mp p = B.localVolumeAtPlace p * (B.μKp p * B.μKnatp p) / (B.μSp p * B.μSp' p) := by
    intro p
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff hU.ne'] at h
    rw [h]
    ring
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKnat MassData.μS MassData.μS'
  simp only [h0, h1, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [div_mul_div_comm]
  congr 1 <;> ring
end Formalism.L2.SG.Pf.NcCut
