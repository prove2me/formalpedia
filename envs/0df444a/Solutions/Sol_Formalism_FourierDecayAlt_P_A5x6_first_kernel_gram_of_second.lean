-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.first_kernel_gram_of_second
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:36.318014+00:00
-- url     : https://prove2.me/submissions/7784b6ec-5b83-46ec-a223-d04dece54cd1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psd_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (h : BlockKernelPosSemidef) : SingleBlockPosSemidef := by
  classical
  unfold SingleBlockPosSemidef
  unfold BlockKernelPosSemidef at h
  intro K _ _ _ R ψ hLD m F hF c
  have hI := h K R ψ hLD 1 le_rfl m (F.image fun x => (x, c)) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hF y hy)
  exact psd_comap (fun x y : Point K × Kˣ => Ns R ψ 1 x.1 y.1 x.2 y.2) (fun x => (x, c)) F hI
end Formalism.FourierDecayAlt.P.A5x6
