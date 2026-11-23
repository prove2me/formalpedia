-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.oneLevelAfterOfOld
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:10.372987+00:00
-- url     : https://prove2.me/submissions/9c54726f-065c-4906-b0d0-ff34c442c534

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict__26d2ae93ba06
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_ThR_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_thetaDomination_dp_of_krPSD_of_domMin
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_Dp_Q

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution : OneLevelAfterOfOld := by
  intro hOL E W _ D ep C₄ hG hK hW hA2 hE hWv hP hLi hB hLa hep hC hv hv1 T hTh ε hε σ i hi1 hi hσ
    w hw
  obtain ⟨Th, hD⟩ := hTh
  have hA2' : (Dp D T Th).KernelSupport := by
    intro i s hs hsi hi h h' t t' hl hl' ht ht' htt hne
    refine hA2 i s hs hsi hi h h' t t' hl hl' ht ht' htt ?_
    intro h0
    apply hne
    show KrR D T i (join h s t) (join h' s t') = 0
    simp only [KrR, h0, ite_self]
  have hKP : (Dp D T Th).KernelPSD :=
    ⟨fun i Y => psd_restrict' Y (hK i (T.X i))
      (fun x y hxy => by show KrR D T i x y = _; simp only [KrR, if_pos hxy])
      (fun x y hxy => by show KrR D T i x y = _; simp only [KrR, if_neg hxy]), fun i s t Y => ThR_psd D T Th hK hD i s t Y⟩
  have h := hOL E W (Dp D T Th) ep C₄ hG hKP hW hA2' (thetaDomination_dp_of_krPSD_of_domMin D T Th hK hE hD) hWv hP hLi hB hLa
    hep hC hv hv1 T ε hε σ i hi1 hi
    (fun k hk => ⟨(hσ k hk).1, fun w hw => by rw [Dp_Q]; exact (hσ k hk).2 w hw⟩) w hw
  rw [Dp_Q] at h
  exact h
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
