-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DualKernelLemmas.d1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:52:06.712174+00:00
-- url     : https://prove2.me/submissions/ba21ba3d-f124-415b-87f1-f362bfab0406

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_real_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_d1a
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_d1b
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_csPos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DualKernelLemmas
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.DualKernelLemmas
theorem _root_.solution : DualityCauchySchwarz := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD hP X₁ X₂
  have ha := d1a A S V ρ Ω RR TT q a Y hD X₁ X₂
  have hb := d1b A S V ρ Ω RR TT q a Y hD X₂ X₂
  have hq : q Y ≠ 0 := hD.2.2.2.2.2
  have hm : frm ρ (RR * ins a (TT (↑Y + 1))ᵀ) X₂ X₂ =
      q Y * frm ρ (RR * ins a (TT ↑Y)) (act (PsiP TT q a ↑Y) X₂) (act (PsiP TT q a ↑Y) X₂) := by
    rw [hb]; field_simp
  rw [hm, ha]
  refine real_bound _ _ _ _ hq (hP X₁).2 (hP _).2 ?_
  exact csPos A S V ρ _ X₁ _ hP
end Formalism.FourierDecayAlt.P.DualKernelLemmas
