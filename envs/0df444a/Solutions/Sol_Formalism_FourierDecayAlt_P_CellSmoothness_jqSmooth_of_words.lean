-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CellSmoothness.jqSmooth_of_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:54:52.026861+00:00
-- url     : https://prove2.me/submissions/4a609888-8ad4-42b3-86ca-63e8568bd1f8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CellSmoothness
import Theorems.Thm_Formalism_FourierDecayAlt_P_CellSmoothness_contDiffOn_gq
import Theorems.Thm_Formalism_FourierDecayAlt_P_CellSmoothness_glev0
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_isOpen_good_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellHermitian_gqDom
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CellSmoothness
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CellSmoothness
theorem _root_.solution (hW : JWords) : JqSmooth := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  have hck := (hW k r Wp Wq D A m F hThr hCC).1
  have hg := contDiffOn_gq D
  have hQo : IsOpen (QDom k r D.z D.z') := Formalism.FourierDecayAlt.P.B7.isOpen_good_set D
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hqOm : gq D q ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := hck _ ⟨glev0 hqOm.1, hqOm.2⟩
  have hVo : IsOpen (QDom k r D.z D.z' ∩ (fun x => gq D x) ⁻¹' U) :=
    hg.continuousOn.isOpen_inter_preimage hQo hU
  refine ⟨QDom k r D.z D.z' ∩ (fun x => gq D x) ⁻¹' U, hVo, ⟨hq, hgU⟩, ?_⟩
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => F' (gq D x))
      (QDom k r D.z D.z' ∩ (QDom k r D.z D.z' ∩ (fun x => gq D x) ⁻¹' U)) :=
    hF'.comp ((hg.of_le (by exact_mod_cast le_top)).mono Set.inter_subset_left) (fun x hx => hx.2.2)
  refine h1.congr fun x hx => ?_
  have hxOm : gq D x ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hx.1
  exact hUF _ hx.2.2 (glev0 hxOm.1)
end Formalism.FourierDecayAlt.P.CellSmoothness
