-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.dW_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:02:00.544591+00:00
-- url     : https://prove2.me/submissions/e41de158-32d4-4f58-a89c-823e616f7b35

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_sizeAt_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_g_pos_of_built
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_gamLev_pos
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_rd_pos__cb5bba46fb5e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBL
theorem _root_.solution {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) :
    0 ≤ dW S v j w h h' := by
  have hg := g_pos_of_built hB
  have hrd := rd_pos' E
  have hκ : 0 < D.kapG (S.g : ℝ) (S6.rd E) := by unfold D.kapG; positivity
  have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
  unfold dW bS ΓS
  have := bSt_pos' _ hκ h
  have := bSt_pos' _ hκ h'
  have := gamLev_pos S.G.k S.G.r _ _ hκ hδ j
  have := sizeAt_nonneg S v w
  positivity
end Formalism.FourierDecayAlt.P.PBL
