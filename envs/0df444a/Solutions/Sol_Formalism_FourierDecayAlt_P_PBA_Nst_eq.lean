-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.Nst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:20:03.563409+00:00
-- url     : https://prove2.me/submissions/edfbba91-d7b5-4aec-b413-c9d1a9137ea0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_loc_join

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {ε : ℝ} {i : ℕ} (hi : i ≤ S.G.r + 1) (s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    S.base.Nst ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, KB.gN S v ε i (w.1 v)
      (C.loc (S.σ v) h ++ [(s, S.σ v t)]) (C.loc (S.σ v) h' ++ [(s, S.σ v t')]) := by
  have hsz : ((C.Word.size S.P w.1 : ℝ) : ℂ) = ∏ v, ((S.sizeAt v (w.1 v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    rfl
  show (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) /
      ((C.Word.size S.P w.1 : ℝ) : ℂ) = _
  simp only [C.HidaSetting.gram, if_pos hi, loc_join, KB.gN, Finset.prod_div_distrib, hsz,
    Finset.sum_div, mul_div_assoc]
end Formalism.FourierDecayAlt.P.PBA
