-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.gramLoc_setC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:12.977892+00:00
-- url     : https://prove2.me/submissions/6d54aa51-e4d9-4a6c-bdd8-f19c05eae628

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_pdG_of_built

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
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (w : List C.Letter) (P Q : C.LPt) :
    (setC S p F).gramLoc v ε i w P Q =
      ((√(nnS S P) * √(nnS S Q) : ℝ) : ℂ) * ((1 / (bS S P * bS S Q * ΓS S i) : ℝ) : ℂ) *
        (p v).RR (F v ε) i w (stdS S P) (stdS S Q) := by
  have hG := (pdG_of_built hB v).1
  show ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G Q) : ℝ) : ℂ) *
    rrC S p F v ε i w P Q = _
  rw [hG]
  simp only [rrC, nnS, bS, ΓS, stdS, mul_assoc]
end Formalism.FourierDecayAlt.P.PBL
