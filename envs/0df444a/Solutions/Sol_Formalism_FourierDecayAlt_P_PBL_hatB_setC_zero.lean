-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.hatB_setC_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:09.601745+00:00
-- url     : https://prove2.me/submissions/75afd0bf-acb5-4a6a-902c-d9fe272381d1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_gN_setC_zero

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
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (w : List C.Letter) (l : ℂ) (h h' : C.LPt) (hsz : D.ptSize h = j)
    (hsz' : D.ptSize h' = j) (hn : ¬ (D.IsLocPt h j ∧ D.IsLocPt h' j)) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' = 0 := by
  unfold KB.hatB
  have h0 : ∀ c : ℂ, KB.gN (setC S p F) v ε (j + 1 + 1 - 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
    intro c
    apply gN_setC_zero hB F v ε _ w _ _
    rintro ⟨h1, h2⟩
    apply hn
    have key : ∀ R : C.LPt, D.ptSize R = j → D.IsLocPt (R ++ [(1, c)]) (j + 1 + 1 - 1) → D.IsLocPt R j := by
      intro R hR hRl
      exact And.intro (fun b hb => hRl.1 b (List.mem_append_left _ hb)) hR
    exact ⟨key h hsz h1, key h' hsz' h2⟩
  simp only [h0, zero_mul, MeasureTheory.integral_zero, mul_zero]
end Formalism.FourierDecayAlt.P.PBL
