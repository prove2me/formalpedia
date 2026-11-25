-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.hatOK_of_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:25:01.265642+00:00
-- url     : https://prove2.me/submissions/9d51120a-0dd2-42c0-9d85-c74149d74a6a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution (hP : JDPolyOK) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cc : ℝ} (hCc : 1 ≤ Cc) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}
    {Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    (hΘ : PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ)
    (hc : B.Commutes (T v).base (B.GPos (T v).base) Θ) : HatOK Cc S T v Θ := by
  obtain ⟨hs, hg, ho⟩ := hP S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) _ _ Θ hΘ
  have hn : (0 : ℝ) ≤ nDim S.G.k S.G.r := by unfold nDim; positivity
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  refine ⟨hs _, hc, hg _ ?_, ?_⟩
  · have e1 : (((S.G.r + 1) * (2 * S.G.r + S.G.k + 1) : ℕ) : ℝ) = ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
      unfold nDim; push_cast; ring
    rw [e1, mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg hr hn) hCc
  · have e2 : ((B.opOrder Θ : ℕ) : ℝ) ≤ nDim S.G.k S.G.r := by
      unfold nDim; exact_mod_cast ho
    exact e2.trans (le_mul_of_one_le_left hn hCc)
end Formalism.FourierDecayAlt.P.CutMP
