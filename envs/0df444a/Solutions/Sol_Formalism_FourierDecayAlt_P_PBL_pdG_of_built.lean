-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.pdG_of_built
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:28.914863+00:00
-- url     : https://prove2.me/submissions/1d43be7e-fd52-4fea-9d50-5bc8e4974294

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex

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
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) :
    (S.pd v).G = D.ptGG (S.T * S.T') ∧
      Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' = S.T * S.T' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB
  obtain ⟨-, -, hpd, -, -⟩ := hv v
  have hTT : Tz S.G.k S.G.r (p v).T.base.z * Tz S.G.k S.G.r (p v).T.base.z' = S.T * S.T' := by
    have h := S.hT v
    rw [hpd] at h
    rw [← h.1, ← h.2]
    rfl
  refine ⟨?_, hTT⟩
  rw [hpd, ← hTT]
  rfl
end Formalism.FourierDecayAlt.P.PBL
