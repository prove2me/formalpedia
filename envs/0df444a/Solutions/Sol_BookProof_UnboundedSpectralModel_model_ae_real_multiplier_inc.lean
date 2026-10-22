-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:12.709281+00:00
-- url     : https://prove2.me/submissions/16a9e82a-ffb8-4de8-a1c9-116d9c72b2a3

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterStoneResolvent
open BookProof.UnboundedSpectralModel



noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

set_option maxHeartbeats 1000000 in
include hV in
theorem solution [IsFiniteMeasure mu] :
    ∀ᵐ z ∂mu, 1 + Complex.I * z.1 = ((z.1.re / ‖z.1‖ ^ 2 : ℝ) : ℂ) * z.1 := by

  filter_upwards [model_ae_circle T V hV, model_ae_ne_zero T V hV] with z hcirc hne
  exact cayley_real_multiplier hcirc hne
