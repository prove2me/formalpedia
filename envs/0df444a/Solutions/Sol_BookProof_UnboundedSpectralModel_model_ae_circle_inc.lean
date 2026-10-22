-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.model_ae_circle_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:10.319815+00:00
-- url     : https://prove2.me/submissions/f5989287-af63-49de-9a94-57e5ef2918f1

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.model_ae_circle_inc
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_eq_zero_iff
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterStoneResolvent
open BookProof.UnboundedSpectralModel



noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum
open BookProof.ChapterLinftyMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

set_option maxHeartbeats 1000000 in
include hV in
theorem solution [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, ‖z.1‖ ^ 2 = z.1.im := by

  have h0 : mulRep mu (cayleyFn T) = 0 := mulRep_cayleyFn_eq_zero T V hV
  have hae : (fun z => (cayleyFn T z : ℂ)) =ᵐ[mu] 0 :=
    (BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff (μ := mu)
      (fun z => (cayleyFn T z : ℂ)) (contMemLpTop mu (cayleyFn T))).mp h0
  filter_upwards [hae] with z hz
  have : ((z.1.im - ‖z.1‖ ^ 2 : ℝ) : ℂ) = 0 := hz
  have hr : (z.1.im - ‖z.1‖ ^ 2 : ℝ) = 0 := by exact_mod_cast this
  linarith
