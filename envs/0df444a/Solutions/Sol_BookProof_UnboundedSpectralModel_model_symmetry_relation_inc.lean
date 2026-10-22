-- Prove2me | solution 1 for BookProof.UnboundedSpectralModel.model_symmetry_relation_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:08:16.941449+00:00
-- url     : https://prove2.me/submissions/190ce7c4-db0a-43b0-b5a0-92ac140e0963

-- Generated from ChapterUnboundedSpectralModel.lean — solution of BookProof.UnboundedSpectralModel.model_symmetry_relation_inc
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
open BookProof.UnboundedSpectralModel



noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

set_option maxHeartbeats 1000000 in
include hV in
theorem solution (u : Lp ℂ 2 mu) :
    (inner ℂ u (mulRep mu (coordFn (resOp T)) u) : ℂ)
        - inner ℂ (mulRep mu (coordFn (resOp T)) u) u
      = (2 * Complex.I)
          * inner ℂ (mulRep mu (coordFn (resOp T)) u) (mulRep mu (coordFn (resOp T)) u) := by

  set Z := mulRep mu (coordFn (resOp T)) with hZ
  have hx := T.symmetric ⟨V (Z u), model_mem T V hV u⟩ ⟨V (Z u), model_mem T V hV u⟩
  rw [model_apply T V hV u] at hx
  simp only at hx
  rw [V.inner_map_map, V.inner_map_map, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right] at hx
  simp only [Complex.conj_I] at hx
  linear_combination hx
