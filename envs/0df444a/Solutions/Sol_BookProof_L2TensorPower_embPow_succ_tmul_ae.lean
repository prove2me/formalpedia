-- Prove2me | solution 1 for BookProof.L2TensorPower.embPow_succ_tmul_ae
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:41:16.416839+00:00
-- url     : https://prove2.me/submissions/0b2a0832-a0a8-4d15-a84b-abcecb64da48

-- Generated from ChapterL2TensorPowerUnitary.lean — solution of BookProof.L2TensorPower.embPow_succ_tmul_ae
import Mathlib
import Definitions.Def_ChapterL2TensorPowerUnitary
import Theorems.Thm_BookProof_L2TensorPower_embPow_succ_tmul
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.L2TensorPower




open MeasureTheory BookProof.TensorCore BookProof.NsScalarVectorCurry
open BookProof.SecondQuantizationCore
open scoped TensorProduct

noncomputable section


variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]
variable {V : Type} [MeasurableSpace V] (μ : Measure V) [SigmaFinite μ]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) :
    (embPow μ (n + 1) (a ⊗ₜ[ℂ] t) : (Fin (n + 1) → V) → ℂ) =ᵐ[piMeasure μ (n + 1)]
      fun x => (a : V → ℂ) (x 0) * (embPow μ n t : (Fin n → V) → ℂ) (Fin.tail x) := by

  rw [embPow_succ_tmul, splitIso]
  have h1 := Lp.coeFn_compMeasurePreserving (prodMk a (embPow μ n t))
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0)
  have h2 := (coeFn_prodMk a (embPow μ n t)).comp_tendsto
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).quasiMeasurePreserving.tendsto_ae
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Function.comp_apply] at hx1 hx2
  refine hx1.trans (hx2.trans ?_)
  simp [MeasurableEquiv.piFinSuccAbove_apply]
