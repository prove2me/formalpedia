-- Prove2me | solution 1 for BosonicLearn.adaptive_scheme_collective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T04:38:30.439771+00:00
-- url     : https://prove2.me/submissions/6d78bc84-874f-4058-b250-9a98f6c2ec6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Theorems.Thm_BosonicLearn_fockPOVM_postprocess
import Theorems.Thm_BosonicLearn_adaptive_scheme_product_povm
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

theorem solution {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (est : Kernel (Fin N → O) (State (Occupation (Fin n))))
    (hest : IsMarkovKernel est) :
    ∃ E : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n))),
      ∀ ρ : State (Occupation (Fin n)),
        E.law (WildeQIT.Schumacher.tensorPow N ρ.coefficients) =
          (transcriptLaw S ρ.coefficients).bind est := by
  -- the scheme as one POVM on the `N` copies, with the transcript as outcome
  obtain ⟨M, hM⟩ := adaptive_scheme_product_povm S
  -- the estimator applied to the transcript
  obtain ⟨E, hE⟩ := fockPOVM_postprocess M est hest
  refine ⟨E, fun ρ => ?_⟩
  rw [hE]
  -- on `ρ^{⊗N}` the law of `M` is the transcript law
  have h := hM (fun _ => ρ.coefficients) (fun _ => ρ.density)
  have h' : M.law (WildeQIT.Schumacher.tensorPow N ρ.coefficients) = transcriptLaw S ρ.coefficients := h
  rw [h']
