-- Prove2me | solution 1 for CorrelatedRounding.exists_alg1_draw__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T21:19:06.315745+00:00
-- url     : https://prove2.me/submissions/f7a7f52d-dbed-49ca-9abe-61184b5b0890

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_IsAlg1Draw
open CorrelatedRounding MeasureTheory ProbabilityTheory

namespace CRAux

noncomputable def ν {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) : Measure ℝ :=
  if 0 < y u k then expMeasure (y u k) else Measure.dirac 0

instance {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) : IsProbabilityMeasure (ν u k) := by
  unfold ν
  split_ifs with h
  · exact isProbabilityMeasure_expMeasure h
  · infer_instance

end CRAux

theorem solution (q K : ℕ) (hq : 1 ≤ q) (u : Fin K → Fin q → ℝ) (hu : IsInstance u) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E := by
  refine ⟨Fin K → ℝ, inferInstance, Measure.pi (CRAux.ν u), inferInstance,
    fun k ω => ω k, ?_, ?_⟩
  · exact iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id)
  · intro k hk
    refine ⟨(measurable_pi_apply k).aemeasurable, ?_⟩
    rw [(measurePreserving_eval (CRAux.ν u) k).map_eq]
    simp [CRAux.ν, hk]
