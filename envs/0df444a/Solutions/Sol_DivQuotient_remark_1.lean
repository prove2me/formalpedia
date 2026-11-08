-- Prove2me | solution 1 for DivQuotient.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:42:00.028596+00:00
-- url     : https://prove2.me/submissions/d238d1c7-0170-46df-86c4-ae7e0c1b7441

import Mathlib
import Definitions.Def_DivQuotient_Axioms

open MeasureTheory

open DivQuotient in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (D : (Fin n → Lp ℝ ⊤ P) → EReal) :
    AxPC D ↔
      ∀ (X : Fin n → Lp ℝ ⊤ P) (l : ℝ), l ∈ Set.Icc (0 : ℝ) 1 →
        ∀ w ∈ stdSimplex ℝ (Fin n), ∀ w' ∈ stdSimplex ℝ (Fin n),
          D (fun i => (l • w + (1 - l) • w') i • X i) ≤
            max (D (fun i => w i • X i)) (D (fun i => w' i • X i)) := by
  constructor
  · intro hPC X l hl w hw w' hw'
    have hC := hPC X (max (D (fun i => w i • X i)) (D (fun i => w' i • X i)))
    have hmem := hC ⟨hw, le_max_left _ _⟩ ⟨hw', le_max_right _ _⟩ hl.1
      (by linarith [hl.2] : (0 : ℝ) ≤ 1 - l) (by ring)
    exact hmem.2
  · intro h X d
    intro w hw w' hw' a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    refine ⟨convex_stdSimplex ℝ (Fin n) hw.1 hw'.1 ha hb hab, ?_⟩
    exact le_trans (h X a ⟨ha, by linarith⟩ w hw.1 w' hw'.1) (max_le hw.2 hw'.2)
