-- Prove2me | solution 1 for FamousTheorems.kac_independence_char_fun_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:49:34.695361+00:00
-- url     : https://prove2.me/submissions/3e73afae-7d38-4ecf-86a0-1e4d149ebf9b

import Mathlib

open MeasureTheory

theorem solution {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Fintype ι] [IsProbabilityMeasure P]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] {X : ∀ i, Ω → E i} (hX : ∀ i, AEMeasurable (X i) P) :
    ProbabilityTheory.iIndepFun X P ↔
      ∀ t : WithLp 2 (∀ i, E i),
        charFun (P.map fun ω => WithLp.toLp 2 fun i => X i ω) t = ∏ i, charFun (P.map (X i)) (t.ofLp i) :=
  ProbabilityTheory.iIndepFun_iff_charFun_pi hX
