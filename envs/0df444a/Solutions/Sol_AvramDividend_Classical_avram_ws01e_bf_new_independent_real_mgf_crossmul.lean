-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_independent_real_mgf_crossmul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:19:17.9765+00:00
-- url     : https://prove2.me/submissions/90a2ca41-e630-44bf-a92f-ecc36dcce7c3

import Mathlib
import Mathlib.Probability.Moments.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (S D : Ω → ℝ) (p lam β gp : ℝ)
    (hIndep : ProbabilityTheory.IndepFun S D μ)
    (hS : Measurable S) (hD : Measurable D)
    (hGap : gp < p) (hLamGap : β < lam)
    (hSup : ProbabilityTheory.mgf S μ β = lam / (lam - β))
    (hTerm : ProbabilityTheory.mgf (fun ω => S ω - D ω) μ β =
      p / (p - gp)) :
    (p - gp) * lam *
      ProbabilityTheory.mgf (fun ω => -D ω) μ β =
    p * (lam - β) := by
  have hI : IndepFun S (fun ω => -D ω) μ := hIndep.comp measurable_id measurable_neg
  have hadd := hI.mgf_add' (t := β) hS.aestronglyMeasurable hD.neg.aestronglyMeasurable
  have hfun : (S + fun ω => -D ω) = fun ω => S ω - D ω := by funext ω; simp [sub_eq_add_neg]
  rw [hfun, hTerm, hSup] at hadd
  have h1 : p - gp ≠ 0 := by linarith
  have h2 : lam - β ≠ 0 := by linarith
  field_simp at hadd
  linear_combination -hadd
