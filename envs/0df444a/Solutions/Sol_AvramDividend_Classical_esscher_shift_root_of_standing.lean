-- Prove2me | solution 1 for AvramDividend.Classical.esscher_shift_root_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:35:13.919388+00:00
-- url     : https://prove2.me/submissions/5c5fcbe0-c9fe-45b7-af43-197802970166

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every positive shifted Esscher level has a root under the actual standing law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F) (hX : X.Standing)
    (q phi p : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hroot : X.ψ phi = q)
    (hp : 0 < p) :
    ∃ lambda : ℝ, 0 < lambda ∧ X.ψ (phi + lambda) - q = p := by
  have hqp : 0 < p + q := by linarith
  obtain ⟨b0, hb0, hbeyond⟩ :=
    psi_eventually_gt_of_standing X hX (p + q) hqp
  let B : ℝ := max phi b0
  have hphiB : phi ≤ B := le_max_left _ _
  have hbB : b0 ≤ B := le_max_right _ _
  have hsubset : Icc phi B ⊆ Ici (0 : ℝ) := by
    intro t ht
    exact le_trans hphi.le ht.1
  have hcont : ContinuousOn X.ψ (Icc phi B) :=
    (levy_laplace_exponent_continuousOn_nonnegative X).mono hsubset
  have hval : p + q ∈ Icc (X.ψ phi) (X.ψ B) := by
    change X.ψ phi ≤ p + q ∧ p + q ≤ X.ψ B
    constructor
    · rw [hroot]
      linarith
    · exact (hbeyond B hbB).le
  obtain ⟨theta, htheta, heq⟩ :=
    (intermediate_value_Icc hphiB hcont) hval
  have hthetagt : phi < theta := by
    by_contra hn
    have ht_eq : theta = phi := le_antisymm (le_of_not_gt hn) htheta.1
    rw [ht_eq, hroot] at heq
    linarith
  refine ⟨theta - phi, by linarith, ?_⟩
  have hadd : phi + (theta - phi) = theta := by ring
  rw [hadd, heq]
  ring
