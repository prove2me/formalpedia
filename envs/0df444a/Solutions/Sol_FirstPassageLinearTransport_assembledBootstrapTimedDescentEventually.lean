-- Prove2me | solution 1 for FirstPassageLinearTransport.assembledBootstrapTimedDescentEventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:33.307188+00:00
-- url     : https://prove2.me/submissions/e49b7a37-0ea6-4bea-a332-d0a2558a81b9

import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Theorems.Thm_FirstPassageLinearTransport_eventuallyOfEventuallyShellwise
import Theorems.Thm_FirstPassageLinearTransport_assembledBootstrap_naturalDensityOne_of_vanish
import Theorems.Thm_FirstPassageLinearTransport_assembledBootstrap_timed_descent_of_scalar_bounds
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellClockLt6953
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellLanding
import Theorems.Thm_FirstPassageLinearTransport_mem_shellBootstrap_of_mem_assembled
import Theorems.Thm_FirstPassageLinearTransport_shellBootstrapRatioTendstoZero


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta chi Dc omega delta : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hdensity : densityGamma omega chi < 1)
    (hdelta1 : delta < 1)
    (hdescent : delta < descentAlpha omega r)
    (hrclock : r < clockThreshold) :
    NaturalDensityOne (assembledBootstrap p omega) ∧
      ∀ᶠ n : ℕ in atTop,
        n ∈ assembledBootstrap p omega →
          HasTimedStretchedLogDescent delta (6953 / 1000) n := by
  have hdense : NaturalDensityOne (assembledBootstrap p omega) :=
    assembledBootstrap_naturalDensityOne_of_vanish p omega
      (shellBootstrapRatioTendstoZero p hchi0 hchir hchi1
        hDc0 hDc1 hDcRate hchiDc homega0 hdensity)
  have hlandingM := eventuallyShellLanding p homega0 hdelta1 hdescent
  have hclockM := eventuallyShellClockLt6953 p hrclock homega0
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount omega M) →
      (stageOrbit p (stageCount omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount omega M) →
      (stageClock p (stageCount omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  refine ⟨hdense, ?_⟩
  filter_upwards [hlanding, hclock, eventually_gt_atTop (0 : ℕ)] with n
    hnlanding hnclock hnpos hnassembled
  have hnboot := mem_shellBootstrap_of_mem_assembled p hnassembled
  exact assembledBootstrap_timed_descent_of_scalar_bounds p
    (hnlanding hnpos hnboot) (hnclock hnpos hnboot)
end FirstPassageLinearTransport
