-- Prove2me | solution 1 for CompactnessConjecture.familyLittleO_of_eventual_host_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/173a4435-b9e1-4cf9-a3cf-187be6d27b99

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_extremalScale_nonneg
import Theorems.Thm_CompactnessConjecture_familyExtremal_real_le_of_forall_free

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology
namespace CompactnessConjecture
theorem _root_.solution
    (family : Finset FiniteGraph)
    (hhost : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ host : SimpleGraph (Fin n),
          FamilyFree family host →
            (host.edgeFinset.card : ℝ) ≤ ε * extremalScale n) :
    FamilyLittleO family := by
  intro ε hε
  filter_upwards [hhost ε hε] with n hn
  exact familyExtremal_real_le_of_forall_free family n
    (mul_nonneg hε.le (extremalScale_nonneg n)) hn
end CompactnessConjecture
