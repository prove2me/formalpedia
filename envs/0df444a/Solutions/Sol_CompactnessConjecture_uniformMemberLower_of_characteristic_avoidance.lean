-- Prove2me | solution 1 for CompactnessConjecture.uniformMemberLower_of_characteristic_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/5e723134-b347-414e-a2be-1793c7b258c8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_induction
import Theorems.Thm_CompactnessConjecture_jQuotient_mem_proposedFamily
import Theorems.Thm_CompactnessConjecture_kQuotient_mem_proposedFamily
import Theorems.Thm_CompactnessConjecture_four_cycle_eventual_manuscript_lower
import Theorems.Thm_CompactnessConjecture_six_cycle_eventual_manuscript_lower
import Theorems.Thm_CompactnessConjecture_member_eventual_lower_of_prime_power_avoidance

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Topology
namespace CompactnessConjecture
theorem _root_.solution
    (hj : ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)))
    (hk : ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j))) :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  proposedFamily_induction
    (P := fun graph => ∀ᶠ n : ℕ in Filter.atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n graph.graph : ℝ))
    (by simpa [finiteCycle] using four_cycle_eventual_manuscript_lower)
    (by simpa [finiteCycle] using six_cycle_eventual_manuscript_lower)
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (jQuotient_mem_proposedFamily hf)
      2 (by norm_num) (by norm_num) (hj f hf))
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (kQuotient_mem_proposedFamily hf)
      3 (by norm_num) (by norm_num) (hk f hf))
end CompactnessConjecture
