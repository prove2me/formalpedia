-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.least_exponent_over_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:27.377885+00:00
-- url     : https://prove2.me/submissions/c5b44823-ec51-4832-8081-886c4717a284

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_lattice_incl_iff_ring
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_exponent_eq_over_ring
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_latIncl_deltaIn_iff_dual_weyl
import Theorems.Thm_Formalism_CohomologicalDescent_LA_exact_z_specialization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : ExZLeastO := by
  intro O _ _ _ _ l hl hlO r n hn ν hν e
  rw [latIncl_deltaIn_iff_dual_weyl, exponent_eq_over_ring O l hl hlO r n hn ν]
  constructor
  · intro h
    exact Nat.sInf_le h
  · intro he
    have hne : (exZ r n hn ν l) ∈
        {e : ℕ | ∀ x ∈ dualWeyl O r n ν, (l : O) ^ e • x ∈ weyl O r n hn ν} :=
      (lattice_incl_iff_ring O l hl hlO r n hn ν _).1 (Formalism.CohomologicalDescent.LA.exact_z_specialization r n hn ν hν l hl)
    have hmem := Nat.sInf_mem ⟨_, hne⟩
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le he
    rw [hk, add_comm, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hmem x hx)
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
