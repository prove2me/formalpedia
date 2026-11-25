-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.cor_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:10:00.823185+00:00
-- url     : https://prove2.me/submissions/3fbbfa8c-266f-4761-8a1e-dead95936c22

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (hk : RowGlDiv) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (μ : Fin r → ℤ)
    (v : MvPolynomial (Fin n × Fin r) ℚ_[p]) (hv : v ∈ swappedDualWeyl p r n ν) (hh : (GR p r ν).IsHW μ v) :
    ∃ c : ℚ_[p], v = c • swappedHighestWeight p hn ν := by
  obtain ⟨f, hf, rfl⟩ := hv
  obtain ⟨c, hc⟩ := hwLine ℚ_[p] r n hn ν hν f hf (by
    intro a b hab k hk1
    apply (swp ℚ_[p] r n).injective
    rw [hk p r n ν a b hab.ne k f, map_zero]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h0 : (GR p r ν).E a b (swp ℚ_[p] r n f) = 0 := hh.2 a b hab
    rw [pow_succ, Module.End.mul_apply, h0, map_zero, smul_zero])
  refine ⟨c, ?_⟩
  rw [swappedHighestWeight, ← map_smul, ← hc]
  rfl
end Formalism.InvariantFactorPaths.INST
