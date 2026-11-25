-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restrictedLattice_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:10:28.517638+00:00
-- url     : https://prove2.me/submissions/662ccc16-ce25-4373-84c1-ed21a4b7399f

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
variable {r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (S : Submodule ℤ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]))
    (hS : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
      initPart (Fin.last K, ρ) 0 h ∈ S) : M2 p LL J M ρ ≤ S := by
  unfold M2
  refine iSup_le fun o => ?_
  intro z hz
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.1 hz
  obtain ⟨hY, hi⟩ := Submodule.mem_inf.1 hh
  exact hS o h hY hi
end Formalism.InvariantFactorPaths.L4
