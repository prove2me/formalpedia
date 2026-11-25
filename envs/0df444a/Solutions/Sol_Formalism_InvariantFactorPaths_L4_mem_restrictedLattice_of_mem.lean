-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mem_restrictedLattice_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:44.627053+00:00
-- url     : https://prove2.me/submissions/3f981cb7-6794-4a63-ac0d-9bf7d0db9f0b

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
theorem _root_.solution (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (o : ℕ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hY : h ∈ Y p (setLast LL o) J M)
    (hi : h ∈ IntPol p (Fin (K + 1) × Fin r)) : initPart (Fin.last K, ρ) 0 h ∈ M2 p LL J M ρ := by
  unfold M2
  exact Submodule.mem_iSup_of_mem o (Submodule.mem_map.2 ⟨h, Submodule.mem_inf.2 ⟨hY, hi⟩, rfl⟩)
end Formalism.InvariantFactorPaths.L4
