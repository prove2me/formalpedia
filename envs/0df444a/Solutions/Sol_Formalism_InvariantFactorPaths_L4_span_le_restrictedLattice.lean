-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.span_le_restrictedLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:27.43598+00:00
-- url     : https://prove2.me/submissions/9979f921-5483-4e6a-9bdb-fb083e60732a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restrictedLattice_zpClosed
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restrictedLattice_divStable

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
variable {s : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hU : UDivInt) (hD : DWDivInt) (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c)
    (S : Set (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]))
    (hS : S ⊆ ((M2 p LL J M (Fin.last s)).toAddSubgroup : Set (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]))) :
    DeltaLat p G S ≤ (M2 p LL J M (Fin.last s)).toAddSubgroup := by
  unfold DeltaLat
  exact sInf_le ⟨hS, restrictedLattice_zpClosed LL J M (Fin.last s), restrictedLattice_divStable hU hD LL hv J M c k0 hk0 hc hmin G hE⟩
end Formalism.InvariantFactorPaths.L4
