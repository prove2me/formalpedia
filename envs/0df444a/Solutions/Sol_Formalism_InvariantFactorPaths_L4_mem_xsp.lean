-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mem_xsp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:43:57.229894+00:00
-- url     : https://prove2.me/submissions/310f02fc-fde3-4214-9e56-a457ba029af9

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    x ∈ XSp p LL J M ρ ↔ x ∈ Pol p r LL ∧ x ∈ FreeOf p (Fin.last K, ρ) ∧
      ∀ k, (K + 1 ≤ J k → x ∈ YCond p LL K (M k) ∧ x ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k)) ∧
        (¬ K + 1 ≤ J k → x ∈ YCond p LL (J k) (M k)) := by
  unfold XSp
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun k => ?_
  split_ifs with hk
  · rw [Submodule.mem_inf]
    exact ⟨fun h => ⟨fun _ => h, fun h' => absurd hk h'⟩, fun h => h.1 hk⟩
  · exact ⟨fun h => ⟨fun h' => absurd h' hk, fun _ => h⟩, fun h => h.2 hk⟩
end Formalism.InvariantFactorPaths.L4
