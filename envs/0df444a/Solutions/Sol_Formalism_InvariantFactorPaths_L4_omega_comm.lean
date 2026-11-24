-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.omega_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:51.543968+00:00
-- url     : https://prove2.me/submissions/aaa03024-b3d3-4b4a-a6ed-48e4363f4249

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_comm_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (c : ℤ) (s t : Fin r)
    (hs : s ∈ univ.erase ρ) (ht : t ∈ univ.erase ρ) (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) s t (Omega p LL c ρ z) = Omega p LL c ρ (glAct p LL (K + 1) s t z) := by
  classical
  have hterm : ∀ a : Fin r, glAct p LL (K + 1) s t (Uop p LL c (univ.erase ρ) a (dW p K a z)) =
      Uop p LL c (univ.erase ρ) a (dW p K a (glAct p LL (K + 1) s t z)) -
        (if s = a then Uop p LL c (univ.erase ρ) a (dW p K t z) else 0) +
        (if t = a then Uop p LL c (univ.erase ρ) s (dW p K a z) else 0) := by
    intro a
    have h1 := raising_comm_holds p K r LL c (univ.erase ρ) a s t (dW p K a z) hv hs ht
    have h2 : dW p K a (glAct p LL (K + 1) s t z) =
        glAct p LL (K + 1) s t (dW p K a z) + (if s = a then dW p K t z else 0) := pderiv_glAct LL hv s t a z
    rw [h2, map_add, ← h1]
    split_ifs <;> simp
  unfold Omega
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos hs, if_pos ht]
  abel
end Formalism.InvariantFactorPaths.L4
