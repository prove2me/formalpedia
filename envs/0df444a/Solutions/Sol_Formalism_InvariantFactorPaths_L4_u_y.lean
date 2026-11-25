-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.u_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:15.908278+00:00
-- url     : https://prove2.me/submissions/36131cb6-bec2-4d77-a07f-309f9e77ae85

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_degree_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_keeps_early_letters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_keeps_last_letter
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_late
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_mono


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
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (a : Fin (s + 1)) (o : ℕ) :
    ∀ h ∈ Y p (setLast LL o) J M, Uop p LL c univ a h ∈ Y p (setLast LL (o + 1)) J M := by
  intro h hh
  rw [mem_y] at hh ⊢
  refine ⟨raising_degree_holds p K (s + 1) LL c univ a o h hh.1, fun k => ?_⟩
  by_cases hk : K + 1 ≤ J k
  · have h1 : h ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ) := by
      have := hh.2 k0
      rw [ycond_late _ (J k0) hk0, hc] at this
      exact this
    rw [ycond_late _ (J k) hk]
    exact ycond_mono LL (K + 1) _ _ (hc ▸ hmin k hk) (raising_keeps_last_letter p K (s + 1) LL c a hv h h1)
  · exact raising_keeps_early_letters p K (s + 1) LL c univ a (J k) (M k) (by omega) h (hh.2 k)
end Formalism.InvariantFactorPaths.L4
