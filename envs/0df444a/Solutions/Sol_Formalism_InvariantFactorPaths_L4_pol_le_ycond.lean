-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pol_le_ycond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:28:54.909781+00:00
-- url     : https://prove2.me/submissions/5bec8216-d0b9-462b-b687-25cc7b1016bf

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedSaturationHolds
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol


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
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {r N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (c : ℤ) (hc : (LL.total : ℤ) ≤ c) :
    Pol p r LL ≤ YCond p LL j ((c : ℤ) : WithTop ℤ) := by
  unfold YCond
  apply le_sSup
  refine ⟨?_, fun c d x hx => Formalism.CountingSumsFrames.glAct_pol (p := p) LL j c d x hx⟩
  intro x hx
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hx
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hd := hx hm
  show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((c : ℤ) : WithTop ℤ)
  rw [WithTop.coe_le_coe]
  refine le_trans ?_ hc
  calc wt LL j 0 m ≤ ∑ i, (LL.deg i : ℤ) := Finset.sum_le_sum fun i _ => by
        have h1 : (m (i, 0) : ℤ) ≤ LL.deg i := by
          rw [← hd i]
          exact_mod_cast Finset.single_le_sum (fun c _ => Nat.zero_le (m (i, c))) (Finset.mem_univ 0)
        split_ifs <;> omega
    _ = (LL.total : ℤ) := by unfold Letters.total; push_cast; rfl
end Formalism.InvariantFactorPaths.L4
