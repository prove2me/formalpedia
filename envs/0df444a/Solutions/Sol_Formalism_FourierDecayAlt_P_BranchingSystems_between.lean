-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:16.189463+00:00
-- url     : https://prove2.me/submissions/bd5ebdf4-c480-4a91-84f7-5b9637805acc

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.BranchingSystems
theorem _root_.solution {n : ℕ} {L : Fin (n + 1) → ℤ} (hL : StrictAnti L) (i : Fin n) {x : ℤ}
    (h1 : L i.succ < x) (h2 : x < L i.castSucc) (j : Fin (n + 1)) : x ≠ L j := by
  intro hx
  subst hx
  rcases le_or_gt j i.castSucc with hj | hj
  · have h3 := hL.antitone hj
    omega
  · have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hj
    have h3 := hL.antitone hj'
    omega
end Formalism.FourierDecayAlt.P.BranchingSystems
