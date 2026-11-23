-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.CostOK.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:12.125727+00:00
-- url     : https://prove2.me/submissions/50584a3b-3a20-47c5-bfb7-0dbd295d84d4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open Formalism.MainNotions.PlaneGram.CostOK
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
namespace Formalism.MainNotions.PlaneGram.CostOK
theorem _root_.solution (hC : CostOK TotallyRealRoots) (n : ℕ) : TotallyRealRoots n (fun _ => 0) := by
  have h0 := hC.smul 0 (0 : K) _ hC.one
  simp only [zero_mul] at h0
  exact hC.mono 0 n _ (Nat.zero_le n) h0
end Formalism.MainNotions.PlaneGram.CostOK
