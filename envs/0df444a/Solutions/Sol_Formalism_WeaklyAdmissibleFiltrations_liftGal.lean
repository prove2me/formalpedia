-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.liftGal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:03.263628+00:00
-- url     : https://prove2.me/submissions/2dbb31be-b7cd-4272-a36b-ff3bcfb2088e

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_CoboundaryTransfers_WachBridges
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_LiftGal
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_cocycle_mem_Zf
import Theorems.Thm_Formalism_CoboundaryTransfers_finiteClassesLift_holds
import Theorems.Thm_Formalism_CoboundaryTransfers_lift_wach


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : LiftGal := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V V' _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' _ _ _ _ _ _ _ L L' F A D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Bw M W₀ W₁ W₂ S cl₁ cl₂ eW e δ R a k u hL1 hL2 hNat hInt hW hQ hk ha hδ hR hZ hZu hgr hφ
  have hLift := Formalism.CoboundaryTransfers.lift_wach O A Bw M D₀ D₁ D₂ W₀ W₁ W₂ S e hW hQ δ R a k u hk ha hδ hR hZ
    hZu hgr hφ
  refine Formalism.CoboundaryTransfers.finiteClassesLift_holds O A Bw M D₀ D₁ D₂ W₀ W₁ W₂ S (LatticeCohomology L) (LatticeCohomology L') cl₁ cl₂
    (latticeFiniteCohomology PD L) (latticeFiniteCohomology PD L') F.H1map eW _ hNat ?_ hInt hLift
  intro pr hc
  rw [← hL1.2]
  exact ⟨pr, W₁.cocycle_mem_Zf hc, rfl⟩
end Formalism.WeaklyAdmissibleFiltrations
