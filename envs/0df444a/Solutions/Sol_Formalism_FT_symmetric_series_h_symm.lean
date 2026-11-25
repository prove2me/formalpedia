-- Prove2me | solution 1 for Formalism.FT.symmetric_series_h_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:00.788865+00:00
-- url     : https://prove2.me/submissions/ebf5dbfc-8483-4342-9e1a-febc6b1d73ae

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_hasSubst_hv
import Theorems.Thm_Formalism_FT_SymmetricSeries_exists_G
import Theorems.Thm_Formalism_FT_SymmetricSeries_G_unique

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
namespace Formalism.FT
theorem _root_.solution : Formalism.FT.SymmSeriesHsymm := by
  intro R _ n F hF
  obtain ⟨G, hG⟩ := Formalism.FT.SymmetricSeries.exists_G F hF
  refine ⟨G, hG, fun G' hG' => ?_⟩
  have hG'' : G'.subst (Formalism.FT.SymmetricSeries.hv R n) = F := hG'
  have h0 : (G' - G).subst (Formalism.FT.SymmetricSeries.hv R n) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom Formalism.FT.SymmetricSeries.hasSubst_hv, map_sub,
      MvPowerSeries.coe_substAlgHom Formalism.FT.SymmetricSeries.hasSubst_hv, hG'', hG, sub_self]
  exact sub_eq_zero.mp (Formalism.FT.SymmetricSeries.G_unique _ h0)
end Formalism.FT
