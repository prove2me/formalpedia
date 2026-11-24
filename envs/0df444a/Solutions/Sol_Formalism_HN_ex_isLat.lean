-- Prove2me | solution 1 for Formalism.HN.ex_isLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:22.661808+00:00
-- url     : https://prove2.me/submissions/45d55333-b34a-4b24-a037-05698ba58369

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_zl_id
import Theorems.Thm_Formalism_HN_PolygonExample_discrete_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2
namespace Formalism.HN
theorem _root_.solution (N : Submodule ℤ E2) (hN : N ≤ Lx) : IsLat ρx N := ⟨fun x _ y _ h => h, by rw [zl_id]; exact discrete_of_le N hN⟩
end Formalism.HN
