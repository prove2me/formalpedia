-- Prove2me | solution 1 for Formalism.UG.P.rational_points_le_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:57.147844+00:00
-- url     : https://prove2.me/submissions/41562e12-4ad9-461b-9f23-4d3023e82647

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Theorems.Thm_Formalism_UG_P_base_change_mem_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.RatPtsLe := by
  intro F E _ _ _ n _ _ σ J R _ _ x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hc : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE (F := F) R) := by
    ext e
    simp [inclE, sigR, Algebra.TensorProduct.map_tmul]
  exact base_change_mem_holds E (E ⊗[F] R) n (σ : E →+* E) (sigR σ R) (inclE (F := F) R) hc J g hg
end Formalism.UG.P
