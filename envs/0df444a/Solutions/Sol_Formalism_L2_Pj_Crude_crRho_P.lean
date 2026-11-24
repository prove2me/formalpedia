-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crRho_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:08.663074+00:00
-- url     : https://prove2.me/submissions/21dae864-6e14-40fe-bdeb-262e94869f66

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crRho_minor
import Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_pow
import Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (hβ : Function.Injective β) : crIsMono (crRho R β (crP r n R β a)) := by
  unfold crP
  rw [map_prod]
  refine crIsMono_prod _ _ fun σ _ => ?_
  rw [map_prod]
  refine crIsMono_prod _ _ fun kk _ => ?_
  rw [map_pow]
  refine crIsMono_pow ?_ _
  rw [AlgHom.map_det, crRho_minor R β hβ σ kk, Matrix.det_diagonal]
  exact crIsMono_prod _ _ fun q _ => ⟨Finsupp.single _ 1, rfl⟩
end Formalism.L2.Pj.Crude
