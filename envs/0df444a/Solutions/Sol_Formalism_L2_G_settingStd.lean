-- Prove2me | solution 1 for Formalism.L2.G.settingStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:17.863913+00:00
-- url     : https://prove2.me/submissions/512597be-cba4-4039-a60d-8db56f85d9bc

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective
import Theorems.Thm_Formalism_L2_G_wU_sq
import Theorems.Thm_Formalism_L2_G_sq_OO
import Theorems.Thm_Formalism_L2_G_Quad_algebraMap_finite
import Theorems.Thm_Formalism_L2_G_Quad_card_res
import Theorems.Thm_Formalism_L2_G_card_quot_WQ
import Theorems.Thm_Formalism_L2_G_card_quotient_extRing
import Theorems.Thm_Formalism_L2_G_frob_WQ
import Theorems.Thm_Formalism_L2_G_jW_finite
import Theorems.Thm_Formalism_L2_G_sig_alg
import Theorems.Thm_Formalism_L2_G_sig_period
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__GatR_isAdicComplete_e5d83f2ed8a2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
namespace Formalism.L2.G
theorem _root_.solution (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    UnramifiedQuadraticSetting p n (WQ p n) (QQ p n) (OO p n) (KO p n) (iota p n) (sig p n) (jO p n) (wU p n) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, GatR.om_irreducible (WittVector.irreducible p), ?_, sq_OO p n (by omega)⟩
  · exact
    { prime := hp.out
      five_le := h5
      two_le := h2
      even := he
      frac_alt := inferInstance
      frac_O := inferInstance
      p_unif := WittVector.irreducible p
      res_card := card_quot_WQ p n
      eq_sum_herm_smul_frame_of_inW := inferInstance
      frob := fun x => by
        obtain ⟨y, hy⟩ := frob_WQ p n x
        exact ⟨y, by rw [sig_alg, hy]⟩
      period := sig_period p n
      ι_comp := fun x => IsFractionRing.lift_algebraMap (inj_WK p n) x
      finite := (Quad.algebraMap_finite _).comp (jW_finite p n)
      complete_O := GatR.isAdicComplete (WittVector.irreducible p) inferInstance
      w_sq := wU_sq p n }
  · exact (Quad.card_res _).trans (card_quotient_extRing p n)
end Formalism.L2.G
