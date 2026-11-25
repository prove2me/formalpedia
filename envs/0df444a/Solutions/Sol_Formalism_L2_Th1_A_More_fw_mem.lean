-- Prove2me | solution 1 for Formalism.L2.Th1.A.More.fw_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:24.787665+00:00
-- url     : https://prove2.me/submissions/384aa7ee-13d4-4c4c-afb5-ae803dfce2c1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_fw


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
open Formalism.L2.Th1.A.More
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)
namespace Formalism.L2.Th1.A.More
theorem _root_.solution (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S)
    (n : ℕ) : coeff n (fw W) ∈ S := by
  have e : (⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩ :
      WeierstrassCurve S).map S.subtype = W := by
    ext <;> rfl
  rw [← e, ← CurveSer.map_fw, coeff_map]
  exact SetLike.coe_mem _
end Formalism.L2.Th1.A.More
