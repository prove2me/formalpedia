-- Prove2me | solution 1 for Formalism.HN.imageStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:56.659738+00:00
-- url     : https://prove2.me/submissions/e19d63d8-d139-4712-afed-b8d32f81c07f

import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_StatementCor
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Theorems.Thm_Formalism_HN_hnStep_spec
import Theorems.Thm_Formalism_HN_slopeIneq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : ImageStep := by
  intro R ι W F _ _ _ _ _ _ V E _ _ _ _ _ ρ ρ' L M s φ C θ hL hM hC
  refine iSup₂_le fun i hi => ?_
  by_cases h0 : φ i = 0
  · simp [h0]
  · have hLi : L i ≠ ⊥ := by
      intro hb
      apply h0
      refine LinearMap.ext fun x => ?_
      have : x = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb x x.2)
      simp [this]
    have hN0 : (LinearMap.range (φ i)).map M.subtype ≠ ⊥ := by
      intro hb
      apply h0
      refine LinearMap.ext fun x => Subtype.ext ?_
      have hx : ((φ i x : M) : W) ∈ (LinearMap.range (φ i)).map M.subtype :=
        ⟨φ i x, ⟨x, rfl⟩, rfl⟩
      rw [hb, Submodule.mem_bot] at hx
      simp [hx]
    have hθ : θ ≤ muMin ρ' ((LinearMap.range (φ i)).map M.subtype) :=
      ((hC i hi).2.2 hLi).trans ((slopeIneq R (V i) W (E i) F (ρ i) ρ' (L i) M (hL i hi) hM (φ i)
        (C i) (hC i hi).1 (hC i hi).2.1).1 h0).1
    exact (hnStep_spec R W F ρ' M hM θ).2.2.1 _ (Submodule.map_subtype_le _ _) hN0 hθ
end Formalism.HN
