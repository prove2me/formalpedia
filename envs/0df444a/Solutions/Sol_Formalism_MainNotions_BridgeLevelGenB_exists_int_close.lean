-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenB.exists_int_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:26.099977+00:00
-- url     : https://prove2.me/submissions/1b6c38fb-efcd-4cb0-bea6-e1224f34525e

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGenB_val_int
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.MainNotions.BridgeLevelGenB
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : Valued.v x ≤ 1)
    {g : 𝓞 F} (hg : g ≠ 0) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < v.intValuation g := by
  have hγ : v.intValuation g ≠ 0 := intValuation_ne_zero v g hg
  set w : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F g) with hw
  have hwv : Valued.v w = v.intValuation g := val_int v g
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hwv
    exact hγ hwv.symm
  have hr0 : (Valued.v : Valuation (v.adicCompletion F) _).restrict w ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact hw0
  have hnhds : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v w} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    exact ⟨Units.mk0 _ hr0, fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩
  obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (R := 𝓞 F) F v) x) _ hnhds
  simp only [Set.mem_ofPred_eq] at hy
  rw [hwv] at hy
  have hg1 : v.intValuation g ≤ 1 := intValuation_le_one v g
  have hk : v.valuation F k ≤ 1 := by
    rw [← PI.WAU.val_algebraMap_F]
    calc Valued.v (algebraMap F (v.adicCompletion F) k)
        = Valued.v ((algebraMap F (v.adicCompletion F) k - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) k - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le (hy.le.trans hg1) hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk (Units.mk0 _ hγ)
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) k -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < v.intValuation g := by
    rw [← map_sub, PI.WAU.val_algebraMap_F, ← Valuation.map_neg, neg_sub]
    simpa using ha
  calc Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      = Valued.v ((x - algebraMap F (v.adicCompletion F) k) + (algebraMap F (v.adicCompletion F) k -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < _ := by
      refine max_lt ?_ h2
      rw [← Valuation.map_neg, neg_sub]; exact hy
end Formalism.MainNotions.BridgeLevelGenB
