-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.subst_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:44.590582+00:00
-- url     : https://prove2.me/submissions/76a88a61-59b1-4433-ab1f-ada615b04d0b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_mem_SuppOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {R σ Pl : Type} [CommRing R]
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {τ : Type} {π : σ → Pl} {π' : τ → Pl} {v : Pl} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {f : MvPowerSeries σ R} (hf : f ∈ SuppOn π v)
    (h : ∀ s, π s = v → a s ∈ SuppOn π' v) : MvPowerSeries.subst a f ∈ SuppOn π' v := by
  classical
  intro e he x hx
  rw [MvPowerSeries.coeff_subst ha] at he
  by_contra hxv
  apply he
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : MvPowerSeries.coeff d f = 0
  · rw [hd, zero_smul]
  · have hprod : (d.prod fun s n => a s ^ n) ∈ SuppOn π' v := by
      unfold Finsupp.prod
      exact Subring.prod_mem _ fun s hs => Subring.pow_mem _ (h s ((mem_SuppOn.mp hf) d hd s hs)) _
    have h0 : MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) = 0 := by
      by_contra hne
      exact hxv ((mem_SuppOn.mp hprod) e hne x hx)
    rw [h0, smul_zero]
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
