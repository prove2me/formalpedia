-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.mem_iff_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:40:48.163934+00:00
-- url     : https://prove2.me/submissions/6355fe18-a24a-46de-98ba-aaed380e49e1

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
variable {S : Subring K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M) {X : V}
    (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) (x : V) :
    x ∈ M ↔ coef h X x ∈ S ∧ (proj h X hXu.1 x : V) ∈ M := by
  constructor
  · intro hx
    have hc : coef h X x ∈ S := by
      rw [coef_apply]
      exact S.mul_mem hXu.2.2 (hM.int X hXM x hx)
    refine ⟨hc, ?_⟩
    rw [proj_val]
    exact M.sub_mem hx (hM.smul_mem _ hc X hXM)
  · rintro ⟨hc, hp⟩
    rw [decomp h X hXu.1 x]
    exact M.add_mem (hM.smul_mem _ hc X hXM) hp
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
