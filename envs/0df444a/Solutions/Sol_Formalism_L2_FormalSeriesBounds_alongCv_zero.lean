-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.alongCv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:31:38.094167+00:00
-- url     : https://prove2.me/submissions/4589b6c7-4f46-40af-8b24-590151e1e7cb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    alongCv (fun _ : σ => (0 : PowerSeries C)) f = 0 := by
  unfold alongCv
  have ha : MvPowerSeries.HasSubst (fun _ : σ => (0 : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_subst ha, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (d.prod fun _ e => (0 : PowerSeries C) ^ e) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)
    simp only [h0, map_zero, smul_zero]
end Formalism.L2.FormalSeriesBounds
