-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:51.672298+00:00
-- url     : https://prove2.me/submissions/c9b0ec05-283c-4fcf-b35e-628487f4ae24

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mvExp_partial
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_of_ordGE
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst


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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {h : MvPowerSeries σ C} (hh : OrdGE 1 h) : subst a (mvExp h) = mvExp (subst a h) := by
  ext e
  have hsh : OrdGE 1 (subst a h) := ordGE_subst ha hh
  rw [coeff_subst_congr ha (F := mvExp h)
      (G := ∑ k ∈ Finset.range (e.degree + 1), ((k.factorial : C)⁻¹) • h ^ k) (N := e.degree)
      (fun d hd => coeff_mvExp_partial hh e.degree d hd) e le_rfl,
    coeff_mvExp_partial hsh e.degree e le_rfl]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_ordGE ha), map_sum]
  simp only [map_smul, map_pow]
end Formalism.L2.FormalSeriesBounds
