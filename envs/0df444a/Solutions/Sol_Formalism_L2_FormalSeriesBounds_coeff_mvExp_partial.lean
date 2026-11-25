-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_mvExp_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:21.956844+00:00
-- url     : https://prove2.me/submissions/f7b3756d-c903-4c21-a585-c397ef10d2de

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_finset_prod


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
theorem _root_.solution {h : MvPowerSeries σ C} (hh : OrdGE 1 h) (N : ℕ) (m : σ →₀ ℕ)
    (hm : m.degree ≤ N) :
    coeff m (mvExp h) = coeff m (∑ k ∈ Finset.range (N + 1), ((k.factorial : C)⁻¹) • h ^ k) := by
  have hpow : ∀ k, OrdGE k (h ^ k) := by
    intro k
    have := ordGE_finset_prod (Finset.range k) (fun _ => 1) (fun _ => h) (fun _ _ => hh)
    simpa [Finset.prod_const, Finset.card_range] using this
  show (∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_subset (Finset.range_mono (by omega : m.degree + 1 ≤ N + 1)) ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]
  · intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hpow k m (by omega), zero_div]
end Formalism.L2.FormalSeriesBounds
