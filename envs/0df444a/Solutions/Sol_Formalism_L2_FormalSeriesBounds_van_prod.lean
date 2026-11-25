-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.van_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:07.761838+00:00
-- url     : https://prove2.me/submissions/1a3f59fc-fa26-483b-b4f5-e00251f170fd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_right


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ : Type} {T : Set τ} {a : σ → MvPowerSeries τ C} {e : σ →₀ ℕ} {s : σ} (hs : s ∈ e.support)
    (ha : Van T (a s)) : Van T (e.prod fun s m => a s ^ m) := by
  unfold Finsupp.prod
  rw [← Finset.mul_prod_erase _ _ hs]
  apply Van.mul_right
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs)
  show Van T (a s ^ e s)
  rw [hm, pow_succ']
  exact ha.mul_right _
end Formalism.L2.FormalSeriesBounds
