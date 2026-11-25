-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.mfact_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:31:49.544608+00:00
-- url     : https://prove2.me/submissions/89144cb4-ebf2-4a81-89e6-5035628fe3e1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet

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
theorem _root_.solution (m : σ →₀ ℕ) (x : σ) :
    mfact (m + Finsupp.single x 1) = (m x + 1) * mfact m := by
  unfold mfact
  set s := insert x m.support with hs
  have hsub : (m + Finsupp.single x 1).support ⊆ s := by
    intro y hy
    rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
    · exact Finset.mem_insert_of_mem h
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_insert_self _ _
  rw [Finsupp.prod_of_support_subset (m + Finsupp.single x 1) hsub _ (fun _ _ => Nat.factorial_zero),
    Finsupp.prod_of_support_subset m (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)]
  have hx : x ∈ s := Finset.mem_insert_self _ _
  rw [← Finset.mul_prod_erase s _ hx, ← Finset.mul_prod_erase s (fun y => (m y).factorial) hx]
  have hrest : ∏ y ∈ s.erase x, ((m + Finsupp.single x 1 : σ →₀ ℕ) y).factorial = ∏ y ∈ s.erase x, (m y).factorial :=
    Finset.prod_congr rfl fun y hy => by
      rw [Finset.mem_erase] at hy
      simp [Finsupp.single_apply, Ne.symm hy.1]
  rw [hrest]
  simp [Nat.factorial_succ]
  ring
end Formalism.L2.FormalSeriesBounds
