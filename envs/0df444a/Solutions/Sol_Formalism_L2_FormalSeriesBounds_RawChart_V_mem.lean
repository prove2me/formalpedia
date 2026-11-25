-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.V_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:29.413862+00:00
-- url     : https://prove2.me/submissions/41bf8e77-9943-4740-85cf-c3fa595a3a41

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_TySet_repar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow_of_not_dvd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
section TyS
variable {l : ℕ} (hl : 2 ≤ l)
include hl
end TyS
section Repar
end Repar
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
private theorem ge_zero_lemma (V : VF C) : V.Ge 0 (0 : C) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top
end RawChart
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end RawChart
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow 1 x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  refine X.TySet_repar (PowerSeries.X ^ V.l) (by simp [hl0.ne']) (fun f hf m => ?_) hx (fun m => ?_)
  · by_cases hd : V.l ∣ m
    · obtain ⟨q, rfl⟩ := hd
      rw [coeff_subst_X_pow hl0]
      exact hf q
    · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]
      exact ge_zero_lemma V
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · cases s with
      | zero =>
        rw [pow_zero, coeff_subst_X_pow_of_not_dvd hl0 _ _ V.l_prime.not_dvd_one]
        simp [Vpow]
      | succ s =>
        rw [pow_succ', coeff_subst_X_pow hl0, coeff_tyS_pow hl]
        simp [Vpow]
    · by_cases hd : V.l ∣ k
      · obtain ⟨q, rfl⟩ := hd
        rw [coeff_subst_X_pow hl0, coeff_tyS_of_ne _ _ (fun s hs => hk (s + 1) (by rw [pow_succ', hs]))]
      · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]
end Formalism.L2.FormalSeriesBounds.RawChart
