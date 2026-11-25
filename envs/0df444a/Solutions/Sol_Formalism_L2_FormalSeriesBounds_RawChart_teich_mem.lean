-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.teich_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:04.830662+00:00
-- url     : https://prove2.me/submissions/2ee02561-4d87-4b84-9936-46cedbb9df77

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_TySet_repar
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
private theorem ge_mul_lemma_2 (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) : V.Ge 0 (a * b) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul]
  have h := add_le_add (show ((0 : ℝ) : WithTop ℝ) ≤ V.v a from ha) (show ((0 : ℝ) : WithTop ℝ) ≤ V.v b from hb)
  simpa using h
private theorem ge_zero_pow' (V : VF C) {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero =>
    change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a ^ 0)
    rw [pow_zero, AddValuation.map_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    exact ge_mul_lemma_2 V ih ha
private theorem coeff_subst_smul_X (c : C) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (c • (PowerSeries.X : PowerSeries C)) f) = c ^ n * PowerSeries.coeff n f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [PowerSeries.smul_eq_C_mul])),
    finsum_eq_single _ n]
  · rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_self, smul_eq_mul]
    ring
  · intro d hd
    rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero, smul_zero]
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
theorem _root_.solution (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) (x : ℕ → I g ⊕ JJ I g → C)
    (hx : x ∈ X.TySet V g) : teich V.l c x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  refine X.TySet_repar (c • PowerSeries.X) (by simp [PowerSeries.smul_eq_C_mul]) (fun f hf n => ?_) hx (fun m => ?_)
  · rw [coeff_subst_smul_X]
    exact ge_mul_lemma_2 V (ge_zero_pow' V hc n) (hf n)
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · rw [coeff_subst_smul_X, coeff_tyS_pow hl]
      rfl
    · rw [coeff_subst_smul_X, coeff_tyS_of_ne _ _ hk, mul_zero]
end Formalism.L2.FormalSeriesBounds.RawChart
