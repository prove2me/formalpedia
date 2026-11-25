-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.coeff_single_substX_tyS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:51.823729+00:00
-- url     : https://prove2.me/submissions/160d31f4-5a0a-4520-bd07-322e7f78d1a0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
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
namespace FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
private theorem prod_X_lemma_8 {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]
    rfl
  · intro a b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]
section Law
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
end Law
section Sys1
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
end Sys1
end FormalGermZero
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {τ : Type} {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (c c'' : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1)
        (PowerSeries.subst (MvPowerSeries.X c'' : MvPowerSeries τ C) (tyS l a)) =
      if c'' = c then a 0 else 0 := by
  classical
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hcoef : MvPowerSeries.coeff (Finsupp.single () 1) (tyS l a) = a 0 := by
    have hl1 : l ≠ 1 := by omega
    unfold tyS
    first
    | (rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff (R := C) 1 from rfl,
        PowerSeries.coeff_mk]
       simp [Finset.sum_range_succ, hl1])
    | (rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff C 1 from rfl,
        PowerSeries.coeff_mk]
       simp [Finset.sum_range_succ, hl1])
    | (show (∑ s ∈ Finset.range (1 + 1), if l ^ s = 1 then a s else 0) = a 0
       simp [Finset.sum_range_succ, hl1])
  show MvPowerSeries.coeff (Finsupp.single c 1)
      (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C)) (tyS l a)) = _
  rw [MvPowerSeries.coeff_subst ha]
  simp only [prod_X_lemma_8 (fun _ : Unit => c''), MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [finsum_eq_single _ (Finsupp.single () 1)]
  · rw [Finsupp.mapDomain_single]
    by_cases h : c'' = c
    · subst h
      rw [if_pos rfl, if_pos rfl, hcoef]
    · rw [if_neg (fun h' => h ((Finsupp.single_left_injective one_ne_zero h').symm)), if_neg h]
  · intro d hd
    rw [if_neg]
    intro h'
    apply hd
    rw [Finsupp.unique_single d, Finsupp.mapDomain_single] at h'
    rw [Finsupp.unique_single d]
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h' with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [← h2]
    · exact absurd h1 one_ne_zero
end Formalism.L2.FormalSeriesBounds.FormalGermZero
