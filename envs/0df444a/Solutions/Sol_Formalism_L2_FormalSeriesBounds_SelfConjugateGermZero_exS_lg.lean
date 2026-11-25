-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.exS_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:41:24.67727+00:00
-- url     : https://prove2.me/submissions/dd3857c4-51f8-4eb6-9839-62c5f69b51f4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_hasSubst_col
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_uncurry_log_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lg_self
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
namespace SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]
private theorem prod_X_lemma {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
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
private theorem un1_lift_lemma_2 (f : MvPowerSeries (Fin 1 × Fin dd) C) :
    MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      (un1 f) = f := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  have hμ : (μ.mapDomain Prod.snd).mapDomain (Prod.mk (0 : Fin 1)) = μ := by
    rw [← Finsupp.mapDomain_comp]
    have hc : (Prod.mk (0 : Fin 1) ∘ (Prod.snd : Fin 1 × Fin dd → Fin dd)) = id := by
      funext p
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [hc, Finsupp.mapDomain_id]
  rw [finsum_eq_single _ (μ.mapDomain Prod.snd)]
  · rw [if_pos hμ.symm, smul_eq_mul, mul_one]
    show MvPowerSeries.coeff ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x))) f = _
    rw [show (fun x : Fin dd => ((0 : Fin 1), x)) = Prod.mk (0 : Fin 1) from rfl, hμ]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h
    apply hd
    rw [h, ← Finsupp.mapDomain_comp,
      show (Prod.snd ∘ Prod.mk (0 : Fin 1) : Fin dd → Fin dd) = id from rfl, Finsupp.mapDomain_id]
private theorem ev1_lemma_3 {n : ℕ} (Q : Pt C n dd) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : PS C 1 dd) : ev ![Q] f = MvPowerSeries.subst Q (un1 f) := by
  have hA : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hB : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => (![Q] : Fin 1 → Pt C n dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨a, i⟩
      fin_cases a
      exact hQ i)
  unfold ev
  conv_lhs => rw [← un1_lift_lemma_2 f]
  rw [MvPowerSeries.subst_comp_subst_apply hA hB]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hB]
  rfl
variable {d : ℕ} {I0 : Type} [Fintype I0]
private theorem un1_lift_lemma_4 (h : MvPowerSeries (Fin dd) C) :
    un1 (MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      h) = h := by
  classical
  ext μ
  show MvPowerSeries.coeff (μ.mapDomain (Prod.mk (0 : Fin 1)))
    (MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) h) =
      MvPowerSeries.coeff μ h
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  rw [finsum_eq_single _ μ]
  · rw [if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h'
    exact hd (Finsupp.mapDomain_injective (Prod.mk_right_injective (0 : Fin 1)) h').symm
private theorem inner_lemma_5 (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j : Fin dd => un1 (Y.lg j)) (un1 (Y.ex i)) =
      (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  have hA : MvPowerSeries.HasSubst
      (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hU : MvPowerSeries.HasSubst (fun j : Fin dd => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (uncurry_log_constantCoeff Y)
  have hlg0 : ∀ j, MvPowerSeries.constantCoeff (Y.lg j) = 0 := fun j => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.lg_lin j 0 (by simp)]
    simp
  have e : ev (n := 1) ![Y.lg] (Y.ex i) = MvPowerSeries.X ((0 : Fin 1), i) := congrFun Y.ex_lg i
  rw [ev1_lemma_3 _ hlg0] at e
  have hL : ∀ g : MvPowerSeries (Fin dd) C,
      MvPowerSeries.subst (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C))
        (MvPowerSeries.subst (fun j : Fin dd => un1 (Y.lg j)) g) = MvPowerSeries.subst Y.lg g := fun g => by
    rw [MvPowerSeries.subst_comp_subst_apply hU hA]
    congr 1
    funext j
    exact un1_lift_lemma_2 (Y.lg j)
  rw [← un1_lift_lemma_4 (MvPowerSeries.subst (fun j : Fin dd => un1 (Y.lg j)) (un1 (Y.ex i))), hL, e,
    ← un1_lift_lemma_4 (MvPowerSeries.X i : MvPowerSeries (Fin dd) C), MvPowerSeries.subst_X hA]
end SelfConjugateGermZero
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable {d : ℕ} {I0 : Type} [Fintype I0]
namespace Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
theorem _root_.solution (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) :
    MvPowerSeries.subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (MvPowerSeries.X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  have hLg0 : ∀ y : Fin 2 × Fin dd, MvPowerSeries.constantCoeff ((Y.rawSelf p).lg y) = 0 := fun y => by
    rw [lg_self Y p y, cc_subst_lemma _ (fun _ => by simp)]
    exact uncurry_log_constantCoeff Y y.2
  have hLg : MvPowerSeries.HasSubst (Y.rawSelf p).lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hLg0
  have hc : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X (x.1, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := hasSubst_col x.1
  have hU : MvPowerSeries.HasSubst (fun i : Fin dd => un1 (Y.lg i)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (uncurry_log_constantCoeff Y)
  show MvPowerSeries.subst (Y.rawSelf p).lg (MvPowerSeries.subst
      (fun i : Fin dd => (MvPowerSeries.X (x.1, i) : MvPowerSeries (Fin 2 × Fin dd) C)) (un1 (Y.ex x.2))) =
    MvPowerSeries.X x
  rw [MvPowerSeries.subst_comp_subst_apply hc hLg]
  simp only [MvPowerSeries.subst_X hLg, lg_self Y p]
  rw [← MvPowerSeries.subst_comp_subst_apply hU hc, inner_lemma_5 Y x.2, MvPowerSeries.subst_X hc]
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
