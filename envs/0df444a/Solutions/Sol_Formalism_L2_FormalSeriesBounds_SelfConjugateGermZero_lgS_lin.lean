-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.lgS_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:32:52.147296+00:00
-- url     : https://prove2.me/submissions/c8f971cc-4081-4d04-abe8-d2f209766126

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_uncurry_log_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lg_self
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_subst_lin
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
variable {d : ℕ} {I0 : Type} [Fintype I0]
private theorem deg_single_lemma_0 {τ : Type} (c : τ) (n : ℕ) : Finsupp.degree (Finsupp.single c n) = n := by
  first
  | exact Finsupp.degree_single c n
  | simp [Finsupp.degree_single]
  | simp [Finsupp.degree]
  | (classical
     unfold Finsupp.degree
     by_cases h : n = 0 <;> simp [h])
private theorem deg_zero_lemma_0 {τ : Type} (d : τ →₀ ℕ) (h : Finsupp.degree d = 0) : d = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff d).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h
  | simpa using h
private theorem deg_map_lemma_6 {α β : Type} (f : α → β) (μ : α →₀ ℕ) :
    Finsupp.degree (μ.mapDomain f) = Finsupp.degree μ := by
  classical
  refine Finsupp.induction μ ?_ ?_
  · simp
  · intro a b g _ _ ih
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single, deg_single_lemma_0, deg_single_lemma_0]
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
theorem _root_.solution (Y : FBChart C V O dd) (p : SelfData Y d I0) (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ)
    (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ ((Y.rawSelf p).lg x) = MvPowerSeries.coeff μ (MvPowerSeries.X x) := by
  classical
  have hdeg : μ.degree = 0 ∨ μ.degree = 1 := by omega
  rcases hdeg with h0 | h1
  · rw [deg_zero_lemma_0 μ h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lg_self Y p x, cc_subst_lemma _ (fun _ => by simp),
      uncurry_log_constantCoeff, MvPowerSeries.constantCoeff_X]
  · obtain ⟨c, rfl⟩ : ∃ c, μ = Finsupp.single c 1 := by
      have hne : μ ≠ 0 := by
        rintro rfl
        simp at h1
      obtain ⟨c, hc⟩ : ∃ c, μ c ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (Finsupp.ext h)
      refine ⟨c, ?_⟩
      have hle : Finsupp.single c 1 ≤ μ := by
        rw [Finsupp.single_le_iff]
        omega
      have hsplit : μ = Finsupp.single c 1 + (μ - Finsupp.single c 1) := (add_tsub_cancel_of_le hle).symm
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add, deg_single_lemma_0, h1] at h2
      have h3 : μ - Finsupp.single c 1 = 0 := deg_zero_lemma_0 _ (by omega)
      rw [h3, add_zero] at hsplit
      exact hsplit
    have hc : ∀ s : Fin dd, MvPowerSeries.constantCoeff
        ((MvPowerSeries.X (x.1, s) : MvPowerSeries (Fin 2 × Fin dd) C)) = 0 := fun _ => by simp
    rw [lg_self Y p x]
    refine (FormalGermZero.coeff_single_subst_lin _ hc (un1 (Y.lg x.2)) x.2 ?_ c).trans rfl
    intro μ' hμ'
    have hA : MvPowerSeries.HasSubst
        (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have hXL : (MvPowerSeries.X ((0 : Fin 1), x.2) : MvPowerSeries (Fin 1 × Fin dd) C) =
        MvPowerSeries.subst (fun j : Fin dd => (MvPowerSeries.X ((0 : Fin 1), j) : MvPowerSeries (Fin 1 × Fin dd) C))
          (MvPowerSeries.X x.2 : MvPowerSeries (Fin dd) C) := (MvPowerSeries.subst_X hA x.2).symm
    show MvPowerSeries.coeff (μ'.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg x.2) = _
    rw [Y.lg_lin x.2 _ (by rw [deg_map_lemma_6]; exact hμ'), hXL]
    exact congrArg (MvPowerSeries.coeff μ') (un1_lift_lemma_4 (MvPowerSeries.X x.2 : MvPowerSeries (Fin dd) C))
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
