-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.coeff_single_subst_of_low_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:49.88407+00:00
-- url     : https://prove2.me/submissions/0a00c177-3d3a-47aa-9b99-f69316017646

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
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
private theorem cs_mul_lemma {τ : Type} (A B : MvPowerSeries τ C) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (A * B) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg := congrArg Finsupp.degree hp
  rw [map_add, deg_single_lemma_0] at hdeg
  rcases Nat.eq_zero_or_pos p.1.degree with h0 | h0
  · rw [deg_zero_lemma_0 p.1 h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
  · have h1 : p.2.degree = 0 := by omega
    rw [deg_zero_lemma_0 p.2 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB, mul_zero]
private theorem cs_prod_lemma_2 {σ τ : Type} (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : σ →₀ ℕ) (he : e ≠ 0) :
    MvPowerSeries.constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (Finsupp.ext h)
  rw [map_finsuppProd]
  simp only [map_pow, ha0, Finsupp.prod]
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)
private theorem cs_prod_lemma_3 {σ τ : Type} (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : σ →₀ ℕ) (he : 2 ≤ e.degree) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (e.prod fun s n => a s ^ n) = 0 := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finsupp.ext h)
  have hle : Finsupp.single s 1 ≤ e := by
    rw [Finsupp.single_le_iff]
    omega
  have hsplit : e = Finsupp.single s 1 + (e - Finsupp.single s 1) := (add_tsub_cancel_of_le hle).symm
  have hdeg : 1 ≤ (e - Finsupp.single s 1).degree := by
    have h2 := congrArg Finsupp.degree hsplit
    rw [map_add, deg_single_lemma_0] at h2
    omega
  have hne' : e - Finsupp.single s 1 ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  rw [hsplit, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun s n => a s ^ n) (pow_zero _), pow_one]
  exact cs_mul_lemma _ _ (ha0 s) (cs_prod_lemma_2 a ha0 _ hne') c
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
theorem _root_.solution {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (r : MvPowerSeries σ C)
    (hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e r = 0) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a r) = 0 := by
  classical
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e.degree < 2
  · rw [hr e he, zero_smul]
  · rw [cs_prod_lemma_3 a ha0 e (by omega) c, smul_zero]
end Formalism.L2.FormalSeriesBounds.FormalGermZero
