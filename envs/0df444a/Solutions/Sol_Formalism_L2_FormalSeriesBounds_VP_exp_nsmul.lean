-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.exp_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:59.479239+00:00
-- url     : https://prove2.me/submissions/08782680-b788-4b5e-8d4b-1f94ea65e6fa

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_exp_add
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
namespace VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
private theorem coeff_mul_eq_zero_of_degree_lt_add_character_germs {σ : Type} {p q : MvPowerSeries σ C} {k l : ℕ}
    (hp : ∀ a : σ →₀ ℕ, a.degree < k → MvPowerSeries.coeff a p = 0)
    (hq : ∀ a : σ →₀ ℕ, a.degree < l → MvPowerSeries.coeff a q = 0) :
    ∀ a : σ →₀ ℕ, a.degree < k + l → MvPowerSeries.coeff a (p * q) = 0 := by
  intro a ha
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = a.degree := by rw [← hx, map_add]
  by_cases h1 : x.1.degree < k
  · rw [hp _ h1, zero_mul]
  · rw [hq _ (by omega), mul_zero]
private theorem coeff_pow_eq_zero_of_degree_lt_character_germs' {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ k : ℕ, ∀ a : σ →₀ ℕ, a.degree < k → MvPowerSeries.coeff a (f ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ k ih =>
    rw [pow_succ]
    refine coeff_mul_eq_zero_of_degree_lt_add_character_germs ih fun a ha => ?_
    have h0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp (by omega)
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
private theorem coeff_mvExp_eq_sum_range_of_degree_le {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (m : σ →₀ ℕ) (N : ℕ) (hN : m.degree ≤ N) :
    MvPowerSeries.coeff m (mvExp f) =
      ∑ k ∈ Finset.range (N + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) := by
  show ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) = _
  rw [← Finset.sum_range_add_sum_Ico _ (show m.degree + 1 ≤ N + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (m.degree + 1) (N + 1)) (fun k hk => by
    rw [Finset.mem_Ico] at hk
    rw [coeff_pow_eq_zero_of_degree_lt_character_germs' hf k m (by omega), zero_div]), add_zero]
private theorem mvExp_zero_character_germs {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp_eq_sum_range_of_degree_le (map_zero _) m m.degree le_rfl, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, zero_div]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
variable (Y : FBChart C V O dd)
section Subst
variable [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
  {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
  (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
end Subst
section Three
variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
include ha hb hc
end Three
end VP
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {σ : Type} {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) (k : ℕ) :
    mvExp ((k : C) • f) = mvExp f ^ k := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact mvExp_zero_character_germs
  | succ k ih =>
    have hk : MvPowerSeries.constantCoeff ((k : C) • f) = 0 := by simp [hf]
    rw [Nat.cast_succ, add_smul, one_smul, exp_add hk hf, ih, pow_succ]
end Formalism.L2.FormalSeriesBounds.VP
