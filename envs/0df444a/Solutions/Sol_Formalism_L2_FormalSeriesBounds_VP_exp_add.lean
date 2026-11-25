-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.exp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:59.636809+00:00
-- url     : https://prove2.me/submissions/52b030ed-e3c0-46b9-8d58-663b41805e9e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
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
theorem _root_.solution {σ : Type} {f g : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  ext m
  have hfg : MvPowerSeries.constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  set N := m.degree with hN
  have hT : ∀ i j : ℕ, N < i + j → MvPowerSeries.coeff m (f ^ i * g ^ j) = 0 :=
    fun i j h => coeff_mul_eq_zero_of_degree_lt_add_character_germs (coeff_pow_eq_zero_of_degree_lt_character_germs' hf i) (coeff_pow_eq_zero_of_degree_lt_character_germs' hg j) m (by omega)

  have hL : MvPowerSeries.coeff m (mvExp (f + g)) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C)) := by
    rw [coeff_mvExp_eq_sum_range_of_degree_le hfg m N le_rfl]
    have hk : ∀ k ∈ Finset.range (N + 1), MvPowerSeries.coeff m ((f + g) ^ k) / (k.factorial : C) =
        ∑ i ∈ Finset.range (k + 1), MvPowerSeries.coeff m (f ^ i * g ^ (k - i)) /
          ((i.factorial : C) * ((k - i).factorial : C)) := by
      intro k _
      rw [add_pow, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← nsmul_eq_mul', map_nsmul, nsmul_eq_mul, Nat.cast_choose C hik]
      have h1 : (k.factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have h2 : (i.factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have h3 : ((k - i).factorial : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
    rw [Finset.sum_congr rfl hk]
    rw [Finset.sum_range_diag_flip (N + 1) fun i j =>
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C))]
    refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_subset (fun j hj => by
      rw [Finset.mem_range] at hj ⊢
      omega) fun j hj hj' => ?_
    rw [Finset.mem_range] at hj hj'
    rw [hT i j (by omega), zero_div]

  have hR : MvPowerSeries.coeff m (mvExp f * mvExp g) = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.coeff m (f ^ i * g ^ j) / ((i.factorial : C) * (j.factorial : C)) := by
    rw [MvPowerSeries.coeff_mul]
    have hx : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m, MvPowerSeries.coeff x.1 (mvExp f) * MvPowerSeries.coeff x.2 (mvExp g) =
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          MvPowerSeries.coeff x.1 (f ^ i) * MvPowerSeries.coeff x.2 (g ^ j) /
            ((i.factorial : C) * (j.factorial : C)) := by
      intro x hx
      replace hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hd : x.1.degree + x.2.degree = N := by rw [hN, ← hx, map_add]
      rw [coeff_mvExp_eq_sum_range_of_degree_le hf x.1 N (by omega), coeff_mvExp_eq_sum_range_of_degree_le hg x.2 N (by omega), Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [div_mul_div_comm]
    rw [Finset.sum_congr rfl hx, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.coeff_mul, Finset.sum_div]
  rw [hL, hR]
end Formalism.L2.FormalSeriesBounds.VP
