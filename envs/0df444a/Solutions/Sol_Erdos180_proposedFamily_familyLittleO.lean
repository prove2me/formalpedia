-- Prove2me | solution 1 for Erdos180.proposedFamily_familyLittleO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:21:23.216063+00:00
-- url     : https://prove2.me/submissions/0a46cc50-d92f-4fad-b988-36de424dc3cd

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Finite
import Theorems.Thm_Erdos180_edgeFinset_card_eq_natCard
import Theorems.Thm_Erdos180_extremalScale_nonneg
import Theorems.Thm_Erdos180_proposedFamilyFree_sixteenth_power_host_bound

namespace Erdos180

noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology

theorem familyExtremal_real_le_of_forall_free
    (family : Finset FiniteGraph) (n : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hfree : ∀ host : SimpleGraph (Fin n),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ≤ bound) :
    (familyExtremal family n : ℝ) ≤ bound := by
  classical
  have hnat : familyExtremal family n ≤ ⌊bound⌋₊ := by
    unfold familyExtremal
    apply Finset.sup_le
    intro host hhost
    apply Nat.le_floor
    simpa only [edgeFinset_card_eq_natCard] using
      hfree host (Finset.mem_filter.mp hhost).2
  have hcast : (familyExtremal family n : ℝ) ≤ (⌊bound⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le hbound)

lemma familyLittleO_of_eventual_host_bounds
    (family : Finset FiniteGraph)
    (hhost : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ host : SimpleGraph (Fin n),
          FamilyFree family host →
            (host.edgeFinset.card : ℝ) ≤ ε * extremalScale n) :
    FamilyLittleO family := by
  intro ε hε
  filter_upwards [hhost ε hε] with n hn
  exact familyExtremal_real_le_of_forall_free family n
    (mul_nonneg hε.le (extremalScale_nonneg n)) hn

lemma eventually_constant_le_positive_nat_rpow
    (constant coefficient exponent : ℝ)
    (hcoefficient : 0 < coefficient)
    (hexponent : 0 < exponent) :
    ∀ᶠ n : ℕ in Filter.atTop,
      constant ≤ coefficient * (n : ℝ) ^ exponent := by
  have hpower :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ exponent)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexponent).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpower.eventually
    (Filter.eventually_ge_atTop (constant / coefficient))]
    with n hn
  calc
    constant = coefficient * (constant / coefficient) := by
      field_simp
    _ ≤ coefficient * (n : ℝ) ^ exponent :=
      mul_le_mul_of_nonneg_left hn hcoefficient.le

lemma extremalScale_sixteenth_power
    {n : ℕ} (hn : 0 < n) :
    (extremalScale n) ^ 16 =
      (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold extremalScale
  calc
    ((n : ℝ) ^ ((4 : ℝ) / 3)) ^ 16 =
        (n : ℝ) ^ (((4 : ℝ) / 3) * (16 : ℝ)) := by
      exact (Real.rpow_mul_natCast hnreal.le
        ((4 : ℝ) / 3) 16).symm
    _ = (n : ℝ) ^ ((21 : ℝ) + (1 : ℝ) / 3) := by
      congr 1
      norm_num
    _ = (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      simp [Real.rpow_add hnreal]

lemma familyLittleO_of_sixteenth_power_host_bound
    (family : Finset FiniteGraph) (constant : ℝ)
    (hbound : ∀ (n : ℕ) (host : SimpleGraph (Fin n)),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21) :
    FamilyLittleO family := by
  apply familyLittleO_of_eventual_host_bounds
  intro ε hε
  have hεpow : 0 < ε ^ (16 : ℕ) := pow_pos hε _
  have hconstant := eventually_constant_le_positive_nat_rpow
    constant (ε ^ (16 : ℕ)) ((1 : ℝ) / 3)
    hεpow (by norm_num)
  filter_upwards [hconstant, Filter.eventually_gt_atTop 0]
    with n hn hnpositive
  intro host hfree
  have hhost := hbound n host hfree
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have htarget :
      (host.edgeFinset.card : ℝ) ^ 16 ≤
        (ε * extremalScale n) ^ 16 := by
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21 := hhost
      _ ≤ (ε ^ (16 : ℕ) * (n : ℝ) ^ ((1 : ℝ) / 3)) *
          (n : ℝ) ^ 21 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (ε * extremalScale n) ^ 16 := by
        rw [mul_pow, extremalScale_sixteenth_power hnpositive]
        ring
  have hresult :
      (Nat.card host.edgeSet : ℝ) ≤ ε * extremalScale n := by
    apply le_of_pow_le_pow_left₀
      (by norm_num : (16 : ℕ) ≠ 0)
      (mul_nonneg hε.le (extremalScale_nonneg n))
    simpa only [edgeFinset_card_eq_natCard] using htarget
  simpa only [edgeFinset_card_eq_natCard] using hresult

end

end Erdos180

open Erdos180
open Filter Finset SimpleGraph
open scoped Classical Topology

theorem solution :
    FamilyLittleO proposedFamily :=
  familyLittleO_of_sixteenth_power_host_bound
    proposedFamily compactnessHostPowerConstant
    proposedFamilyFree_sixteenth_power_host_bound
