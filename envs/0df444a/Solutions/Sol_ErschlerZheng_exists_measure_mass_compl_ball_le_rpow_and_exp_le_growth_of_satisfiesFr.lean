-- Prove2me | solution 1 for ErschlerZheng.exists_measure_mass_compl_ball_le_rpow_and_exp_le_growth_of_satisfiesFr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:37:50.234879+00:00
-- url     : https://prove2.me/submissions/ef4fff0a-2a5c-47d9-8e07-9fc4be30e6e4

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr
section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Kernel library for the Markov heat-kernel package

Substochastic kernels on a type `X` (no countability needed): non-negative entries, summable rows
with sums at most one. Their powers `stepProb`, Chapman–Kolmogorov, symmetry of powers, column
sums, and Poisson series facts used by the heat kernel.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

variable [DecidableEq X]

/-! ## The heat kernel -/

end MarkovHK
end

section
/-!
# Near and far parts of a kernel; `uniformize` of a substochastic kernel (shared by H6 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

variable [DecidableEq X]

end MarkovHK
end

section
/-!
# Orbit kernels of `μ_β` and `υ_n` as Markov kernels (helpers for Proposition 7.19, prover 6)

* `G_ω` and the orbit `1^∞·G_ω` are countable.
* For `ν ⩾ 0` summable on a subgroup `K`, the rows of `P_ν` sum to `Σ ν`; `P_ν` is a transition
  kernel when `ν` is a probability, and symmetric when `ν` is.
* `υ_n` restricted to `G_ω` is a sub-probability, so `P_{(υ_n + υ̌_n)/2}` is substochastic.
* `μ_β ⩾ C_β 2^{-nβ} (υ_n + υ̌_n)/2` pointwise, for `n ⩾ 1`, `D ∣ n`.
* `μ_β` is symmetric; `k_n = A⌊log₂ n⌋` is admissible and eventually `⩽ n` (copied from prover 5's
  `P5Goal`, which is still being edited).
-/

open scoped RightActions
open DurrettProbability MarkovChain

namespace ErschlerZheng

namespace P6Dev

open GrigBasic Garrido Filter

set_option linter.unusedSectionVars false

/-! ### Countability -/

lemma gens_finite (ω : ℕ → Fin 3) : (gens ω).Finite := by
  unfold gens
  exact (((Set.finite_singleton _).insert _).insert _).insert _

instance countable_grigorchuk (ω : ℕ → Fin 3) : Countable (grigorchuk ω) := by
  have hT : (gens ω ∪ (gens ω)⁻¹).Countable :=
    ((gens_finite ω).union (gens_finite ω).inv).countable
  have hc : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut).Countable := by
    have h1 : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut) =
        (Submonoid.closure (gens ω ∪ (gens ω)⁻¹) : Set BinaryTreeAut) := by
      unfold grigorchuk
      rw [← Subgroup.closure_toSubmonoid]
      rfl
    rw [h1, Submonoid.closure_eq_image_prod]
    have : Countable (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) := hT.to_subtype
    have h2 : {l : List BinaryTreeAut | ∀ x ∈ l, x ∈ gens ω ∪ (gens ω)⁻¹} ⊆
        Set.range (fun l : List (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) =>
          l.map Subtype.val) := by
      intro l hl
      refine ⟨l.attach.map fun x => ⟨x.1, hl x.1 x.2⟩, ?_⟩
      simp [List.map_attach_eq_pmap]
    exact ((Set.countable_range _).mono h2).image _
  exact hc.to_subtype

instance countable_orbitOne (ω : ℕ → Fin 3) : Countable (orbitOne ω) := by
  have : (orbitOne ω).Countable := by
    have h : orbitOne ω ⊆ Set.range (fun g : grigorchuk ω => oneRay <• (g : BinaryTreeAut)) := by
      rintro y ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    exact (Set.countable_range _).mono h
  exact this.to_subtype

/-! ### Orbit kernels -/

section Orbit

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X] (K : Subgroup H)

end Orbit

/-! ### The measures `υ_n` on `G_ω` -/

/-! ### `μ_β` dominates its `n`-th component -/

/-! ### Symmetry of `μ_β` and the parameters (after prover 5's `P5Goal`) -/

end P6Dev

end ErschlerZheng
end

section
/-!
# Printed versions and boundary cases (group `printed`)

1. Theorem 8.3 as printed (p. 58), with the bounds `C n^{-1+ε}` and `exp(c n^{1-ε})`, from the
   mission's version with `2^n` in place of `n`, applied with the same `ε` if `ε ⩽ 1` and with
   `ε = 1/2` if `ε > 1`.
2. Lemma 7.17 (ii) without `n ⩾ 1` fails: `D = 3`, `ω = (201)^∞`, `k_0 = 0`, `n = ℓ = 0`.
3. The odd case of (2.3) as printed, `(wa, aw)ε`, fails: `ω = (012)^∞`, `n = 0`, `w = ad`.
4. Proposition 7.18 at distance `⩾ 3` and for `r ⩾ 3`, from the stated version at `⩾ 4`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewPrinted

open GrigBasic

/-! ### 1. Theorem 8.3 as printed -/

/-- `n^t ⩽ 2^{t n}` for `t ⩾ 0`. -/
lemma natCast_rpow_le_two_rpow (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (n : ℝ) ^ t ≤ (2 : ℝ) ^ (t * n) := by
  have h1 : (n : ℝ) ≤ (2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast Nat.lt_two_pow_self.le
  calc (n : ℝ) ^ t ≤ ((2 : ℝ) ^ (n : ℝ)) ^ t := Real.rpow_le_rpow (Nat.cast_nonneg n) h1 ht
    _ = (2 : ℝ) ^ (t * n) := by rw [← Real.rpow_mul (by norm_num), mul_comm]

/-! ### 2. Lemma 7.17 (ii) at `n = 0` -/

/-! ### 3. The odd case of (2.3) at `ω = (012)^∞`, `w = ad` -/

/-! ### 4. Proposition 7.18 at distance `3` and for `3 ⩽ r < 4` -/

end NewPrinted

open NewPrinted GrigBasic

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewPrinted GrigBasic
theorem solution (D : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ ω : ℕ → Fin 3, SatisfiesFr D ω →
      ∃ μ : grigorchuk ω → ℝ, IsNondegenerate μ ∧ IsSymmetric μ ∧ IsProbability μ ∧
        HasFiniteEntropy μ ∧ HasNontrivialPoissonBoundary μ ∧
        (∀ n : ℕ, 1 ≤ n →
          mass μ (ball (genSet ω) (lengthL ω n))ᶜ ≤ C * (n : ℝ) ^ (-1 + ε)) ∧
        ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
          Real.exp (c * (n : ℝ) ^ (1 - ε)) ≤ growth (genSet ω) (lengthL ω n) := by
  -- the mission's version at `ε' = ε` if `ε ⩽ 1`, and at `ε' = 1/2` if `ε > 1`
  set ε' : ℝ := if ε ≤ 1 then ε else 1 / 2 with hε'
  have hε'0 : 0 < ε' := by rw [hε']; split_ifs <;> linarith
  have hε'ε : ε' ≤ ε := by rw [hε']; split_ifs <;> linarith
  have ht : 0 ≤ 1 - ε' := by rw [hε']; split_ifs <;> linarith
  obtain ⟨C, hC, hall⟩ :=
    exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr D ε' hε'0
  refine ⟨C, hC, fun ω hω => ?_⟩
  obtain ⟨μ, h1, h2, h3, h4, h5, hmass, c, hc, hgrowth⟩ := hall ω hω
  refine ⟨μ, h1, h2, h3, h4, h5, fun n hn => ?_, c, hc, fun n hn => ?_⟩
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hkey : (2 : ℝ) ^ (-((1 - ε') * n)) ≤ (n : ℝ) ^ (-1 + ε) := by
      have hp : 0 < (n : ℝ) ^ (1 - ε') := Real.rpow_pos_of_pos hnpos _
      calc (2 : ℝ) ^ (-((1 - ε') * n)) = ((2 : ℝ) ^ ((1 - ε') * n))⁻¹ :=
            Real.rpow_neg (by norm_num) _
        _ ≤ ((n : ℝ) ^ (1 - ε'))⁻¹ := by
            gcongr
            exact natCast_rpow_le_two_rpow n ht
        _ = (n : ℝ) ^ (-(1 - ε')) := (Real.rpow_neg hnpos.le _).symm
        _ ≤ (n : ℝ) ^ (-1 + ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    calc mass μ (ball (genSet ω) (lengthL ω n))ᶜ ≤ C * (2 : ℝ) ^ (-((1 - ε') * n)) := hmass n hn
      _ ≤ C * (n : ℝ) ^ (-1 + ε) := mul_le_mul_of_nonneg_left hkey hC.le
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine le_trans ?_ (hgrowth n hn)
    rw [Real.exp_le_exp]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    calc (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε') :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ ≤ (2 : ℝ) ^ ((1 - ε') * n) := natCast_rpow_le_two_rpow n ht
end
