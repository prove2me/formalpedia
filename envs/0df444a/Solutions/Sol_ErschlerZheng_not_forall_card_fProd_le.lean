-- Prove2me | solution 1 for ErschlerZheng.not_forall_card_fProd_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.145441+00:00
-- url     : https://prove2.me/submissions/5711d06a-cc54-42fe-a9eb-d56fac9987fb

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Construction
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

/-! ### 2. Lemma 7.17 (ii) at `n = 0` -/

/-- `ω = (201)^∞`. -/
def om201 : ℕ → Fin 3 := fun i => if i % 3 = 0 then 2 else if i % 3 = 1 then 0 else 1

theorem satisfiesFr_om201 : SatisfiesFr 3 om201 := by
  intro k
  have h0 : (k * 3 + 0) % 3 = 0 := by omega
  have h1 : (k * 3 + 0 + 1) % 3 = 1 := by omega
  have h2 : (k * 3 + 0 + 2) % 3 = 2 := by omega
  refine ⟨0, by norm_num, ?_, ?_, Or.inl ?_⟩
  · simp only [om201, h0, if_true]
  · simp only [om201, h2]; rfl
  · simp only [om201, h1]; rfl

/-- `k_0 = 0` and `k_n = 3` for `n ⩾ 1`. -/
def kZero : ℕ → ℕ := fun n => if n = 0 then 0 else 3

theorem isAdmissibleSeq_kZero : IsAdmissibleSeq 3 kZero := by
  refine ⟨fun m n hmn => ?_, fun n hn _ => ?_⟩
  · simp only [kZero]; split_ifs <;> omega
  · simp only [kZero, if_neg (show n ≠ 0 by omega)]
    exact ⟨by norm_num, dvd_refl 3⟩

theorem oneRay_mem_orbitOne (ω : ℕ → Fin 3) : oneRay ∈ orbitOne ω :=
  ⟨1, (grigorchuk ω).one_mem, (one_smul _ oneRay).symm⟩

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
theorem solution :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      ∀ n : ℕ, D ∣ n →
      ∀ ε : Fin n → Bool, ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ n + 2 * k n + 2 * D + 5 → ∀ x ∈ orbitOne ω,
        (Nat.card {γ : fProd D ω k n // k n * 2 ^ ℓ ≤ schreierDist ω x (x <• theta D ω k n (ε, γ))} :
            ℝ) / Nat.card (fProd D ω k n) ≤
          8 * k n * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by
  intro H
  have h := H 3 om201 satisfiesFr_om201 kZero isAdmissibleSeq_kZero 0 (dvd_zero 3) Fin.elim0 0
    le_rfl (by omega) oneRay (oneRay_mem_orbitOne om201)
  have hk0 : kZero 0 = 0 := rfl
  have hcard : Nat.card (fProd 3 om201 kZero 0) = 1 := Nat.card_unique
  have hsub : Nat.card {γ : fProd 3 om201 kZero 0 // kZero 0 * 2 ^ 0 ≤
      schreierDist om201 oneRay (oneRay <• theta 3 om201 kZero 0 (Fin.elim0, γ))} = 1 := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun γ => by rw [hk0]; exact Nat.zero_le _)
  rw [hsub, hcard, hk0] at h
  norm_num at h
end
