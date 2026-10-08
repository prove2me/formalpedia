-- Prove2me | solution 1 for ErschlerZheng.not_forall_sec_evalWord_zetaWord_eq_mul_grigA_and_grigA_mul_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.595627+00:00
-- url     : https://prove2.me/submissions/a44c2ed5-076d-4576-846b-9b665dc27a37

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

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem gen_mul_self (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ * gen ω γ = 1 :=
  Subtype.ext (Equiv.ext fun w => genFun_involutive ω γ w)

theorem gen_inv (ω : ℕ → Fin 3) (γ : BCD) : (gen ω γ)⁻¹ = gen ω γ :=
  inv_eq_of_mul_eq_one_right (gen_mul_self ω γ)

theorem vertex_smul_gen (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    v <• gen ω γ = genFun ω γ v := by
  rw [vertex_smul_def, gen_inv]
  rfl

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

/-! ### 3. The odd case of (2.3) at `ω = (012)^∞`, `w = ad` -/

/-- The value `g` of `ζ_0(ad) = abadac` in `G_{(012)^∞}` sends `0 0 0` to `1 0 1`. -/
theorem vertex_smul_zeta_ad_three :
    [false, false, false] <• evalWord firstString 0
      ((zetaWord (firstString 0) [APair.ad]).flatMap APair.toWord) = [true, false, true] := by
  rw [show firstString 0 = 0 from rfl]
  simp only [zetaWord, zetaPair, List.flatMap_cons, List.flatMap_nil, APair.toWord, evalWord,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.cons_append, List.nil_append,
    List.append_nil, vertex_smul_mul, vertex_smul_grigA, vertex_smul_gen]
  decide

/-- The same `g` sends `0` to `1`. -/
theorem vertex_smul_zeta_ad_one :
    [false] <• evalWord firstString 0
      ((zetaWord (firstString 0) [APair.ad]).flatMap APair.toWord) = [true] := by
  rw [show firstString 0 = 0 from rfl]
  simp only [zetaWord, zetaPair, List.flatMap_cons, List.flatMap_nil, APair.toWord, evalWord,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.cons_append, List.nil_append,
    List.append_nil, vertex_smul_mul, vertex_smul_grigA, vertex_smul_gen]
  decide

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
    ¬ ∀ (ω : ℕ → Fin 3) (n : ℕ) (w : List APair),
      Odd (((zetaWord (ω n) w).flatMap APair.toWord).count .a) →
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [false] =
            evalWord ω (n + 1) (w.flatMap APair.toWord) * Garrido.grigA ∧
          sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [true] =
            Garrido.grigA * evalWord ω (n + 1) (w.flatMap APair.toWord) := by
  intro H
  have hodd : Odd (((zetaWord (firstString 0) [APair.ad]).flatMap APair.toWord).count .a) := by
    decide
  obtain ⟨hp, -⟩ := H firstString 0 [APair.ad] hodd
  -- `(0 0 0)·g = (0·g)((0 0)·g_0)`, and the printed `g_0 = (a d_{𝔰ω}) a` gives `1 0 0`
  have h1 := append_vertex_smul (evalWord firstString 0
    ((zetaWord (firstString 0) [APair.ad]).flatMap APair.toWord)) [false] [false, false]
  rw [hp, show [false] ++ [false, false] = [false, false, false] from rfl,
    vertex_smul_zeta_ad_three, vertex_smul_zeta_ad_one] at h1
  simp only [evalWord, APair.toWord, List.flatMap_cons, List.flatMap_nil, vertex_smul_mul,
    vertex_smul_grigA] at h1
  revert h1
  decide
end
