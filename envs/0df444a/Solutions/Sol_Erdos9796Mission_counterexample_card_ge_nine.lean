-- Prove2me | solution 1 for Erdos9796Mission.counterexample_card_ge_nine
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:29.185847+00:00
-- url     : https://prove2.me/submissions/85e33fb4-bf8e-43c5-931a-f9e7609e7805

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Counting:3716:4592. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Theorems.Thm_Problem97_CGN8_circumscribed_iCount_upper_bound
import Theorems.Thm_Problem97_ConvexIndep_not_collinear_of_card_ge_three
import Theorems.Thm_Problem97_MEC_no_diameter_under_k4
import Theorems.Thm_Problem97_card_ge_five_of_K4
import Theorems.Thm_Problem97_counting_arithmetic
import Theorems.Thm_Problem97_iCountAt_ge_six_of_K4

section Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount

open Problem97

/- Fragment from Erdos9796Proof.P97.IsoscelesCount; source SHA-256 207564b11a38e9270192c8e5de3202b113b7f89c7ece5af3bc12954928d3013c -/


/-!
# Isosceles count for Erdős Problem 97 (Dumitrescu lower bound, Milestone 3)

Defines the per-vertex and total isosceles count of a finite point set,
in the Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013 convention
(equilaterals counted three times), and proves the easy lower bound:

  Per-vertex `K4` ⇒ each vertex contributes `≥ C(4,2) = 6` isosceles pairs.
  Summing: `6 · |A| ≤ I(A)`.

The matching upper bound `I(A) ≤ (11·|A|²−18·|A|)/12` for convex point
sets is Dumitrescu 2006 eq. (5), still open
(`p97-isosceles-count-upper-bound`).

References: doc slug `p97-isosceles-obstruction`.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical



















/-- **Total isosceles count lower bound under K4.**  Summing the per-vertex
bound `iCountAt_ge_six_of_K4` over all `p ∈ A`. -/
theorem Problem97.six_mul_card_le_iCount_of_K4 {A : Finset ℝ²}
    (hK4 : HasNEquidistantProperty 4 A) : 6 * A.card ≤ iCount A := by
  classical
  unfold iCount
  have hpoint : ∀ p ∈ A, 6 ≤ iCountAt A p :=
    fun p hp => iCountAt_ge_six_of_K4 A p (hK4 p hp)
  calc 6 * A.card
      = ∑ _p ∈ A, 6 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ A, iCountAt A p := sum_le_sum hpoint

end Erdos9796CountingFragment_Erdos9796Proof_P97_IsoscelesCount

section Erdos9796CountingFragment_Erdos9796Proof_P97_Counting

open Problem97

/- Fragment from Erdos9796Proof.P97.Counting; source SHA-256 1bc8e15663c147d582d82d71a22bf654f8becdb1003f0aef828d47271d204523 -/


/-!
# Counting obstruction: `9 ≤ |A|` (Milestone 3)

This module packages the proven lower bound
`Problem97.six_mul_card_le_iCount_of_K4` and the proven arithmetic core
`Problem97.counting_arithmetic` into the intermediate theorem
`Problem97.counterexample_card_ge_nine_of_iCount_upper_bound`.

The top-level theorem `Problem97.counterexample_card_ge_nine` now
instantiates that reducer with the circumscribed-branch CGN closure
`Problem97.CGN8_circumscribed_iCount_upper_bound`.
-/

open scoped EuclideanGeometry
open Finset





/-- CGN1 + CGN2 packaged: a K4 counterexample with at least five points
is non-collinear. -/
theorem Problem97.not_collinear_of_K4 {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A) :
    ¬ Collinear ℝ (A : Set ℝ²) := by
  have h5 : 5 ≤ A.card := card_ge_five_of_K4 hne hK4
  have h3 : 3 ≤ A.card := le_trans (by decide : 3 ≤ 5) h5
  exact ConvexIndep.not_collinear_of_card_ge_three hconv h3

/-- CGN3 packaged at the counting level: a K4 counterexample has at
least three points on the MEC boundary, so the diameter branch is
excluded. -/
theorem Problem97.boundary_card_ge_three_of_K4 {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A) :
    3 ≤ (A.filter (fun p =>
      dist p (Problem97.MEC.mec A hne).center = (Problem97.MEC.mec A hne).radius)).card := by
  have hnoncol : ¬ Collinear ℝ (A : Set ℝ²) :=
    not_collinear_of_K4 hne hconv hK4
  exact Problem97.MEC.no_diameter_under_k4 hne hnoncol hconv hK4

/-- **M3 counting obstruction (conditional on an upper-bound theorem).**

This theorem isolates the arithmetic assembly: once `iCount A` is
bounded above by the quadratic expression, the `6n` lower bound and the
arithmetic lemma `counting_arithmetic` force `9 ≤ A.card`.

The top-level theorem instantiates this reducer with the CGN8
circumscribed upper bound. -/
theorem Problem97.counterexample_card_ge_nine_of_iCount_upper_bound
    {A : Finset ℝ²} (hne : A.Nonempty) (_hconv : ConvexIndep A)
    (hK4 : HasNEquidistantProperty 4 A)
    (hup : (iCount A : ℝ) ≤ ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12) :
    9 ≤ A.card := by
  have h5 : 5 ≤ A.card := card_ge_five_of_K4 hne hK4
  have h3 : 3 ≤ A.card := by omega
  -- Lower: 6 * A.card ≤ iCount A (ℕ).
  have hlo : 6 * A.card ≤ iCount A := six_mul_card_le_iCount_of_K4 hK4
  have hlor : (6 : ℝ) * A.card ≤ (iCount A : ℝ) := by exact_mod_cast hlo
  -- Upper: `iCount A` is bounded above by the quadratic expression.
  have hchain : (6 : ℝ) * A.card ≤ ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 :=
    hlor.trans hup
  exact counting_arithmetic h3 hchain

/- Provenance: this route follows Dumitrescu's 2006 isosceles-count
method and uses cap-witness refinements attributed in the source to
Nivasch–Pach–Pinchasi–Zerbib (2013). The Lean proof is this project's own
formalization; these citations record provenance, not an imported or
machine-checked paper proof. -/
theorem solution
    (A : Finset Erdos9796Mission.Plane) (hne : A.Nonempty)
    (hconv : Erdos9796Mission.ConvexIndep (A : Set Erdos9796Mission.Plane))
    (hK4 : Erdos9796Mission.HasNEquidistantProperty 4 A) : 9 ≤ A.card := by
  have hnoncol : ¬ Collinear ℝ (A : Set ℝ²) :=
    not_collinear_of_K4 hne hconv hK4
  have hbd :
      3 ≤ (A.filter (fun p =>
        dist p (Problem97.MEC.mec A hne).center =
          (Problem97.MEC.mec A hne).radius)).card :=
    boundary_card_ge_three_of_K4 hne hconv hK4
  exact counterexample_card_ge_nine_of_iCount_upper_bound hne hconv hK4
    (CGN8_circumscribed_iCount_upper_bound hne hnoncol hconv hbd)

end Erdos9796CountingFragment_Erdos9796Proof_P97_Counting
