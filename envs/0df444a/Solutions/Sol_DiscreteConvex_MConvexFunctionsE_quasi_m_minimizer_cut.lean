-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.quasi_m_minimizer_cut
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:43:26.386196+00:00
-- url     : https://prove2.me/submissions/7c795d60-3d4a-40da-94a4-a95388df26b9

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNe
import Theorems.Thm_DiscreteConvex_MConvexFunctions_Quasi_quasi_m_minimizer_cut

open Classical
open scoped Pointwise
open DiscreteConvex.MConvexFunctionsE

private lemma charVec_eq {V : Type*} [Fintype V] [DecidableEq V] :
    (DiscreteConvex.MConvexFunctionsE.CharVec : V → V → ℤ) =
      DiscreteConvex.MConvexFunctions.CharVec := by
  funext u w
  simp [DiscreteConvex.MConvexFunctionsE.CharVec, DiscreteConvex.MConvexFunctions.CharVec]

private lemma withTop_sub_lt_zero_iff {a b : WithTop ℝ} (hb : b ≠ ⊤) :
    a - b < 0 ↔ a < b := by
  cases b with
  | top => exact absurd rfl hb
  | coe rb =>
    cases a with
    | top =>
      change (⊤ : WithTop ℝ) < ((0 : ℝ) : WithTop ℝ) ↔ (⊤ : WithTop ℝ) < (rb : WithTop ℝ)
      simp
    | coe ra =>
      change ((ra - rb : ℝ) : WithTop ℝ) < ((0 : ℝ) : WithTop ℝ) ↔
        (ra : WithTop ℝ) < (rb : WithTop ℝ)
      rw [WithTop.coe_lt_coe, WithTop.coe_lt_coe, sub_lt_zero]

private lemma withTop_sub_eq_zero_iff {a b : WithTop ℝ} (hb : b ≠ ⊤) :
    a - b = 0 ↔ a = b := by
  cases b with
  | top => exact absurd rfl hb
  | coe rb =>
    cases a with
    | top =>
      change (⊤ : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) ↔ (⊤ : WithTop ℝ) = (rb : WithTop ℝ)
      simp
    | coe ra =>
      change ((ra - rb : ℝ) : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) ↔
        (ra : WithTop ℝ) = (rb : WithTop ℝ)
      rw [WithTop.coe_inj, WithTop.coe_inj, sub_eq_zero]

private lemma ssqmNe_imp_ssqmNeq {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ} (hf : SSQMNe f) :
    DiscreteConvex.MConvexFunctions.Quasi.SSQMNeq f := by
  intro x hx y hy hne u hu
  obtain ⟨v, hv, hcorr⟩ := hf x hx y hy hne u hu
  refine ⟨v, hv, ?_⟩
  have h_step_x : (fun w => x w + CharVec v w - CharVec u w) =
      (fun w => x w - DiscreteConvex.MConvexFunctions.CharVec u w +
        DiscreteConvex.MConvexFunctions.CharVec v w) := by
    funext w
    rw [← charVec_eq]
    omega
  have h_step_y : (fun w => y w + CharVec u w - CharVec v w) =
      (fun w => y w + DiscreteConvex.MConvexFunctions.CharVec u w -
        DiscreteConvex.MConvexFunctions.CharVec v w) := by
    funext w
    rw [← charVec_eq]
  unfold DeltaF at hcorr
  rw [h_step_x, h_step_y, withTop_sub_lt_zero_iff hx, withTop_sub_lt_zero_iff hy,
    withTop_sub_eq_zero_iff hx, withTop_sub_eq_zero_iff hy] at hcorr
  exact hcorr

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNe f)
    (hne : (ArgMinOn f).Nonempty) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec v w)) →
        ∃ xs ∈ ArgMinOn f, xs u ≤ x u - 1 + CharVec v u) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec u w + CharVec t w)) →
        ∃ xs ∈ ArgMinOn f, xs v ≥ x v - CharVec u v + 1) ∧
    (∀ x ∈ DomZ f \ ArgMinOn f, ∀ u v : V,
        (∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec t w)) →
        ∃ xs ∈ ArgMinOn f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1) := by
  have hmain := DiscreteConvex.MConvexFunctions.Quasi.quasi_m_minimizer_cut f
    (ssqmNe_imp_ssqmNeq hf) hne
  change (∀ x ∈ DiscreteConvex.MConvexFunctions.DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec v w)) →
        ∃ xs ∈ DiscreteConvex.MConvexFunctions.ArgMin f, xs u ≤ x u - 1 + CharVec v u) ∧
    (∀ x ∈ DiscreteConvex.MConvexFunctions.DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec u w + CharVec t w)) →
        ∃ xs ∈ DiscreteConvex.MConvexFunctions.ArgMin f, xs v ≥ x v - CharVec u v + 1) ∧
    (∀ x ∈ DiscreteConvex.MConvexFunctions.DomZ f \ DiscreteConvex.MConvexFunctions.ArgMin f,
      ∀ u v : V,
        (∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec t w)) →
        ∃ xs ∈ DiscreteConvex.MConvexFunctions.ArgMin f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1)
  rw [charVec_eq]
  exact hmain
