-- Prove2me | solution 1 for DiazModulus.rank_one_config_separation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:48:39.92488+00:00
-- url     : https://prove2.me/submissions/487e00be-8122-42a9-83b5-d5de697a7b89

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rank_one_config_separation_two

open Complex ComplexConjugate

/-! # Separation for `p × q` configurations and `m` algebraically independent numbers
Induction on `m`; for `m = 0` the span of the empty family is `⊥`. For `m + 1`, let `w'` be the
first `m` numbers and `F' = F(w')` (an `IntermediateField` of `ℂ` over `F`, seen as a subfield).
The last number is transcendental over `Algebra.adjoin F (range w')`
(`AlgebraicIndependent.transcendental_adjoin`), hence over `F'`
(`IntermediateField.transcendental_adjoin_iff`). Put `V₀' = V₀ ⊔ span K (range w') ⊆ F'`. Every
entry `(i, j)` sits in a `2 × 2` block with rows `i ≠ i'` and columns `j ≠ j'` (here `2 ≤ p, q`);
restricting `x, y` along the injective maps `![i, i']`, `![j, j']` keeps `K`-independence, and the
block is a `2 × 2` configuration in `V₀' ⊔ K w_last`. The `2 × 2` separation node puts `x i * y j` in
`V₀'`, and the induction hypothesis (the first `m` numbers stay algebraically independent over `F`)
puts it in `V₀`.
-/

namespace R6_sep
open DiazModulus

theorem inj_pair {n : ℕ} (i i' : Fin n) (h : i' ≠ i) : Function.Injective ![i, i'] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢
  · exact h hab.symm
  · exact h hab

end R6_sep

open DiazModulus R6_sep in
theorem solution (K F : Subfield ℂ) (hKF : K ≤ F)
    (V₀ : Submodule K ℂ) (hV₀ : ∀ v ∈ V₀, v ∈ F) (m : ℕ) (w : Fin m → ℂ)
    (hw : AlgebraicIndependent F w) (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (x : Fin p → ℂ) (y : Fin q → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀ ⊔ Submodule.span K (Set.range w)) :
    ∀ i j, x i * y j ∈ V₀ := by
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.mpr hp
  have : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr hq
  induction m with
  | zero =>
    intro i j
    simpa [Set.range_eq_empty] using hxy i j
  | succ m ih =>
    set w' : Fin m → ℂ := fun k => w k.castSucc with hw'def
    have hw' : AlgebraicIndependent F w' := hw.comp _ (Fin.castSucc_injective m)
    let E := IntermediateField.adjoin F (Set.range w')
    let F' : Subfield ℂ := E.toSubfield
    have htr : Transcendental F' (w (Fin.last m)) := by
      have := hw.transcendental_adjoin (s := Set.range Fin.castSucc) (i := Fin.last m) (by simp)
      rw [← Set.range_comp] at this
      exact IntermediateField.transcendental_adjoin_iff.mpr this
    have hFF' : ∀ a ∈ F, a ∈ F' := fun a ha => IntermediateField.algebraMap_mem E ⟨a, ha⟩
    have hKF' : K ≤ F' := fun a ha => hFF' a (hKF ha)
    have hV₀' : ∀ v ∈ V₀ ⊔ Submodule.span K (Set.range w'), v ∈ F' := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      clear hv
      refine F'.add_mem (hFF' a (hV₀ a ha)) ?_
      induction hb using Submodule.span_induction with
      | mem z hz => exact IntermediateField.subset_adjoin _ _ hz
      | zero => exact F'.zero_mem
      | add a b _ _ ha hb => exact F'.add_mem ha hb
      | smul a b _ hb => rw [Subfield.smul_def]; exact F'.mul_mem (hKF' a.2) hb
    have hle : V₀ ⊔ Submodule.span K (Set.range w) ≤
        (V₀ ⊔ Submodule.span K (Set.range w')) ⊔ Submodule.span K {w (Fin.last m)} := by
      rw [sup_assoc]
      refine sup_le_sup_left (Submodule.span_le.mpr ?_) _
      rintro _ ⟨k, rfl⟩
      induction k using Fin.lastCases with
      | last => exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      | cast k => exact Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩)
    refine ih w' hw' (fun i j => ?_)
    obtain ⟨i', hi'⟩ := exists_ne i
    obtain ⟨j', hj'⟩ := exists_ne j
    have := DiazModulus.rank_one_config_separation_two K F' hKF' _ hV₀' _ htr
      (x ∘ ![i, i']) (y ∘ ![j, j']) (hx.comp _ (inj_pair i i' hi'))
      (hy.comp _ (inj_pair j j' hj')) (fun a b => hle (hxy _ _)) 0 0
    simpa using this
