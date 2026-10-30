-- Prove2me | solution 1 for DiazModulus.sse_setup
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:12:20.220999+00:00
-- url     : https://prove2.me/submissions/50262564-b312-4aa3-91e3-d8bf07eb9cca

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The SSE setup: `Υ⁻¹(ℂx)` has dimension `2m+1`, and `ker Υ` is spanned by algebraic vectors
Write `Υ(u, v)_i = u_i + Σ_k ω_k v_{(k,i)}` on `ℂ² × ℂ^{m×2}`. The map `Υ` is surjective, since
`Υ(u, 0) = u`. Composing it with the quotient map `ℂ² → ℂ²/ℂx` gives a surjection whose kernel is
`Υ⁻¹(ℂx)`; the quotient has dimension `2 − 1 = 1` because `x ≠ 0`, so rank–nullity on a domain of
dimension `2 + 2m` gives `dim Υ⁻¹(ℂx) = 2m + 1`.
For the second claim, each vector `b_p = (−ω_{p.1} e_{p.2}, e_p)` lies in `ker Υ` by a direct
computation, and every `z ∈ ker Υ` equals `Σ_p z.2(p) • b_p`: the second coordinates agree
trivially, and the first coordinates agree because `z.1_i = −Σ_k ω_k z.2(k,i)` on the kernel. -/

namespace C14_S5
open DiazModulus

/-- The map `Υ`, verbatim. -/
noncomputable def Ups (m : ℕ) (ω : Fin m → ℂ) :
    ((Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i : Fin 2 =>
    (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
    + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)

theorem Ups_apply {m : ℕ} (ω : Fin m → ℂ) (z : (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) (i : Fin 2) :
    Ups m ω z i = z.1 i + ∑ k, ω k * z.2 (k, i) := by
  simp [Ups, LinearMap.sum_apply]

theorem Ups_range {m : ℕ} (ω : Fin m → ℂ) : LinearMap.range (Ups m ω) = ⊤ :=
  LinearMap.range_eq_top.mpr fun u => ⟨(u, 0), by ext i; simp [Ups_apply]⟩

theorem finrank_dom (m : ℕ) :
    Module.finrank ℂ ((Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ)) = 2 + 2 * m := by
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_prod]; ring

theorem finrank_comap {m : ℕ} (ω : Fin m → ℂ) (x : Fin 2 → ℂ) (hx0 : x ≠ 0) :
    Module.finrank ℂ ↥((ℂ ∙ x).comap (Ups m ω)) = 2 * m + 1 := by
  set f := (ℂ ∙ x).mkQ ∘ₗ Ups m ω
  have hker : LinearMap.ker f = (ℂ ∙ x).comap (Ups m ω) := by
    simp [f, LinearMap.ker_comp]
  have hrange : LinearMap.range f = ⊤ := by
    simp only [f, LinearMap.range_comp, Ups_range, Submodule.map_top, Submodule.range_mkQ]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_quotient_add_finrank (ℂ ∙ x)
  rw [finrank_span_singleton hx0] at h2
  have h3 : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by simp
  rw [hrange, finrank_top, hker, finrank_dom] at h1
  omega

/-- The spanning vectors. -/
def bv {m : ℕ} (ω : Fin m → ℂ) (p : Fin m × Fin 2) : (Fin 2 → ℂ) × (Fin m × Fin 2 → ℂ) :=
  ((fun i => if i = p.2 then -ω p.1 else 0), (fun q => if q = p then (1 : ℂ) else 0))

theorem bv_mem_ker {m : ℕ} (ω : Fin m → ℂ) (p : Fin m × Fin 2) :
    bv ω p ∈ LinearMap.ker (Ups m ω) := by
  rw [LinearMap.mem_ker]
  ext i
  rw [Ups_apply]
  obtain ⟨a, b⟩ := p
  by_cases hi : i = b
  · subst hi
    simp [bv, Prod.ext_iff]
  · have : ∀ k : Fin m, ((k, i) : Fin m × Fin 2) ≠ (a, b) := fun k h => hi (Prod.ext_iff.mp h).2
    simp [bv, hi, this]

theorem span_bv {m : ℕ} (ω : Fin m → ℂ) :
    Submodule.span ℂ (Set.range (bv ω)) = LinearMap.ker (Ups m ω) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact bv_mem_ker ω p
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    have hz1 : ∀ i, z.1 i = -∑ k, ω k * z.2 (k, i) := by
      intro i
      have := congrFun hz i
      rw [Ups_apply] at this
      simp only [Pi.zero_apply] at this
      linear_combination this
    have hsum : z = ∑ p, z.2 p • bv ω p := by
      refine Prod.ext ?_ ?_
      · ext i
        rw [hz1 i, Prod.fst_sum, Finset.sum_apply, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Fin.sum_univ_two]
        fin_cases i <;> simp [bv] <;> ring
      · ext q
        rw [Prod.snd_sum, Finset.sum_apply]
        simp [bv]
    rw [hsum]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

end C14_S5

open DiazModulus C14_S5 in
theorem solution (m : ℕ) (ω : Fin m → ℂ) (x : Fin 2 → ℂ) (hx0 : x ≠ 0) :
    Module.finrank ℂ ↥((ℂ ∙ x).comap (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ))) = 2 * m + 1 ∧
    Submodule.span ℂ (Set.range (fun p : Fin m × Fin 2 => ((fun i => if i = p.2 then -ω p.1 else 0),
        (fun q => if q = p then (1 : ℂ) else 0))))
      = LinearMap.ker (LinearMap.pi fun i : Fin 2 =>
        (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin 2 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin 2 → ℂ) (Fin m × Fin 2 → ℂ)) :=
  ⟨finrank_comap ω x hx0, span_bv ω⟩
