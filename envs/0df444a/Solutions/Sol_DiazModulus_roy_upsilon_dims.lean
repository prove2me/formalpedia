-- Prove2me | solution 1 for DiazModulus.roy_upsilon_dims
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T10:03:38.94032+00:00
-- url     : https://prove2.me/submissions/728195f9-18f3-4a07-b707-8979cdf36d6e

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The map `Υ`: preimages, kernel and joins
Write `Υ(u, v)_i = u_i + Σ_k ω_k v_{(k,i)}` on `ℂ^d × ℂ^{m×d}`. The map `Υ` is surjective, since
`Υ(u, 0) = u`. For a subspace `U ⊆ ℂ^d`, the composite of `Υ` with the quotient map
`ℂ^d → ℂ^d / U` is surjective with kernel `Υ⁻¹(U)`; rank–nullity on a domain of dimension
`d + md`, together with `dim(ℂ^d / U) + dim U = d`, gives `dim Υ⁻¹(U) = dim U + md`.
For the kernel, each vector `b_p = (−ω_{p.1} e_{p.2}, e_p)` lies in `ker Υ` by a direct
computation, and every `z ∈ ker Υ` equals `Σ_p z.2(p) • b_p`: the second coordinates agree
trivially, and the first coordinates agree because `z.1_i = −Σ_k ω_k z.2(k,i)` on the kernel.
For the join, `ker Υ ⊔ X = Υ⁻¹(Υ(X))` (`Submodule.comap_map_eq`), so the first claim applied to
`U = Υ(X)` gives `dim(ker Υ ⊔ X) = md + dim Υ(X)`. -/

namespace RC1_UD
open DiazModulus

/-- The map `Υ`, verbatim. -/
noncomputable def Ups (d m : ℕ) (ω : Fin m → ℂ) :
    ((Fin d → ℂ) × (Fin m × Fin d → ℂ)) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d =>
    (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
    + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)

theorem Ups_apply {d m : ℕ} (ω : Fin m → ℂ) (z : (Fin d → ℂ) × (Fin m × Fin d → ℂ)) (i : Fin d) :
    Ups d m ω z i = z.1 i + ∑ k, ω k * z.2 (k, i) := by
  simp [Ups, LinearMap.sum_apply]

theorem Ups_range {d m : ℕ} (ω : Fin m → ℂ) : LinearMap.range (Ups d m ω) = ⊤ :=
  LinearMap.range_eq_top.mpr fun u => ⟨(u, 0), by ext i; simp [Ups_apply]⟩

theorem finrank_dom (d m : ℕ) :
    Module.finrank ℂ ((Fin d → ℂ) × (Fin m × Fin d → ℂ)) = d + m * d := by
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_prod]

theorem finrank_comap {d m : ℕ} (ω : Fin m → ℂ) (U : Submodule ℂ (Fin d → ℂ)) :
    Module.finrank ℂ ↥(U.comap (Ups d m ω)) = Module.finrank ℂ ↥U + m * d := by
  set f := U.mkQ ∘ₗ Ups d m ω
  have hker : LinearMap.ker f = U.comap (Ups d m ω) := by
    simp [f, LinearMap.ker_comp]
  have hrange : LinearMap.range f = ⊤ := by
    simp only [f, LinearMap.range_comp, Ups_range, Submodule.map_top, Submodule.range_mkQ]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_quotient_add_finrank U
  have h3 : Module.finrank ℂ (Fin d → ℂ) = d := by simp
  rw [hrange, finrank_top, hker, finrank_dom] at h1
  omega

/-- The spanning vectors. -/
def bv {d m : ℕ} (ω : Fin m → ℂ) (p : Fin m × Fin d) : (Fin d → ℂ) × (Fin m × Fin d → ℂ) :=
  ((fun i => if i = p.2 then -ω p.1 else 0), (fun q => if q = p then (1 : ℂ) else 0))

theorem bv_mem_ker {d m : ℕ} (ω : Fin m → ℂ) (p : Fin m × Fin d) :
    bv ω p ∈ LinearMap.ker (Ups d m ω) := by
  rw [LinearMap.mem_ker]
  ext i
  rw [Ups_apply]
  obtain ⟨a, b⟩ := p
  by_cases hi : i = b
  · subst hi
    simp [bv, Prod.ext_iff]
  · have : ∀ k : Fin m, ((k, i) : Fin m × Fin d) ≠ (a, b) := fun k h => hi (Prod.ext_iff.mp h).2
    simp [bv, hi, this]

theorem span_bv {d m : ℕ} (ω : Fin m → ℂ) :
    Submodule.span ℂ (Set.range (bv (d := d) ω)) = LinearMap.ker (Ups d m ω) := by
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
        simp [bv, mul_comm]
      · ext q
        rw [Prod.snd_sum, Finset.sum_apply]
        simp [bv]
    rw [hsum]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

theorem finrank_ker_sup {d m : ℕ} (ω : Fin m → ℂ)
    (X : Submodule ℂ ((Fin d → ℂ) × (Fin m × Fin d → ℂ))) :
    Module.finrank ℂ ↥(LinearMap.ker (Ups d m ω) ⊔ X) =
      m * d + Module.finrank ℂ ↥(X.map (Ups d m ω)) := by
  rw [sup_comm, ← Submodule.comap_map_eq, finrank_comap, add_comm]

end RC1_UD

open DiazModulus RC1_UD in
theorem solution {d m : ℕ} (ω : Fin m → ℂ) (U : Submodule ℂ (Fin d → ℂ))
    (X : Submodule ℂ ((Fin d → ℂ) × (Fin m × Fin d → ℂ))) :
    Module.finrank ℂ ↥(U.comap (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ))) = Module.finrank ℂ ↥(U) + m * d ∧
    Submodule.span ℂ (Set.range (fun p : Fin m × Fin d =>
        ((fun i => if i = p.2 then -ω p.1 else 0), (fun q => if q = p then (1 : ℂ) else 0)))) =
      LinearMap.ker (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) ∧
    Module.finrank ℂ ↥(LinearMap.ker (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) ⊔ X) = m * d + Module.finrank ℂ ↥(X.map (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ))) :=
  ⟨finrank_comap ω U, span_bv ω, finrank_ker_sup ω X⟩
