-- Prove2me | solution 1 for DiazModulus.fischler_rational_hull
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:24:56.443648+00:00
-- url     : https://prove2.me/submissions/e89b8b64-c3fc-4b35-9681-ba58bda0709c

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The rational hull of a complex vector

Let `V` be the `Q̄`-span of the coordinates `v₁, …, v_m`; it is finite-dimensional, say of dimension `n`, with a
`Q̄`-basis `b₁, …, b_n`. Put `cₐ = bₐ` and let `w_{a,i}` be the `a`-th coordinate of `vᵢ` in this basis. Then the
`cₐ` are `Q̄`-free, every `w_{a,i}` is algebraic, and `v = Σₐ cₐ wₐ`. The vectors `wₐ` are `Q̄`-free: a relation
`Σₐ γₐ wₐ = 0` says that the linear form `Σₐ γₐ b*ₐ` on `V` vanishes at every `vᵢ`, hence on their span `V`, hence
at each `bₐ`, which gives `γₐ = 0`. Finally, if `ψ` is algebraic and `ψ · v = 0`, then
`Σₐ (ψ · wₐ) cₐ = ψ · v = 0` is a `Q̄`-relation among the free `cₐ` (each `ψ · wₐ` is algebraic), so every
`ψ · wₐ` vanishes. -/

open DiazModulus in
theorem solution {m : ℕ} (v : Fin m → ℂ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → Fin m → ℂ),
      n = Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range v)) ∧
      LinearIndependent (↥Qbar) c ∧ LinearIndependent (↥Qbar) w ∧ (∀ a i, w a i ∈ Qbar) ∧
      v = ∑ a, c a • w a ∧
      ∀ ψ : Fin m → ℂ, (∀ i, ψ i ∈ Qbar) → ψ ⬝ᵥ v = 0 → ∀ a, ψ ⬝ᵥ w a = 0 := by
  classical
  set V := Submodule.span (↥Qbar) (Set.range v) with hV
  have hvV : ∀ i, v i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  have : Module.Finite (↥Qbar) V := FiniteDimensional.span_of_finite (↥Qbar) (Set.finite_range v)
  let b := Module.finBasis (↥Qbar) V
  set c : Fin (Module.finrank (↥Qbar) V) → ℂ := fun a => (b a : ℂ) with hc
  set w : Fin (Module.finrank (↥Qbar) V) → Fin m → ℂ :=
    fun a i => ((b.repr ⟨v i, hvV i⟩ a : ↥Qbar) : ℂ) with hw
  have hcfree : LinearIndependent (↥Qbar) c :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hvc : v = ∑ a, c a • w a := by
    funext i
    have h := congrArg Subtype.val (b.sum_repr ⟨v i, hvV i⟩)
    rw [Submodule.coe_sum] at h
    rw [Finset.sum_apply]
    refine h.symm.trans (Finset.sum_congr rfl fun a _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Submodule.coe_smul, Subfield.smul_def, hc, hw]
    ring
  refine ⟨_, c, w, rfl, hcfree, ?_, fun a i => (b.repr ⟨v i, hvV i⟩ a).2, hvc, ?_⟩
  · -- the `w a` are Q̄-free: a relation would give a linear form on `V` killing every `v i`
    rw [Fintype.linearIndependent_iff]
    intro γ hγ a
    set f : V →ₗ[↥Qbar] ↥Qbar := ∑ a', γ a' • b.coord a' with hf
    have hf0 : f = 0 := by
      refine LinearMap.ext_on (Submodule.span_span_coe_preimage (R := ↥Qbar) (s := Set.range v)) ?_
      rintro ⟨x, hx⟩ ⟨i, hi⟩
      have hxi : (⟨x, hx⟩ : V) = ⟨v i, hvV i⟩ := Subtype.ext hi.symm
      rw [hxi]
      have := congr_fun hγ i
      simp only [Finset.sum_apply, Pi.smul_apply, Subfield.smul_def, smul_eq_mul, hw,
        Pi.zero_apply] at this
      have h1 : f ⟨v i, hvV i⟩ = ∑ a', γ a' * b.repr ⟨v i, hvV i⟩ a' := by
        simp [hf, LinearMap.sum_apply, Module.Basis.coord_apply]
      rw [h1, LinearMap.zero_apply]
      apply Subtype.val_injective
      push_cast
      exact this
    have := LinearMap.congr_fun hf0 (b a)
    simpa [hf, LinearMap.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply] using this
  · intro ψ hψ hψv a
    have hrel := Fintype.linearIndependent_iff.1 hcfree
      (fun a => ⟨ψ ⬝ᵥ w a, Qbar.sum_mem fun i _ => Qbar.mul_mem (hψ i) (b.repr ⟨v i, hvV i⟩ a).2⟩)
      (by
        rw [hvc, dotProduct_sum] at hψv
        rw [← hψv]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Subfield.smul_def, smul_eq_mul, dotProduct_smul, smul_eq_mul, mul_comm])
    exact congrArg Subtype.val (hrel a)
