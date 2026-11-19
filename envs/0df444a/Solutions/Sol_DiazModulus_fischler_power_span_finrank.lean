-- Prove2me | solution 1 for DiazModulus.fischler_power_span_finrank
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:24:53.743694+00:00
-- url     : https://prove2.me/submissions/a919e9c8-36b9-44d5-ad40-35942f401bb4

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_strong_six_exponentials_unconditional

open Complex ComplexConjugate

/-! # The Q̄-span of the coordinates of a power in ℒ̃

Let `V` be the `Q̄`-span of `v₁, …, v_m`. Step 0: expanding each factor in the `vᵢ`, every product of `k`
elements of `V` is a `Q̄`-combination of products `v_{I(0)}⋯v_{I(k−1)}`, hence lies in `ℒ̃`.
Step 1 (`dim V ≤ 2`): otherwise pick `c₀, c₁, c₂ ∈ V` free over `Q̄` and write `k = p + 2`. Take `x = (c₀, c₁)`
and `y = c₀ᵖ·(c₀, c₁, c₂)`; both are `Q̄`-free (multiplication by `c₀ᵖ ≠ 0` is injective), and each `xᵢyⱼ` is
`c₀ᵖ·cᵢcⱼ`, a product of `k` elements of `V`, so in `ℒ̃` by Step 0. Roy's strong six exponentials theorem, in
product form, forbids this.
Step 2 (`dim V ≤ 1` when `k ≥ 3`): otherwise pick `c₀, c₁ ∈ V` free over `Q̄` and write `k = p + 3`. The ratio
`τ = c₁/c₀` is not algebraic (else `τc₀ − c₁ = 0` is a `Q̄`-relation), hence transcendental over `Q̄`, so
`1, τ, τ²` are `Q̄`-free. Take `x = (c₀, c₁)` and `y = c₀^{p+2}·(1, τ, τ²) = c₀ᵖ·(c₀², c₀c₁, c₁²)`: each `xᵢyⱼ` is
`c₀ᵖ` times a product of three elements of `V`, so in `ℒ̃` by Step 0, and the same theorem gives a contradiction. -/

namespace RC9_F3
open DiazModulus

/-- Step 0: every product of `k` elements of `span_Q̄ {v_i}` lies in `ℒ̃`. -/
theorem prod_mem_of_span {m k : ℕ} (v : Fin m → ℂ)
    (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) (u : Fin k → ℂ)
    (hu : ∀ t, u t ∈ Submodule.span (↥Qbar) (Set.range v)) : ∏ t, u t ∈ LogAlgTilde := by
  classical
  choose A hA using fun t => (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (hu t)
  have key : ∏ t, u t = ∑ I : Fin k → Fin m, ((∏ t, A t (I t) : ↥Qbar) : ℂ) * ∏ t, v (I t) := by
    simp_rw [← hA, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [show ((∏ t, A t (I t) : ↥Qbar) : ℂ) = ∏ t, (A t (I t) : ℂ) from map_prod Qbar.subtype _ _,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Subfield.smul_def, smul_eq_mul]
  rw [key]
  refine Submodule.sum_mem _ fun I _ => ?_
  have := Submodule.smul_mem LogAlgTilde (∏ t, A t (I t)) (hv I)
  rwa [Subfield.smul_def, smul_eq_mul] at this

theorem transcendental_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental Qbar u := by
  have : Algebra.IsAlgebraic ℚ Qbar := ⟨fun x =>
    (isAlgebraic_algHom_iff (Qbar.subtype.toRatAlgHom) Subtype.val_injective).1
      (mem_Qbar_iff.1 x.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h => hu (mem_Qbar_iff.2 h)

theorem linInd_pow {u : ℂ} (hu : Transcendental Qbar u) {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) : LinearIndependent Qbar (fun i => u ^ f i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hp : (∑ j, Polynomial.C (g j) * Polynomial.X ^ f j : Polynomial Qbar) = 0 := by
    by_contra hne
    exact hu ⟨_, hne, by simpa [Polynomial.aeval_def, Polynomial.eval₂_finsetSum,
      Algebra.smul_def] using hg⟩
  have := congrArg (fun p : Polynomial Qbar => p.coeff (f i)) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hf.eq_iff] using this

/-- Multiplying a `Q̄`-free family by a non-zero constant keeps it free. -/
theorem linInd_mul {n : ℕ} {c : ℂ} (hc : c ≠ 0) {w : Fin n → ℂ}
    (hw : LinearIndependent (↥Qbar) w) : LinearIndependent (↥Qbar) (fun j => c * w j) := by
  have hker : LinearMap.ker (LinearMap.mulLeft (↥Qbar) c) = ⊥ :=
    LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc)
  have heq : (fun j => c * w j) = (LinearMap.mulLeft (↥Qbar) c) ∘ w := by
    funext j; simp only [Function.comp_apply, LinearMap.mulLeft_apply]
  rw [heq]
  exact hw.map' _ hker

end RC9_F3

open DiazModulus RC9_F3 in
theorem solution {m k : ℕ} (hk : 2 ≤ k) (v : Fin m → ℂ)
    (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range v)) ≤ 2 ∧
      (3 ≤ k → Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range v)) ≤ 1) := by
  set V := Submodule.span (↥Qbar) (Set.range v) with hV
  have hP := prod_mem_of_span v hv
  -- free families in `V`, as families of complex numbers
  have hfam : ∀ r, r ≤ Module.finrank (↥Qbar) V →
      ∃ c : Fin r → ℂ, LinearIndependent (↥Qbar) c ∧ ∀ i, c i ∈ V := by
    intro r hr
    obtain ⟨c, hc⟩ := exists_linearIndependent_of_le_finrank hr
    exact ⟨fun i => (c i : ℂ), hc.map' V.subtype (Submodule.ker_subtype V), fun i => (c i).2⟩
  constructor
  · -- Step 1: `dim V ≤ 2`
    by_contra h
    obtain ⟨c, hc, hcV⟩ := hfam 3 (by omega)
    obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
    have key2 : ∀ a ∈ V, ∀ b ∈ V, c 0 ^ p * (a * b) ∈ LogAlgTilde := by
      intro a ha b hb
      have := hP (Fin.append (fun _ : Fin p => c 0) ![a, b]) (by
        intro t
        refine Fin.addCases (fun i => ?_) (fun i => ?_) t
        · simpa using hcV 0
        · fin_cases i <;> simpa)
      simpa [Fin.prod_univ_add, Fin.prod_univ_two, mul_assoc] using this
    have hc0 : c 0 ≠ 0 := hc.ne_zero 0
    refine DiazModulus.strong_six_exponentials_unconditional (fun i : Fin 2 => c (Fin.castSucc i))
      (fun j => c 0 ^ p * c j) (hc.comp _ (Fin.castSucc_injective 2))
      (linInd_mul (pow_ne_zero p hc0) hc) fun i j => ?_
    have := key2 _ (hcV (Fin.castSucc i)) _ (hcV j)
    convert this using 1
    ring
  · -- Step 2: `dim V ≤ 1` when `k ≥ 3`
    intro hk3
    by_contra h
    obtain ⟨c, hc, hcV⟩ := hfam 2 (by omega)
    obtain ⟨p, rfl⟩ : ∃ p, k = p + 3 := ⟨k - 3, by omega⟩
    have key3 : ∀ a ∈ V, ∀ b ∈ V, ∀ d ∈ V, c 0 ^ p * (a * b * d) ∈ LogAlgTilde := by
      intro a ha b hb d hd
      have := hP (Fin.append (fun _ : Fin p => c 0) ![a, b, d]) (by
        intro t
        refine Fin.addCases (fun i => ?_) (fun i => ?_) t
        · simpa using hcV 0
        · fin_cases i <;> simpa)
      simpa [Fin.prod_univ_add, Fin.prod_univ_three, mul_assoc] using this
    have hc0 : c 0 ≠ 0 := hc.ne_zero 0
    set τ := c 1 / c 0 with hτ
    have hτc : τ * c 0 = c 1 := div_mul_cancel₀ _ hc0
    have hτQ : τ ∉ Qbar := by
      intro hτQ
      have := Fintype.linearIndependent_iff.1 hc ![⟨τ, hτQ⟩, -1] (by
        simp [Fin.sum_univ_two, Subfield.smul_def, hτc])
      simpa using this 1
    have hy : LinearIndependent (↥Qbar) (fun j : Fin 3 => c 0 ^ (p + 2) * τ ^ (j : ℕ)) :=
      linInd_mul (pow_ne_zero _ hc0)
        (linInd_pow (transcendental_of_not_mem hτQ) (fun j : Fin 3 => (j : ℕ)) Fin.val_injective)
    refine DiazModulus.strong_six_exponentials_unconditional c _ hc hy fun i j => ?_
    have hcV' : ∀ j : Fin 3, ![c 0, c 0, c 1] j ∈ V ∧ ![c 0, c 1, c 1] j ∈ V := by
      intro j; fin_cases j <;> simp [hcV]
    have := key3 _ (hcV i) _ (hcV' j).1 _ (hcV' j).2
    convert this using 1
    fin_cases j <;> simp [← hτc] <;> ring
