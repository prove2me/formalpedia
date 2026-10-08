-- Prove2me | solution 1 for DiazModulus.generic_circle_point_no_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-04T18:34:05.318913+00:00
-- url     : https://prove2.me/submissions/fb219f84-04d0-4910-94bd-fdde77cf3a82

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# No `2 × 3` configuration on a generic point of a circle (Theorem A of `R4_NOTES.md`, `k = 1`)

Let `u ≠ 0` with `ρ = u ū` algebraic, and let `u, w₁, …, w_m` be algebraically independent over
`Q̄`. Put `E = span_Q̄ {1, u, ū, w₁, …, w_m}`. Then there are no `Q̄`-free `x₁, x₂` and `y₁, y₂, y₃`
with every `xᵢ yⱼ ∈ E`.

**Model.** `P = Q̄[X₀, X₁, …, X_m]`, evaluated at `X₀ ↦ u`, `X_{j+1} ↦ w_j`; this is injective. Since
`u ū = ρ`, every element of `u E` is the value of a *good* polynomial: total degree at most `2`, and
constant after `X₀ = 0`. (The good polynomials are exactly the span of `1, X₀, X₀², X₀ X_{j+1}`;
only the generators and closure under linear combinations are used.)

**Proof.** Steps 1–2 follow the notes; their steps 3–5 (weights, and the count of differences in
`S`) are replaced by a total-degree count and the specialisation `X₀ = 0`.
1. Pull back: `u xᵢ yⱼ = ev aᵢⱼ` with `aᵢⱼ` good, and `(aᵢⱼ)` has rank one.
2. Factor in the UFD `P`: `a₀ⱼ = h cⱼ`, `a₁ⱼ = g cⱼ`, with `h, g` free and `c₀, c₁, c₂` free.
3. Degrees add in a domain, so `deg h + deg cⱼ ≤ 2`; `X₀ = 0` is a ring map, so `π(h) π(cⱼ)` is
   constant. Either `π h = π g = 0`, or every `π cⱼ` is constant. In each case a short degree count
   puts `h, g` in a line or `c₀, c₁, c₂` in a plane, against freeness.
-/

namespace R4_generic_circle_point

open MvPolynomial

section Algebra

variable {K : Type*} [Field K] {m : ℕ}

/-- Setting the first variable to zero: `p ↦ p(0, X₁, …, X_m)`. -/
noncomputable def piZ (m : ℕ) : MvPolynomial (Fin (m + 1)) K →+* MvPolynomial (Fin m) K :=
  Polynomial.constantCoeff.comp (finSuccEquiv K m).toRingEquiv.toRingHom

theorem piZ_apply (p : MvPolynomial (Fin (m + 1)) K) :
    piZ m p = (finSuccEquiv K m p).coeff 0 := rfl

theorem piZ_C (r : K) : piZ m (C r : MvPolynomial (Fin (m + 1)) K) = C r := by
  simp [piZ_apply, finSuccEquiv_apply]

theorem piZ_X_zero : piZ m (X 0 : MvPolynomial (Fin (m + 1)) K) = 0 := by
  simp [piZ_apply, finSuccEquiv_X_zero]

/-- The polynomial image of `u · E`: total degree at most two, constant after `X₀ = 0`. -/
def Good (p : MvPolynomial (Fin (m + 1)) K) : Prop :=
  p.totalDegree ≤ 2 ∧ ∃ a : K, piZ m p = C a

theorem good_zero : Good (0 : MvPolynomial (Fin (m + 1)) K) :=
  ⟨by simp, 0, by simp⟩

theorem Good.add {p q : MvPolynomial (Fin (m + 1)) K} (hp : Good p) (hq : Good q) :
    Good (p + q) := by
  obtain ⟨hp1, a, ha⟩ := hp
  obtain ⟨hq1, b, hb⟩ := hq
  exact ⟨(totalDegree_add p q).trans (max_le hp1 hq1), a + b, by rw [map_add, ha, hb, C_add]⟩

theorem Good.smul (r : K) {p : MvPolynomial (Fin (m + 1)) K} (hp : Good p) : Good (r • p) := by
  obtain ⟨hp1, a, ha⟩ := hp
  exact ⟨(totalDegree_smul_le r p).trans hp1, r * a, by
    rw [smul_eq_C_mul, map_mul, ha, piZ_C, C_mul]⟩

theorem good_C (r : K) : Good (C r : MvPolynomial (Fin (m + 1)) K) :=
  ⟨by rw [totalDegree_C]; norm_num, r, piZ_C r⟩

theorem good_X0 : Good (X 0 : MvPolynomial (Fin (m + 1)) K) :=
  ⟨by rw [totalDegree_X]; norm_num, 0, by rw [piZ_X_zero, C_0]⟩

theorem good_X0_mul (q : MvPolynomial (Fin (m + 1)) K) (hq : q.totalDegree ≤ 1) :
    Good (X 0 * q) :=
  ⟨(totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega), 0, by
    rw [map_mul, piZ_X_zero, zero_mul, C_0]⟩

/-- A polynomial of degree at most one that is constant after `X₀ = 0` lies in `K + K X₀`. -/
theorem lin_of_piZ (f : MvPolynomial (Fin (m + 1)) K) (a : K) (hd : f.totalDegree ≤ 1)
    (hπ : piZ m f = C a) : ∃ b : K, f = C a + C b * X 0 := by
  have hX : (Polynomial.X : Polynomial (MvPolynomial (Fin m) K)) ∣ finSuccEquiv K m (f - C a) := by
    rw [Polynomial.X_dvd_iff, map_sub, Polynomial.coeff_sub, ← piZ_apply, ← piZ_apply, hπ, piZ_C,
      sub_self]
  obtain ⟨q, hq⟩ := hX
  have hfq : f - C a = X 0 * (finSuccEquiv K m).symm q := by
    apply (finSuccEquiv K m).injective
    rw [hq, map_mul, finSuccEquiv_X_zero, AlgEquiv.apply_symm_apply]
  by_cases hq0 : (finSuccEquiv K m).symm q = 0
  · refine ⟨0, ?_⟩
    rw [C_0, zero_mul, add_zero]
    exact sub_eq_zero.1 (by rw [hfq, hq0, mul_zero])
  · have h1 : (X 0 * (finSuccEquiv K m).symm q).totalDegree ≤ 1 := by
      rw [← hfq]
      exact (totalDegree_sub _ _).trans (max_le hd (by simp))
    rw [totalDegree_mul_of_isDomain (X_ne_zero _) hq0, totalDegree_X] at h1
    have h2 := totalDegree_eq_zero_iff_eq_C.1 (show ((finSuccEquiv K m).symm q).totalDegree = 0 by
      omega)
    refine ⟨((finSuccEquiv K m).symm q).coeff 0, ?_⟩
    rw [← sub_eq_iff_eq_add', hfq, mul_comm]
    exact congrArg (· * X 0) h2

/-- In a domain, if `p q` is constant and `p ≠ 0` then `q` is constant. -/
theorem const_of_mul_const {p q : MvPolynomial (Fin m) K} (hp : p ≠ 0) {α : K}
    (h : p * q = C α) : ∃ β : K, q = C β := by
  by_cases hq : q = 0
  · exact ⟨0, by rw [hq, C_0]⟩
  · have h1 := totalDegree_mul_of_isDomain hp hq
    rw [h, totalDegree_C] at h1
    exact ⟨_, totalDegree_eq_zero_iff_eq_C.1 (by omega)⟩

/-- `n` free vectors do not fit in the span of `k < n` vectors. -/
theorem not_li {V : Type*} [AddCommGroup V] [Module K V] {n k : ℕ} (hk : k < n)
    {f : Fin n → V} (hf : LinearIndependent K f) (b : Fin k → V)
    (hmem : ∀ i, f i ∈ Submodule.span K (Set.range b)) : False := by
  have h1 : LinearIndependent K (fun i => (⟨f i, hmem i⟩ : Submodule.span K (Set.range b))) :=
    LinearIndependent.of_comp (Submodule.span K (Set.range b)).subtype hf
  have : FiniteDimensional K (Submodule.span K (Set.range b)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range b)
  have h2 := h1.fintype_card_le_finrank
  have h3 := finrank_range_le_card (R := K) b
  simp only [Fintype.card_fin] at h2 h3
  exact absurd (h2.trans h3) (by omega)

theorem mem_span_lin (a b : K) :
    (C a + C b * X 0 : MvPolynomial (Fin (m + 1)) K) ∈
      Submodule.span K (Set.range ![(1 : MvPolynomial (Fin (m + 1)) K), X 0]) :=
  (Submodule.mem_span_range_iff_exists_fun K).2 ⟨![a, b], by
    simp [Fin.sum_univ_two, smul_eq_C_mul]⟩

theorem mem_span_C (a : K) :
    (C a : MvPolynomial (Fin (m + 1)) K) ∈ Submodule.span K (Set.range ![1]) :=
  (Submodule.mem_span_range_iff_exists_fun K).2 ⟨![a], by simp [smul_eq_C_mul]⟩

theorem mem_span_CX (b : K) :
    (C b * X 0 : MvPolynomial (Fin (m + 1)) K) ∈ Submodule.span K (Set.range ![X 0]) :=
  (Submodule.mem_span_range_iff_exists_fun K).2 ⟨![b], by simp [smul_eq_C_mul]⟩

variable {h g : MvPolynomial (Fin (m + 1)) K} {c : Fin 3 → MvPolynomial (Fin (m + 1)) K}

/-- Case `π h = π g = 0`: then `h, g ∈ K X₀`, unless all `cⱼ` are constant. -/
theorem key_caseB (hhg : LinearIndependent K ![h, g]) (hc : LinearIndependent K c)
    (dh : ∀ j, h.totalDegree + (c j).totalDegree ≤ 2)
    (dg : ∀ j, g.totalDegree + (c j).totalDegree ≤ 2)
    (hπh : piZ m h = 0) (hπg : piZ m g = 0) : False := by
  by_cases hcd : ∀ j, (c j).totalDegree = 0
  · refine not_li (by norm_num : 2 < 3) hc ![1, X 0] fun j => ?_
    rw [totalDegree_eq_zero_iff_eq_C.1 (hcd j)]
    simpa using mem_span_lin (m := m) ((c j).coeff 0) 0
  · push Not at hcd
    obtain ⟨j, hj⟩ := hcd
    obtain ⟨b, hb⟩ := lin_of_piZ h 0 (by have := dh j; omega) (by rw [hπh, C_0])
    obtain ⟨b', hb'⟩ := lin_of_piZ g 0 (by have := dg j; omega) (by rw [hπg, C_0])
    refine not_li (by norm_num : 1 < 2) hhg ![X 0] (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simpa [hb] using mem_span_CX (m := m) b
    · simpa [hb'] using mem_span_CX (m := m) b'

/-- Case all `π cⱼ` constant: then `cⱼ ∈ K + K X₀`, unless `h, g` are constant. -/
theorem key_caseA (hhg : LinearIndependent K ![h, g]) (hc : LinearIndependent K c)
    (dh : ∀ j, h.totalDegree + (c j).totalDegree ≤ 2)
    (dg : ∀ j, g.totalDegree + (c j).totalDegree ≤ 2)
    (hpc : ∀ j, ∃ β : K, piZ m (c j) = C β) : False := by
  by_cases hcd : ∀ j, (c j).totalDegree ≤ 1
  · refine not_li (by norm_num : 2 < 3) hc ![1, X 0] fun j => ?_
    obtain ⟨β, hβ⟩ := hpc j
    obtain ⟨b, hb⟩ := lin_of_piZ (c j) β (hcd j) hβ
    rw [hb]
    exact mem_span_lin β b
  · push Not at hcd
    obtain ⟨j, hj⟩ := hcd
    have h0 : h.totalDegree = 0 := by have := dh j; omega
    have g0 : g.totalDegree = 0 := by have := dg j; omega
    refine not_li (by norm_num : 1 < 2) hhg ![1] (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [Matrix.cons_val_zero, totalDegree_eq_zero_iff_eq_C.1 h0]
      exact mem_span_C _
    · rw [Matrix.cons_val_one, Matrix.cons_val_zero, totalDegree_eq_zero_iff_eq_C.1 g0]
      exact mem_span_C _

/-- **The polynomial core.** No good rank-one matrix `(h, g) ⊗ (c₀, c₁, c₂)` with free factors. -/
theorem key (hhg : LinearIndependent K ![h, g]) (hc : LinearIndependent K c)
    (hgood : ∀ j, Good (h * c j) ∧ Good (g * c j)) : False := by
  have hh : h ≠ 0 := by simpa using hhg.ne_zero 0
  have hg : g ≠ 0 := by simpa using hhg.ne_zero 1
  have dh : ∀ j, h.totalDegree + (c j).totalDegree ≤ 2 := fun j => by
    rw [← totalDegree_mul_of_isDomain hh (hc.ne_zero j)]; exact (hgood j).1.1
  have dg : ∀ j, g.totalDegree + (c j).totalDegree ≤ 2 := fun j => by
    rw [← totalDegree_mul_of_isDomain hg (hc.ne_zero j)]; exact (hgood j).2.1
  by_cases hπ : piZ m h = 0 ∧ piZ m g = 0
  · exact key_caseB hhg hc dh dg hπ.1 hπ.2
  · refine key_caseA hhg hc dh dg fun j => ?_
    rcases not_and_or.1 hπ with h1 | h1
    · obtain ⟨α, hα⟩ := (hgood j).1.2
      exact const_of_mul_const h1 (by rw [← map_mul]; exact hα)
    · obtain ⟨α, hα⟩ := (hgood j).2.2
      exact const_of_mul_const h1 (by rw [← map_mul]; exact hα)

/-- A rank-one `2 × 3` matrix over the UFD `P` with `a₀₀ ≠ 0` factors as `(h, g) ⊗ c`. -/
theorem factor (a : Fin 2 → Fin 3 → MvPolynomial (Fin (m + 1)) K)
    (hr : ∀ j l, a 0 j * a 1 l = a 0 l * a 1 j) (h0 : a 0 0 ≠ 0) :
    ∃ h g : MvPolynomial (Fin (m + 1)) K, ∃ c : Fin 3 → MvPolynomial (Fin (m + 1)) K,
      ∀ j, a 0 j = h * c j ∧ a 1 j = g * c j := by
  obtain ⟨g, h, d, hrel, hdg, hdh⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' (a 1 0) (a 0 0) h0
  have hd : d ≠ 0 := by rintro rfl; exact h0 (by rw [← hdh, zero_mul])
  have hh : h ≠ 0 := by rintro rfl; exact h0 (by rw [← hdh, mul_zero])
  have hkey : ∀ j, g * a 0 j = h * a 1 j := fun j =>
    mul_left_cancel₀ hd (by linear_combination (a 0 j) * hdg + hr j 0 - (a 1 j) * hdh)
  have hdiv : ∀ j, h ∣ a 0 j := fun j => hrel.symm.dvd_of_dvd_mul_left ⟨a 1 j, hkey j⟩
  choose c hc using hdiv
  refine ⟨h, g, c, fun j => ⟨hc j, ?_⟩⟩
  apply mul_left_cancel₀ hh
  rw [← hkey j, hc j]
  ring

end Algebra

/-- Freeness pulls back along a linear map that sends the family to a non-zero multiple of a
free family. -/
theorem li_of_map {K V : Type*} [Field K] [Algebra K ℂ] [AddCommGroup V] [Module K V] {n : ℕ}
    (Φ : V →ₗ[K] ℂ) (f : Fin n → V) {z : ℂ} (hz : z ≠ 0) {v : Fin n → ℂ}
    (hv : LinearIndependent K v) (he : ∀ j, Φ (f j) = z * v j) : LinearIndependent K f := by
  have h1 := hv.map' (LinearMap.mulLeft K z) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hz))
  have h2 : ⇑(LinearMap.mulLeft K z) ∘ v = Φ ∘ f := by
    funext j
    simp [he]
  rw [h2] at h1
  exact h1.of_comp _

/-- Every element of `u · E` is the value at `(u, w)` of a good polynomial. -/
theorem transfer {m : ℕ} (u : ℂ) (w : Fin m → ℂ) (ρ : ↥DiazModulus.Qbar) (hρ : u * conj u = ρ)
    {e : ℂ} (he : e ∈ Submodule.span DiazModulus.Qbar (({1, u, conj u} : Set ℂ) ∪ Set.range w)) :
    ∃ p : MvPolynomial (Fin (m + 1)) ↥DiazModulus.Qbar, Good p ∧
      aeval (Fin.cons u w : Fin (m + 1) → ℂ) p = u * e := by
  induction he using Submodule.span_induction with
  | mem z hz =>
    rcases hz with (rfl | rfl | rfl) | ⟨j, rfl⟩
    · exact ⟨X 0, good_X0, by simp⟩
    · exact ⟨X 0 * X 0, good_X0_mul _ (by rw [totalDegree_X]), by simp⟩
    · exact ⟨C ρ, good_C ρ, by rw [aeval_C, hρ]; rfl⟩
    · exact ⟨X 0 * X j.succ, good_X0_mul _ (by rw [totalDegree_X]), by simp⟩
  | zero => exact ⟨0, good_zero, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp, hpe⟩ := ha
    obtain ⟨q, hq, hqe⟩ := hb
    exact ⟨p + q, hp.add hq, by rw [map_add, hpe, hqe, mul_add]⟩
  | smul r a _ ha =>
    obtain ⟨p, hp, hpe⟩ := ha
    exact ⟨r • p, hp.smul r, by rw [map_smul, hpe, mul_smul_comm]⟩

end R4_generic_circle_point

open DiazModulus R4_generic_circle_point MvPolynomial in
theorem solution (m : ℕ) (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u)) (w : Fin m → ℂ)
    (hgen : AlgebraicIndependent (↥Qbar) (Fin.cons u w : Fin (m + 1) → ℂ))
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) :
    ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, conj u} : Set ℂ) ∪ Set.range w) := by
  intro hmem
  have hinj : Function.Injective
      (aeval (Fin.cons u w : Fin (m + 1) → ℂ) : MvPolynomial (Fin (m + 1)) ↥Qbar → ℂ) := hgen
  -- 1. Pull back: `u xᵢ yⱼ = ev aᵢⱼ` with `aᵢⱼ` good; the matrix `(aᵢⱼ)` has rank one.
  have hex : ∀ i j, ∃ p : MvPolynomial (Fin (m + 1)) ↥Qbar, Good p ∧
      aeval (Fin.cons u w : Fin (m + 1) → ℂ) p = u * (x i * y j) := fun i j =>
    transfer u w ⟨u * conj u, mem_Qbar_iff.2 hρ⟩ rfl (hmem i j)
  choose a ha hae using hex
  have hr : ∀ j l, a 0 j * a 1 l = a 0 l * a 1 j := fun j l => hinj (by
    simp only [map_mul, hae]; ring)
  have ha00 : a 0 0 ≠ 0 := by
    intro h0
    have := hae 0 0
    rw [h0, map_zero] at this
    exact mul_ne_zero hu (mul_ne_zero (hx.ne_zero 0) (hy.ne_zero 0)) this.symm
  -- 2. Factor `a = (h, g) ⊗ c`; freeness of `x` and `y` passes to `(h, g)` and `c`.
  obtain ⟨h, g, c, hc⟩ := factor a hr ha00
  have hcl : LinearIndependent (↥Qbar) c :=
    li_of_map ((aeval (Fin.cons u w : Fin (m + 1) → ℂ)).toLinearMap ∘ₗ LinearMap.mulLeft _ h) c
      (mul_ne_zero hu (hx.ne_zero 0)) hy fun j => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
        rw [← (hc j).1, hae]; ring
  have hhg : LinearIndependent (↥Qbar) ![h, g] :=
    li_of_map ((aeval (Fin.cons u w : Fin (m + 1) → ℂ)).toLinearMap ∘ₗ
        LinearMap.mulRight _ (c 0)) ![h, g] (mul_ne_zero hu (hy.ne_zero 0)) hx
      (Fin.forall_fin_two.2 ⟨by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
          Matrix.cons_val_zero]
        rw [← (hc 0).1, hae]; ring, by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
          Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← (hc 0).2, hae]; ring⟩)
  -- 3. The polynomial core.
  exact key hhg hcl fun j => ⟨(hc j).1 ▸ ha 0 j, (hc j).2 ▸ ha 1 j⟩

#print axioms solution
