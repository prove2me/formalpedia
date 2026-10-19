-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_large_exponent_configuration_iff_real_pencil_class
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:29:58.04967+00:00
-- url     : https://prove2.me/submissions/d739b803-6df7-4f0e-9592-a9e794cdc879

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_conj_hull_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_laurent_conj_hull_class_finrank_eq_five

open Complex ComplexConjugate

/-! # Corollary E(a): with an exponent of size at least four, only the real pencil class carries

Let `u ∉ Q̄`, `s ∈ Q̄` with `s² = u ū`, `z = Σ_{|j| ≤ k} c_j (u/s)^j` (`c_j ∈ Q̄`) with some `c_j ≠ 0`,
`|j| ≥ 4`. Then `W = span_Q̄ {1, u, ū, z, z̄}` carries a `2 × 3` configuration iff `W` is in class (R).
"If": (R) gives `dim W = 5` (`laurent_conj_hull_class_finrank_eq_five`), and Theorem E
(`laurent_conj_hull_two_by_three_configuration_iff`) gives the configuration. "Only if": Theorem E
gives `dim W = 5` and (P), (Q) or (R). In (Q), `z ∈ W` lies in the window `span(v^{-3}, …, v^3)`,
`v = u/s` (`v̄ = v⁻¹`, `v` transcendental). In (P), `m = α u² + β u³ ∈ W` is itself a Laurent
polynomial of class (P), so its hull `span {1, u, ū, m, m̄} ≤ W` is five-dimensional by the same node,
hence equal to `W`, and again `z` lies in the window. Clearing by `v^k` and comparing coefficients
of `Σ c_j X^{j+k}` gives `c_j = 0` for `|j| ≥ 4` (`window`), a contradiction. -/

namespace R18_Ea

open DiazModulus Polynomial

theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  have : (conj a : ℂ) = ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) a := rfl
  rw [this, Polynomial.aeval_algHom_apply, hp, map_zero]

/-- Conjugation on `Q̄`. -/
def cjQ (a : ↥Qbar) : ↥Qbar := ⟨conj (a : ℂ), conj_mem_Qbar a.2⟩

theorem cjQ_coe (a : ↥Qbar) : (cjQ a : ℂ) = conj (a : ℂ) := rfl

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) : P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

/-- `s` is real and non-zero. -/
theorem s_facts {u s : ℂ} (hu : u ∉ Qbar) (hss : s * s = u * conj u) : s ≠ 0 ∧ conj s = s := by
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.2 fun h => hu (h ▸ zero_mem _)
  rw [Complex.mul_conj] at hss
  have h1 := congrArg Complex.im hss
  have h2 := congrArg Complex.re hss
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re] at h1 h2
  have him : s.im = 0 := by
    rcases mul_eq_zero.1 (show s.re * s.im = 0 by linarith) with h | h
    · rw [h] at h2; nlinarith [sq_nonneg s.im]
    · exact h
  exact ⟨fun h0 => by simp [h0] at h2; linarith, Complex.ext (by simp) (by simp [him])⟩

/-- `span {1, u, ū, z, z̄}` is conjugation-stable. -/
theorem hull_conj_stable (u z : ℂ) :
    ∀ w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ),
      conj w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Submodule.subset_span (by simp)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [show conj (c • x) = cjQ c • conj x from map_mul conj (c : ℂ) x]
    exact Submodule.smul_mem _ _ hx

theorem coeffs {u z zc t w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-- `P = Σ_{|j| ≤ k} γ_j X^{j+k}`, so that `P(x) = x^k Σ γ_j x^j`. -/
noncomputable def lpoly (k : ℕ) (γ : ℤ → ↥Qbar) : (↥Qbar)[X] :=
  ∑ j ∈ Finset.Icc (-(k : ℤ)) k, C (γ j) * X ^ (j + k).toNat

theorem lpoly_aeval (k : ℕ) (γ : ℤ → ↥Qbar) {x : ℂ} (hx : x ≠ 0) :
    aeval x (lpoly k γ) = x ^ k * ∑ j ∈ Finset.Icc (-(k : ℤ)) k, (γ j : ℂ) * x ^ j := by
  simp only [lpoly, map_sum, map_mul, aeval_C, aeval_X_pow, am, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : 0 ≤ j + k := by simp only [Finset.mem_Icc] at hj; omega
  rw [← zpow_natCast x (j + k).toNat, Int.toNat_of_nonneg hj', zpow_add₀ hx, zpow_natCast]
  ring

/-- If `v³ z` is a polynomial of degree at most `6` in `v`, every `c_j` with `|j| ≥ 4` vanishes. -/
theorem window {v : ℂ} (hv : v ∉ Qbar) (hv0 : v ≠ 0) (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    {j₀ : ℤ} (hj : j₀ ∈ Finset.Icc (-(k : ℤ)) k) (h4 : 4 ≤ |j₀|) {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ↥Qbar}
    (hz : v ^ 3 * ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j =
      a₀ + a₁ * v + a₂ * v ^ 2 + a₃ * v ^ 3 + a₄ * v ^ 4 + a₅ * v ^ 5 + a₆ * v ^ 6) :
    c j₀ = 0 := by
  have hj' := Finset.mem_Icc.1 hj
  have hab : 4 ≤ j₀ ∨ j₀ ≤ -4 := by
    rcases abs_cases j₀ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at h4 <;> omega
  have hk : 3 ≤ k := by omega
  set Q : (↥Qbar)[X] := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 + C a₄ * X ^ 4 +
    C a₅ * X ^ 5 + C a₆ * X ^ 6 with hQ
  have hQd : Q.natDegree ≤ 6 := by rw [hQ]; compute_degree
  have hP : lpoly k (fun j => ⟨c j, hc j⟩) = X ^ (k - 3) * Q := by
    apply sub_eq_zero.1
    apply aeval_eq_zero hv
    rw [map_sub, lpoly_aeval k _ hv0, map_mul, map_pow, aeval_X]
    simp only [hQ, map_add, map_mul, map_pow, aeval_C, aeval_X, am]
    rw [show v ^ k = v ^ (k - 3) * v ^ 3 by rw [← pow_add, Nat.sub_add_cancel hk]]
    linear_combination v ^ (k - 3) * hz
  have h1 := congrArg (coeff · (j₀ + k).toNat) hP
  simp only [lpoly, finsetSum_coeff, coeff_C_mul_X_pow, coeff_X_pow_mul'] at h1
  rw [Finset.sum_eq_single j₀ (fun j hj hne => if_neg (by simp only [Finset.mem_Icc] at hj; omega))
    (fun h => absurd hj h), if_pos rfl] at h1
  split_ifs at h1 with hle
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)] at h1
    exact congrArg Subtype.val h1
  · exact congrArg Subtype.val h1

end R18_Ea

open DiazModulus R18_Ea in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (hbig : ∃ j ∈ Finset.Icc (-(k : ℤ)) k, 4 ≤ |j| ∧ c j ≠ 0) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ↔
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ)) := by
  rw [laurent_conj_hull_two_by_three_configuration_iff u s hu hs hss k c hc]
  refine ⟨fun ⟨h5, hcl⟩ => ?_, fun hR => ⟨laurent_conj_hull_class_finrank_eq_five u s hu hs hss k c
    (Or.inr (Or.inr hR)), Or.inr (Or.inr hR)⟩⟩
  obtain ⟨hs0, hsr⟩ := s_facts hu hss
  have hu0 : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
  obtain ⟨j₀, hj, h4, hcj⟩ := hbig
  lift s to ↥Qbar using hs
  have hcv0 : conj (u / s) = (u / s)⁻¹ := by
    rw [map_div₀, hsr, inv_div, div_eq_div_iff hs0 hu0]
    linear_combination -hss
  have hv : u / s ∉ Qbar := fun h => hu (by
    have := mul_mem s.2 h
    rwa [mul_div_cancel₀ u hs0] at this)
  have hv0 : u / s ≠ 0 := div_ne_zero hu0 hs0
  have hcu' : conj u = s * (u / s)⁻¹ := by
    rw [inv_div, ← mul_div_assoc, eq_div_iff hu0]
    linear_combination -hss
  set z := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j with hz
  rcases hcl with ⟨α, β, hα, hβ, hne, hm⟩ | ⟨e, b, ζ, he, hb, hζ, -, -, -, hWQ⟩ | hR
  · exfalso
    lift α to ↥Qbar using hα
    lift β to ↥Qbar using hβ
    obtain ⟨c', hc'⟩ : ∃ c' : ℤ → ℂ, c' = fun j => if j = 2 then (α : ℂ) * s ^ 2
      else if j = 3 then (β : ℂ) * s ^ 3 else 0 := ⟨_, rfl⟩
    have hsum : ∑ j ∈ Finset.Icc (-((3 : ℕ) : ℤ)) ((3 : ℕ) : ℤ), c' j * (u / s) ^ j =
        (α : ℂ) * u ^ 2 + β * u ^ 3 := by
      rw [Finset.sum_eq_add_of_mem 2 3 (by simp) (by simp) (by norm_num)
        (fun j _ hj => by simp [hc', hj.1, hj.2])]
      simp only [hc']
      norm_num
      field_simp
    have hP5 := laurent_conj_hull_class_finrank_eq_five u s hu s.2 hss 3 c'
      (Or.inl ⟨α, β, α.2, β.2, hne, by rw [hsum]; exact Submodule.subset_span (by simp)⟩)
    rw [hsum] at hP5
    have hPle : Submodule.span Qbar ({1, u, conj u, (α : ℂ) * u ^ 2 + β * u ^ 3,
        conj ((α : ℂ) * u ^ 2 + β * u ^ 3)} : Set ℂ) ≤
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
      refine Submodule.span_le.2 ?_
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
        Submodule.subset_span (by simp), hm, hull_conj_stable u z _ hm⟩
    have : FiniteDimensional (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) :=
      FiniteDimensional.span_of_finite _ (Set.toFinite _)
    have heq := Submodule.eq_of_le_of_finrank_eq hPle (hP5.trans h5.symm)
    have hzm : z ∈ Submodule.span Qbar ({1, u, conj u, (α : ℂ) * u ^ 2 + β * u ^ 3,
        conj ((α : ℂ) * u ^ 2 + β * u ^ 3)} : Set ℂ) := heq ▸ Submodule.subset_span (by simp)
    obtain ⟨c₁, c₂, c₃, c₄, c₅, hzc⟩ := coeffs hzm
    refine hcj (window hv hv0 k c hc hj h4 (a₀ := c₅ * cjQ β * s ^ 3) (a₁ := c₅ * cjQ α * s ^ 2)
      (a₂ := c₃ * s) (a₃ := c₁) (a₄ := c₂ * s) (a₅ := c₄ * α * s ^ 2) (a₆ := c₄ * β * s ^ 3) ?_)
    rw [← hz, hzc]
    simp only [map_add, map_mul, map_pow]
    rw [hcu']
    push_cast
    simp only [cjQ_coe]
    field_simp
    ring
  · exfalso
    have hzq : z ∈ Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2,
        b * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ) :=
      hWQ ▸ Submodule.subset_span (by simp)
    lift e to ↥Qbar using he
    lift b to ↥Qbar using hb
    lift ζ to ↥Qbar using hζ
    obtain ⟨c₁, c₂, c₃, c₄, c₅, hzc⟩ := coeffs hzq
    refine hcj (window hv hv0 k c hc hj h4 (a₀ := c₅ * b) (a₁ := c₄) (a₂ := c₃ * s) (a₃ := c₁)
      (a₄ := c₂ * s) (a₅ := c₄ * e + c₅ * ζ) (a₆ := c₅ * e) ?_)
    rw [← hz, hzc, hcu', hcv0]
    push_cast
    field_simp
    ring
  · exact hR
