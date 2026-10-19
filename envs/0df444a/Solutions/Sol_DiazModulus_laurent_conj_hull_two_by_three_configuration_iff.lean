-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_two_by_three_configuration_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:32:39.764498+00:00
-- url     : https://prove2.me/submissions/78dba4e0-7b90-40c9-b493-dfacf8623d66

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_involution_space_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_laurent_real_pencil_normal_form_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_laurent_conj_hull_with_polynomial_part_configuration_class
import Theorems.Thm_DiazModulus_laurent_conj_hull_finrank_le_four_no_two_by_three_configuration
import Theorems.Thm_DiazModulus_laurent_conj_hull_without_polynomial_part_configuration_classes
import Theorems.Thm_DiazModulus_polynomial_hull_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # Theorem E: the configurations of the conjugation hull of a polynomial in `u` and `ū`

Let `u ∉ Q̄`, `s ∈ Q̄` with `s² = u ū`, and `z = Σ_{|j| ≤ k} c_j (u/s)^j` with `c_j ∈ Q̄`. Then
`W = span_Q̄ {1, u, ū, z, z̄}` carries a `2 × 3` configuration iff `dim W = 5` and `W` is in the
polynomial class (P), the involution class (Q) or the real pencil class (R).

`s` is real (`s s̄ ≥ 0 < u ū` rules out `s̄ = −s`), so `v = u/s` has `v v̄ = 1`, `v ∉ Q̄`, and
`span {1, u, ū, A, B} = span {1, v, v̄, A, B}` for all `A, B`; this moves every node between `u`
and `v`. "Only if": a configuration forces `dim W > 4` by
`laurent_conj_hull_finrank_le_four_no_two_by_three_configuration`, and `dim W ≤ 5` by counting
generators. If `W` contains some `v² P(v)` with `P ≠ 0`,
`laurent_conj_hull_with_polynomial_part_configuration_class` gives `α v² + β v³ ∈ W`, which is (P)
after rescaling by `s²`, `s³`; otherwise `laurent_conj_hull_without_polynomial_part_configuration_classes`
gives (Q) or (R). "If": in class (P), `W` is conjugation-stable, so it contains the hull of
`P(u) = α u² + β u³`, which carries a configuration by Theorem C
(`polynomial_hull_two_by_three_configuration_iff`, degree 2 or 3); classes (Q) and (R) carry the
configurations of `laurent_involution_space_carries_two_by_three_configuration` and
`laurent_real_pencil_normal_form_carries_two_by_three_configuration`. -/

namespace R18_E

open DiazModulus Polynomial

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  have : (conj a : ℂ) = ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ) a := rfl
  rw [this, Polynomial.aeval_algHom_apply, hp, map_zero]

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

/-- `span {1, u, ū, z, z̄}` is conjugation-stable. -/
theorem hull_conj_stable (u z : ℂ) :
    ∀ w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ),
      conj w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  refine span_conj_stable fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    exact Submodule.subset_span (by simp)

/-- `s` is real and non-zero. -/
theorem s_facts {u s : ℂ} (hu : u ∉ Qbar) (hss : s * s = u * conj u) : s ≠ 0 ∧ conj s = s := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [Complex.mul_conj, zero_mul, eq_comm, Complex.ofReal_eq_zero] at hss
    linarith
  · have h1 : conj s * conj s = s * s := by
      rw [← map_mul, hss, map_mul, Complex.conj_conj, mul_comm]
    have h2 : (conj s - s) * (conj s + s) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      have h3 : s * conj s = -(u * conj u) := by linear_combination s * h - hss
      rw [Complex.mul_conj, Complex.mul_conj] at h3
      have h4 := congrArg Complex.re h3
      simp only [Complex.ofReal_re, Complex.neg_re] at h4
      linarith [Complex.normSq_nonneg s]

/-- `span {1, u, ū, A, B} = span {1, u/s, conj (u/s), A, B}`. -/
theorem span_swap {u s : ℂ} (hs : s ∈ Qbar) (hs0 : s ≠ 0) (hsr : conj s = s) (A B : ℂ) :
    Submodule.span Qbar ({1, u, conj u, A, B} : Set ℂ) =
      Submodule.span Qbar ({1, u / s, conj (u / s), A, B} : Set ℂ) := by
  have hcv : conj (u / s) = s⁻¹ * conj u := by rw [map_div₀, hsr, div_eq_inv_mul]
  have hsi : s⁻¹ ∈ Qbar := inv_mem hs
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨Submodule.subset_span (by simp), ?_, ?_, Submodule.subset_span (by simp),
      Submodule.subset_span (by simp)⟩
    · exact span_mem_of_eq (by field_simp)
        (span_mul_mem hs (Submodule.subset_span (by simp) : u / s ∈ _))
    · exact span_mem_of_eq (by rw [hcv]; field_simp)
        (span_mul_mem hs (Submodule.subset_span (by simp) : conj (u / s) ∈ _))
  · refine Submodule.span_le.2 ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨Submodule.subset_span (by simp), ?_, ?_, Submodule.subset_span (by simp),
      Submodule.subset_span (by simp)⟩
    · exact span_mem_of_eq (div_eq_inv_mul u s)
        (span_mul_mem hsi (Submodule.subset_span (by simp) : u ∈ _))
    · exact span_mem_of_eq hcv (span_mul_mem hsi (Submodule.subset_span (by simp) : conj u ∈ _))

theorem finrank_le_five (a b c d e : ℂ) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({a, b, c, d, e} : Set ℂ)) ≤ 5 := by
  classical
  have h := finrank_span_finset_le_card (R := ↥Qbar) ({a, b, c, d, e} : Finset ℂ)
  simp only [Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans Finset.card_le_five

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- `α X² + β X³` with `(α, β) ≠ 0` has degree 2 or 3. -/
theorem natDegree_two_three {a b : ↥Qbar} (h : a ≠ 0 ∨ b ≠ 0) :
    (C a * X ^ 2 + C b * X ^ 3).natDegree = 2 ∨ (C a * X ^ 2 + C b * X ^ 3).natDegree = 3 := by
  by_cases hb : b = 0
  · left
    rw [hb, map_zero, zero_mul, add_zero]
    exact natDegree_C_mul_X_pow 2 a (h.resolve_right (not_not.2 hb))
  · right
    rw [natDegree_add_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow 3 b hb]
    exact (natDegree_C_mul_X_pow_le a 2).trans_lt (by norm_num)

end R18_E

open DiazModulus R18_E in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ↔
      (Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) = 5 ∧
      ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ)))) := by
  obtain ⟨hs0, hsr⟩ := s_facts hu hss
  have hv : u / s ∉ Qbar := fun h => hu (by
    have := mul_mem hs h
    rwa [mul_div_cancel₀ u hs0] at this)
  have hv1 : u / s * conj (u / s) = 1 := by
    rw [map_div₀, hsr, div_mul_div_comm, ← hss, div_self (mul_ne_zero hs0 hs0)]
  set z := ∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j with hz
  have hW := span_swap (u := u) hs hs0 hsr z (conj z)
  constructor
  · intro hconf
    rw [hW] at hconf
    have h5 : Module.finrank (↥Qbar)
        (Submodule.span Qbar ({1, u / s, conj (u / s), z, conj z} : Set ℂ)) = 5 := by
      refine le_antisymm (finrank_le_five _ _ _ _ _) ?_
      by_contra h4
      exact laurent_conj_hull_finrank_le_four_no_two_by_three_configuration (u / s) hv hv1 k c hc
        (Nat.le_of_lt_succ (not_le.1 h4)) hconf
    rw [hW]
    refine ⟨h5, ?_⟩
    simp only [span_swap (u := u) hs hs0 hsr]
    by_cases hB : ∀ P : Polynomial ↥Qbar, (u / s) ^ 2 * Polynomial.aeval (u / s) P ∈
        Submodule.span Qbar ({1, u / s, conj (u / s), z, conj z} : Set ℂ) → P = 0
    · exact Or.inr (laurent_conj_hull_without_polynomial_part_configuration_classes (u / s) hv hv1
        k c hc h5 hB hconf)
    · push Not at hB
      obtain ⟨P, hPW, hP⟩ := hB
      obtain ⟨α, β, hα, hβ, hne, hm⟩ :=
        laurent_conj_hull_with_polynomial_part_configuration_class (u / s) hv hv1 z P hP hPW hconf
      refine Or.inl ⟨α / s ^ 2, β / s ^ 3, div_mem hα (pow_mem hs 2), div_mem hβ (pow_mem hs 3),
        hne.imp (fun h => div_ne_zero h (pow_ne_zero 2 hs0))
          (fun h => div_ne_zero h (pow_ne_zero 3 hs0)), span_mem_of_eq ?_ hm⟩
      field_simp
  · rintro ⟨-, hP | hQ | hR⟩
    · obtain ⟨α, β, hα, hβ, hne, hm⟩ := hP
      set P : Polynomial ↥Qbar := Polynomial.C (⟨α, hα⟩ : ↥Qbar) * Polynomial.X ^ 2 +
        Polynomial.C (⟨β, hβ⟩ : ↥Qbar) * Polynomial.X ^ 3
      have hPu : Polynomial.aeval u P = α * u ^ 2 + β * u ^ 3 := by
        simp only [P, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, am]
      have hρ : IsAlgebraic ℚ (u * conj u) := mem_Qbar_iff.1 (hss ▸ mul_mem hs hs)
      have hdeg : P.natDegree = 2 ∨ P.natDegree = 3 :=
        natDegree_two_three (hne.imp (fun h h0 => h (congrArg Subtype.val h0))
          (fun h h0 => h (congrArg Subtype.val h0)))
      obtain ⟨x, y, hx, hy, hxy⟩ :=
        (polynomial_hull_two_by_three_configuration_iff hu hρ P).2 hdeg
      have hle : Submodule.span Qbar ({1, u, conj u, Polynomial.aeval u P,
          conj (Polynomial.aeval u P)} : Set ℂ) ≤
          Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
        refine Submodule.span_le.2 ?_
        simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
        rw [hPu]
        exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
          Submodule.subset_span (by simp), hm, hull_conj_stable u z _ hm⟩
      exact ⟨x, y, hx, hy, fun i j => hle (hxy i j)⟩
    · obtain ⟨e, β, ζ, he, hβ, hζ, -, -, -, hWQ⟩ := hQ
      rw [hWQ, span_swap (u := u) hs hs0 hsr]
      obtain ⟨hx, hy, hxy⟩ :=
        laurent_involution_space_carries_two_by_three_configuration (u / s) hv hv1 e β ζ he hβ hζ
      exact ⟨_, _, hx, hy, hxy⟩
    · obtain ⟨κ, hκ, hκ1, G, -, hG, hWR⟩ := hR
      rw [hWR, span_swap (u := u) hs hs0 hsr]
      obtain ⟨hx, hy, hxy⟩ :=
        laurent_real_pencil_normal_form_carries_two_by_three_configuration (u / s) hv hv1 κ hκ hκ1 G
          (by omega)
      exact ⟨_, _, hx, hy, hxy⟩
