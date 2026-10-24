-- Prove2me | solution 1 for DiazModulus.degree_one_multiplier_space_visible_or_degree_one_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:25:05.451041+00:00
-- url     : https://prove2.me/submissions/3ea1b5b3-6765-4454-8fc0-b2766beaedd2

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A five-dimensional space with three independent `u`-multipliers is visible or `W_g`

Let `H₀ = ⟨1, u, u⁻¹⟩` (dimension 3, `u` being transcendental) and
`N = {f ∈ W : u f ∈ W}`, a `Q̄`-subspace containing the three independent `tⱼ`.
(→) If every `tⱼ` lies in `H₀`, their span is `H₀`, so `u ∈ N` and `u² ∈ W`. Otherwise take
`g = tⱼ ∉ H₀`. If `(u − c) g ∈ H₀` for some `c ∈ Q̄`, write `(u − c) g = α + βu + γu⁻¹`:
for `c = 0`, `γ ≠ 0` (else `g ∈ H₀`) and `u⁻² = γ⁻¹(g − β − αu⁻¹) ∈ W`; for `c ≠ 0`, with
`r = α + βc + γ/c` one has `(u − c)(g − β + (γ/c)u⁻¹) = r`, so `r ≠ 0` (else `g ∈ H₀`) and
`(u − c)⁻¹ ∈ W`. If no such `c` exists, `1, u, u⁻¹, g, ug` are free (a relation with a `ug`
or `g` coefficient would put `(u − c) g` or `g` in `H₀`), and their span is `W` by dimension.
(←) Take `t = (1, u, u⁻¹)`, `(1, u⁻¹, u⁻²)`, `(1, u⁻¹, (u − a)⁻¹)` (using
`u (u − a)⁻¹ = 1 + a (u − a)⁻¹`) or `(1, u⁻¹, g)`; independence comes from the transcendence
of `u` (a vanishing polynomial of degree ≤ 2) or from that of `1, u, u⁻¹, g, ug`. -/

namespace R20_deg1

open DiazModulus Polynomial

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem quad_zero {u : ℂ} (hu : u ∉ Qbar) (a₀ a₁ a₂ : ↥Qbar)
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 = 0) : a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2)
    (by simpa [show ∀ x : ↥Qbar, algebraMap (↥Qbar) ℂ x = x from fun _ => rfl] using h)
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (coeff · 0) hP
  · simpa using congrArg (coeff · 1) hP
  · simpa using congrArg (coeff · 2) hP

theorem ne0 {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

theorem h0_zero {u : ℂ} (hu : u ∉ Qbar) (a b c : ↥Qbar)
    (h : (a : ℂ) + b * u + c * u⁻¹ = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ (ne0 hu)
  obtain ⟨h1, h2, h3⟩ := quad_zero hu c a b (by linear_combination u * h - (c : ℂ) * hu')
  exact ⟨h2, h3, h1⟩

theorem smem (W : Submodule (↥Qbar) ℂ) {k v : ℂ} (hk : k ∈ Qbar) (hv : v ∈ W) : k * v ∈ W :=
  W.smul_mem (⟨k, hk⟩ : ↥Qbar) hv

theorem li3 (v : Fin 3 → ℂ)
    (h : ∀ a b c : ↥Qbar, (a : ℂ) * v 0 + b * v 1 + c * v 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    LinearIndependent (↥Qbar) v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul] at hg
  obtain ⟨h0, h1, h2⟩ := h _ _ _ hg
  intro i; fin_cases i <;> assumption

theorem li5 (v : Fin 5 → ℂ)
    (h : ∀ a b c d e : ↥Qbar, (a : ℂ) * v 0 + b * v 1 + c * v 2 + d * v 3 + e * v 4 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) : LinearIndependent (↥Qbar) v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_five, Subfield.smul_def, smul_eq_mul] at hg
  obtain ⟨h0, h1, h2, h3, h4⟩ := h _ _ _ _ _ hg
  intro i; fin_cases i <;> assumption

theorem li5_use {v : Fin 5 → ℂ} (hv : LinearIndependent (↥Qbar) v) (a b c d e : ↥Qbar)
    (h : (a : ℂ) * v 0 + b * v 1 + c * v 2 + d * v 3 + e * v 4 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have := Fintype.linearIndependent_iff.1 hv ![a, b, c, d, e]
    (by simpa [Fin.sum_univ_five, Subfield.smul_def] using h)
  exact ⟨this 0, this 1, this 2, this 3, this 4⟩

/-- A pole: `F ∈ W \ H₀` with `(u − c) F ∈ H₀` puts `u⁻²` or some `(u − c)⁻¹` in `W`. -/
theorem pole {u : ℂ} (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) (h1 : (1 : ℂ) ∈ W)
    (hui : u⁻¹ ∈ W) (F : ℂ) (hF : F ∈ W) (hFH : ∀ a b c : ↥Qbar, F ≠ a + b * u + c * u⁻¹)
    (c a b d : ↥Qbar) (e : (u - c) * F = a + b * u + d * u⁻¹) :
    (u ^ 2)⁻¹ ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W := by
  have hu0 := ne0 hu
  have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  by_cases hc : c = 0
  · left
    rw [hc, ZeroMemClass.coe_zero, sub_zero] at e
    have hF' : F = (a + b * u + d * u⁻¹) / u := by rw [← e]; field_simp
    have hd : d ≠ 0 := by
      rintro rfl
      apply hFH b 0 a
      rw [hF']; push_cast; field_simp; ring
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    have : (u ^ 2)⁻¹ = (d : ℂ)⁻¹ * F + (-((d : ℂ)⁻¹ * b)) * 1 + (-((d : ℂ)⁻¹ * a)) * u⁻¹ := by
      rw [hF']; field_simp; ring
    rw [this]
    exact add_mem (add_mem (smem W (inv_mem d.2) hF)
      (smem W (neg_mem (mul_mem (inv_mem d.2) b.2)) h1))
      (smem W (neg_mem (mul_mem (inv_mem d.2) a.2)) hui)
  · right
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hci : (c : ℂ) * (c : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hc'
    have huc : u - c ≠ 0 := sub_ne_zero.2 (fun h => hu (h ▸ c.2))
    set r : ℂ := a + b * c + d / c with hr
    have hrQ : r ∈ Qbar := add_mem (add_mem a.2 (mul_mem b.2 c.2)) (div_mem d.2 c.2)
    have key : (u - c) * (F - b + (d / c) * u⁻¹) = r := by
      rw [hr]
      linear_combination e + (d : ℂ) * (c : ℂ)⁻¹ * hu' - (d : ℂ) * u⁻¹ * hci
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0] at key
      have := (mul_eq_zero.1 key).resolve_left huc
      apply hFH b 0 ⟨-(d / c), neg_mem (div_mem d.2 c.2)⟩
      push_cast
      linear_combination this
    refine ⟨c, c.2, hc', ?_⟩
    have : (u - c)⁻¹ = r⁻¹ * F + (-(r⁻¹ * b)) * 1 + (r⁻¹ * (d / c)) * u⁻¹ := by
      have : (u - c)⁻¹ = (F - b + (d / c) * u⁻¹) / r := by
        rw [eq_div_iff hr0, ← key, inv_mul_cancel_left₀ huc]
      rw [this]; ring
    rw [this]
    exact add_mem (add_mem (smem W (inv_mem hrQ) hF)
      (smem W (neg_mem (mul_mem (inv_mem hrQ) b.2)) h1))
      (smem W (mul_mem (inv_mem hrQ) (div_mem d.2 c.2)) hui)

end R20_deg1

open DiazModulus R20_deg1 in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W) :
    (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ↔ (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ (∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) ∨
      ∃ g : ℂ, LinearIndependent (↥Qbar) ![1, u, u⁻¹, g, u * g] ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, g, u * g} : Set ℂ)) := by
  have hu0 := ne0 hu
  have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  constructor
  · rintro ⟨t, ht, htW⟩
    set H := Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, u⁻¹]) with hH
    have hHli : LinearIndependent (↥Qbar) ![(1 : ℂ), u, u⁻¹] :=
      li3 _ (fun a b c h => h0_zero hu a b c (by simpa using h))
    have : FiniteDimensional (↥Qbar) H := FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have hfH : Module.finrank (↥Qbar) H = 3 := by rw [hH, finrank_span_eq_card hHli]; simp
    have hHmem : ∀ a b c : ↥Qbar, (a : ℂ) + b * u + c * u⁻¹ ∈ H := by
      intro a b c
      have e0 : (1 : ℂ) ∈ H := Submodule.subset_span ⟨0, rfl⟩
      have e1 : u ∈ H := Submodule.subset_span ⟨1, rfl⟩
      have e2 : u⁻¹ ∈ H := Submodule.subset_span ⟨2, rfl⟩
      have := add_mem (add_mem (smem H a.2 e0) (smem H b.2 e1)) (smem H c.2 e2)
      simpa using this
    let N : Submodule (↥Qbar) ℂ := W ⊓ W.comap (LinearMap.mulLeft (↥Qbar) u)
    have hN : ∀ f, f ∈ N ↔ f ∈ W ∧ u * f ∈ W := fun f => by simp [N]
    have hSN : Submodule.span (↥Qbar) (Set.range t) ≤ N :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hN _).2 (htW j))
    by_cases hall : ∀ j, t j ∈ H
    · left
      have hSH : Submodule.span (↥Qbar) (Set.range t) ≤ H :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hall j)
      have heq := Submodule.eq_of_le_of_finrank_eq hSH (by rw [finrank_span_eq_card ht, hfH]; simp)
      have huN : u ∈ N := hSN (heq ▸ (Submodule.subset_span ⟨1, rfl⟩ : u ∈ H))
      rw [sq]; exact ((hN u).1 huN).2
    push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hgW := (htW j).1
    have hugW := (htW j).2
    set g := t j
    have hgH : ∀ a b c : ↥Qbar, g ≠ a + b * u + c * u⁻¹ := fun a b c e => hj (e ▸ hHmem a b c)
    by_cases hc : ∃ c a b d : ↥Qbar, (u - c) * g = a + b * u + d * u⁻¹
    · obtain ⟨c, a, b, d, e⟩ := hc
      rcases pole hu W h1 hui g hgW hgH c a b d e with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    push Not at hc
    right; right; right
    have hli : LinearIndependent (↥Qbar) ![1, u, u⁻¹, g, u * g] := by
      apply li5
      intro a b c d e h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        mul_one] at h
      by_cases he : e = 0
      · by_cases hd : d = 0
        · rw [he, hd] at h
          obtain ⟨x, y, z⟩ := h0_zero hu a b c (by simpa using h)
          exact ⟨x, y, z, hd, he⟩
        · exfalso
          have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
          have hdi : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd'
          simp only [he, ZeroMemClass.coe_zero, zero_mul, add_zero] at h
          apply hgH (-(a / d)) (-(b / d)) (-(c / d))
          push_cast
          linear_combination (d : ℂ)⁻¹ * h - g * hdi
      · exfalso
        have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
        have hei : (e : ℂ) * (e : ℂ)⁻¹ = 1 := mul_inv_cancel₀ he'
        apply hc (-(d / e)) (-(a / e)) (-(b / e)) (-(c / e))
        push_cast
        linear_combination (e : ℂ)⁻¹ * h - u * g * hei
    refine ⟨g, hli, ?_⟩
    have hr : Set.range ![(1 : ℂ), u, u⁻¹, g, u * g] = {1, u, u⁻¹, g, u * g} := by
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · refine Submodule.span_le.2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      exacts [h1, hu1, hui, hgW, hugW]
    · rw [hW, ← hr, finrank_span_eq_card hli]; simp
  · rintro (h | h | ⟨a, ha, ha0, h⟩ | ⟨g, hli, hWg⟩)
    · refine ⟨![1, u, u⁻¹], li3 _ (fun a b c e => h0_zero hu a b c (by simpa using e)), ?_⟩
      intro j; fin_cases j
      · exact ⟨h1, by simpa using hu1⟩
      · exact ⟨hu1, by simpa [sq] using h⟩
      · exact ⟨hui, by simpa [hu'] using h1⟩
    · refine ⟨![1, u⁻¹, (u ^ 2)⁻¹], li3 _ (fun a b c e => ?_), ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one] at e
        obtain ⟨x, y, z⟩ := quad_zero hu c b a (by
          have : u ^ 2 * ((a : ℂ) + b * u⁻¹ + c * (u ^ 2)⁻¹) = 0 := by rw [e, mul_zero]
          rw [← this]; field_simp; ring)
        exact ⟨z, y, x⟩
      · intro j; fin_cases j
        · exact ⟨h1, by simpa using hu1⟩
        · exact ⟨hui, by simpa [hu'] using h1⟩
        · refine ⟨h, ?_⟩
          have : u * (u ^ 2)⁻¹ = u⁻¹ := by field_simp
          simpa [this] using hui
    · have hua : u - a ≠ 0 := sub_ne_zero.2 (fun e => hu (e ▸ ha))
      set a' : ↥Qbar := ⟨a, ha⟩
      have ha' : (a' : ℂ) = a := rfl
      refine ⟨![1, u⁻¹, (u - a)⁻¹], li3 _ (fun x y z e => ?_), ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one] at e
        obtain ⟨p, q, r⟩ := quad_zero hu (-(y * a')) (y + z - x * a') x (by
          have : u * (u - a) * ((x : ℂ) + y * u⁻¹ + z * (u - a)⁻¹) = 0 := by rw [e, mul_zero]
          rw [← this]; push_cast; rw [ha']; field_simp; ring)
        have hy : y = 0 := by
          have : y * a' = 0 := neg_eq_zero.1 p
          exact (mul_eq_zero.1 this).resolve_right (fun h0 => ha0 (by rw [← ha', h0]; rfl))
        refine ⟨r, hy, ?_⟩
        rw [hy, r] at q; simpa using q
      · intro j; fin_cases j
        · exact ⟨h1, by simpa using hu1⟩
        · exact ⟨hui, by simpa [hu'] using h1⟩
        · refine ⟨h, ?_⟩
          have : u * (u - a)⁻¹ = 1 + a * (u - a)⁻¹ := by field_simp; ring
          simpa [this] using add_mem h1 (smem W ha h)
    · have hm : ∀ x ∈ ({1, u, u⁻¹, g, u * g} : Set ℂ), x ∈ W := fun x hx =>
        hWg ▸ Submodule.subset_span hx
      refine ⟨![1, u⁻¹, g], li3 _ (fun a b c e => ?_), ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one] at e
        obtain ⟨x, -, y, z, -⟩ := li5_use hli a 0 b c 0 (by simpa using e)
        exact ⟨x, y, z⟩
      · intro j; fin_cases j
        · exact ⟨h1, by simpa using hu1⟩
        · exact ⟨hui, by simpa [hu'] using h1⟩
        · exact ⟨hm g (by simp), hm (u * g) (by simp)⟩
