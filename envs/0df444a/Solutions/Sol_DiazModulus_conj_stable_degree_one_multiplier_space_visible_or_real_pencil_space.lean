-- Prove2me | solution 1 for DiazModulus.conj_stable_degree_one_multiplier_space_visible_or_real_pencil_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:21:49.261378+00:00
-- url     : https://prove2.me/submissions/5f97e79e-0804-4356-9e9c-9899b583f66d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_degree_one_multiplier_space_visible_or_degree_one_space
import Theorems.Thm_DiazModulus_conj_equivariant_degree_one_space_eq_real_pencil_space

open Complex ComplexConjugate

/-! # A conjugation-stable space with three `u`-multipliers is visible or a real pencil space

Since `s² = u ū` with `s ≠ 0`, `ū = s² u⁻¹`, so `u⁻² ∈ W ⟺ ū² ∈ W`. If `W` is visible we are
done. Otherwise `degree_one_multiplier_space_visible_or_degree_one_space` gives `g` with
`1, u, u⁻¹, g, ug` free and spanning `W`. Then `Z = {h ∈ W : u h ∈ W}` is `⟨1, u⁻¹, g⟩`: for
`h = a₀ + a₁u + a₂u⁻¹ + a₃g + a₄ug ∈ Z`, `a₁u² + a₄u²g ∈ W`; `a₄ = 0` forces `a₁ = 0`
(`u² ∉ W`); if `a₄ ≠ 0`, write `u²(g + b) = b₀ + b₁u + b₂u⁻¹ + b₃g + b₄ug` and take a root
`c ∈ Q̄` of `X² − b₄X − b₃` (a square root of the discriminant is algebraic); then
`F = (c − b₄) g + ug + bu ∈ W \ H₀` (an eigenvector of `u` on `W/H₀`) has
`(u − c) F ∈ H₀`, which puts `u⁻²` or `(u − c)⁻¹` in `W`, a contradiction. Conjugation maps
`Z` onto `uZ`: `h = u⁻¹ ḡ = s⁻² conj(ug) ∈ W` and `u h = ḡ ∈ W`, so `ḡ ∈ u⟨1, u⁻¹, g⟩ =
⟨1, u, ug⟩`. Finally `1, u, ū, g, ug` are free, their span is `W` by dimension, and
`conj_equivariant_degree_one_space_eq_real_pencil_space` (10.43) gives `λ` and `f`. -/

namespace R20_deg1c

open DiazModulus

theorem ne0 {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

theorem smem (W : Submodule (↥Qbar) ℂ) {k v : ℂ} (hk : k ∈ Qbar) (hv : v ∈ W) : k * v ∈ W :=
  W.smul_mem (⟨k, hk⟩ : ↥Qbar) hv

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

theorem range5 (a b c d e : ℂ) : Set.range ![a, b, c, d, e] = {a, b, c, d, e} := by
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

theorem mem5 {x a b c d e : ℂ} (hx : x ∈ Submodule.span (↥Qbar) ({a, b, c, d, e} : Set ℂ)) :
    ∃ k₀ k₁ k₂ k₃ k₄ : ↥Qbar, x = k₀ * a + k₁ * b + k₂ * c + k₃ * d + k₄ * e := by
  rw [← range5] at hx
  obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 hx
  exact ⟨k 0, k 1, k 2, k 3, k 4, by rw [← hk]; simp [Fin.sum_univ_five, Subfield.smul_def]⟩

/-- Every quadratic `X² − pX − q` over `Q̄` has a root in `Q̄`. -/
theorem root2 (p q : ↥Qbar) : ∃ c : ↥Qbar, (c : ℂ) * c = p * c + q := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self ((p : ℂ) ^ 2 + 4 * q)
  have h4 : (4 : ℂ) ∈ Qbar := by simp
  have h2 : (2 : ℂ) ∈ Qbar := by simp
  have hdQ : d ∈ Qbar := by
    have : d ^ 2 ∈ Qbar := by
      rw [sq, ← hd]; exact add_mem (pow_mem p.2 2) (mul_mem h4 q.2)
    exact mem_Qbar_iff.2 (IsAlgebraic.of_pow two_pos (mem_Qbar_iff.1 this))
  refine ⟨⟨(p + d) / 2, div_mem (add_mem p.2 hdQ) h2⟩, ?_⟩
  show (p + d) / 2 * ((p + d) / 2) = (p : ℂ) * ((p + d) / 2) + q
  linear_combination (-1 / 4 : ℂ) * hd

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

/-- In an invisible `W_g`, `{h ∈ W : u h ∈ W} = ⟨1, u⁻¹, g⟩`. -/
theorem multipliers {u : ℂ} (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) (h1 : (1 : ℂ) ∈ W)
    (hu1 : u ∈ W) (hui : u⁻¹ ∈ W) (g : ℂ) (hli : LinearIndependent (↥Qbar) ![1, u, u⁻¹, g, u * g])
    (hWg : W = Submodule.span (↥Qbar) ({1, u, u⁻¹, g, u * g} : Set ℂ))
    (hu2 : u ^ 2 ∉ W) (hui2 : (u ^ 2)⁻¹ ∉ W) (hpole : ¬ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W)
    (h : ℂ) (hh : h ∈ W) (huh : u * h ∈ W) : ∃ a b c : ↥Qbar, h = a + b * u⁻¹ + c * g := by
  have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ (ne0 hu)
  have hgW : g ∈ W := hWg ▸ Submodule.subset_span (by simp)
  have hugW : u * g ∈ W := hWg ▸ Submodule.subset_span (by simp)
  obtain ⟨a₀, a₁, a₂, a₃, a₄, e⟩ := mem5 (hWg ▸ hh)
  have hy : (a₁ : ℂ) * u ^ 2 + a₄ * (u ^ 2 * g) ∈ W := by
    have : (a₁ : ℂ) * u ^ 2 + a₄ * (u ^ 2 * g) =
        u * h + (-(a₀ : ℂ)) * u + (-(a₂ : ℂ)) * 1 + (-(a₃ : ℂ)) * (u * g) := by
      rw [e]; linear_combination (-(a₂ : ℂ)) * hu'
    rw [this]
    exact add_mem (add_mem (add_mem huh (smem W (neg_mem a₀.2) hu1)) (smem W (neg_mem a₂.2) h1))
      (smem W (neg_mem a₃.2) hugW)
  by_cases h4 : a₄ = 0
  · have h1' : a₁ = 0 := by
      by_contra h1'
      have h1'' : (a₁ : ℂ) ≠ 0 := by exact_mod_cast h1'
      apply hu2
      have : u ^ 2 = (a₁ : ℂ)⁻¹ * ((a₁ : ℂ) * u ^ 2 + a₄ * (u ^ 2 * g)) := by
        rw [h4]; push_cast; field_simp; ring
      rw [this]; exact smem W (inv_mem a₁.2) hy
    refine ⟨a₀, a₂, a₃, ?_⟩
    rw [e, h4, h1']; push_cast; ring
  exfalso
  have h4' : (a₄ : ℂ) ≠ 0 := by exact_mod_cast h4
  obtain ⟨b₀, b₁, b₂, b₃, b₄, e2⟩ := mem5 (hWg ▸ (smem W (inv_mem a₄.2) hy))
  obtain ⟨c, hc⟩ := root2 b₄ b₃
  set bQ : ↥Qbar := a₁ / a₄ with hbQ
  have e2' : u ^ 2 * g + bQ * u ^ 2 = b₀ * 1 + b₁ * u + b₂ * u⁻¹ + b₃ * g + b₄ * (u * g) := by
    rw [← e2, hbQ]; push_cast; field_simp; ring
  set F := ((c : ℂ) - b₄) * g + u * g + bQ * u with hF
  have hFW : F ∈ W := add_mem (add_mem (smem W (sub_mem c.2 b₄.2) hgW) hugW) (smem W bQ.2 hu1)
  have hFH : ∀ α β γ : ↥Qbar, F ≠ α + β * u + γ * u⁻¹ := by
    intro α β γ hFe
    have := li5_use hli (-α) (bQ - β) (-γ) (c - b₄) 1 (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
      push_cast
      linear_combination hFe)
    exact one_ne_zero this.2.2.2.2
  have he : (u - c) * F = b₀ + ((b₁ - c * bQ : ↥Qbar) : ℂ) * u + b₂ * u⁻¹ := by
    rw [hF]; push_cast
    linear_combination e2' - g * hc
  rcases pole hu W h1 hui F hFW hFH c b₀ (b₁ - c * bQ) b₂ he with h | h
  · exact hui2 h
  · exact hpole h

end R20_deg1c

open DiazModulus R20_deg1c in
theorem solution (u s : ℂ) (hu : u ∉ Qbar)
    (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (hσ : ∀ w ∈ W, conj w ∈ W) (hD1 : (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W)) :
    (u ^ 2 ∈ W ∨ conj u ^ 2 ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) ∨
    ∃ lam f : ℂ, lam ∈ Qbar ∧ lam * conj lam = 1 ∧ conj f = f ∧
      W = Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ) := by
  have hu0 := ne0 hu
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : u * conj u = 0 := by rw [← hss]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact hu0 h
    · exact hu0 (by simpa using h)
  have hssQ : s * s ∈ Qbar := mul_mem hs hs
  have hss0 : s * s ≠ 0 := mul_ne_zero hs0 hs0
  have hcu : conj u = s * s * u⁻¹ := by
    rw [hss, mul_comm u, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  by_cases hvis : u ^ 2 ∈ W ∨ conj u ^ 2 ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W
  · exact Or.inl hvis
  right
  have hu2 : u ^ 2 ∉ W := fun h => hvis (Or.inl h)
  have hui2 : (u ^ 2)⁻¹ ∉ W := fun h => hvis (Or.inr (Or.inl (by
    have : conj u ^ 2 = (s * s) ^ 2 * (u ^ 2)⁻¹ := by rw [hcu]; ring
    rw [this]; exact smem W (pow_mem hssQ 2) h)))
  have hpole : ¬ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W := fun h => hvis (Or.inr (Or.inr h))
  rcases (DiazModulus.degree_one_multiplier_space_visible_or_degree_one_space u hu W hW h1 hu1
    hui).1 hD1 with h | h | h | ⟨g, hli, hWg⟩
  · exact absurd h hu2
  · exact absurd h hui2
  · exact absurd h hpole
  have hgW : g ∈ W := hWg ▸ Submodule.subset_span (by simp)
  have hugW : u * g ∈ W := hWg ▸ Submodule.subset_span (by simp)
  -- conjugation maps `{h ∈ W : u h ∈ W}` into `u · {h ∈ W : u h ∈ W}`
  have hcg : conj g ∈ Submodule.span Qbar ({1, u, u * g} : Set ℂ) := by
    have hhW : u⁻¹ * conj g ∈ W := by
      have : u⁻¹ * conj g = (s * s)⁻¹ * conj (u * g) := by
        rw [map_mul, hcu]; field_simp
      rw [this]; exact smem W (inv_mem hssQ) (hσ _ hugW)
    have huhW : u * (u⁻¹ * conj g) ∈ W := by
      rw [mul_inv_cancel_left₀ hu0]; exact hσ g hgW
    obtain ⟨a, b, c, e⟩ :=
      multipliers hu W h1 hu1 hui g hli hWg hu2 hui2 hpole _ hhW huhW
    refine Submodule.mem_span_triple.2 ⟨b, a, c, ?_⟩
    simp only [Subfield.smul_def, smul_eq_mul]
    have : conj g = u * (u⁻¹ * conj g) := by rw [mul_inv_cancel_left₀ hu0]
    rw [this, e]; field_simp; ring
  have hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g] := by
    apply li5
    intro a b c d e h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at h
    obtain ⟨x, y, z, w, v⟩ := li5_use hli a b (c * ⟨s * s, hssQ⟩) d e (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
      push_cast
      rw [hcu] at h
      linear_combination h)
    refine ⟨x, y, ?_, w, v⟩
    exact (mul_eq_zero.1 z).resolve_right (fun h0 => hss0 (congrArg Subtype.val h0))
  have hWeq : Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · refine Submodule.span_le.2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      exacts [h1, hu1, hσ _ hu1, hgW, hugW]
    · rw [hW, ← range5, finrank_span_eq_card hind]; simp
  obtain ⟨lam, f, hlam, hlam1, hf, hspan⟩ :=
    DiazModulus.conj_equivariant_degree_one_space_eq_real_pencil_space u s hu hs hsr hss g hind hcg
  exact ⟨lam, f, hlam, hlam1, hf, by rw [← hWeq, hspan]⟩
