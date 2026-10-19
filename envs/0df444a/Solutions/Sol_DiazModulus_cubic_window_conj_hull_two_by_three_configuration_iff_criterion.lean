-- Prove2me | solution 1 for DiazModulus.cubic_window_conj_hull_two_by_three_configuration_iff_criterion
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:29:52.349415+00:00
-- url     : https://prove2.me/submissions/420a03f2-31a1-4a2e-ad24-2478d8cc9749

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_conj_hull_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_cubic_window_hull_polynomial_class_iff
import Theorems.Thm_DiazModulus_cubic_window_hull_involution_class_iff
import Theorems.Thm_DiazModulus_cubic_window_hull_real_pencil_class_iff

open Complex ComplexConjugate

/-! # Corollary E(b): the configuration criterion for a cubic window

Let `u ∉ Q̄`, `s ∈ Q̄`, `s² = u ū`, and `z ≡ A ū³ + B ū² + C u² + D u³` modulo `span(1, u, ū)` with
a five-dimensional hull `W`. Then `s` is real (`s² = |u|² > 0`), `v = u/s` has `v v̄ = 1` and
`v ∉ Q̄`, `u = s v`, `ū = s v̄`, so `span(1, u, ū, ·, ·) = span(1, v, v̄, ·, ·)` and
`z ≡ a v̄³ + b v̄² + c v² + d v³` with `a = A s³`, `b = B s²`, `c = C s²`, `d = D s³`. The Plücker
coordinates become `ac̄ − bd̄ = s⁵Δ` and `aā − dd̄ = s⁶N` (`Δ = AC̄ − BD̄`, `N = AĀ − DD̄`). The
classes (P), (Q), (R) are then read off `cubic_window_hull_polynomial_class_iff`,
`cubic_window_hull_involution_class_iff` and `cubic_window_hull_real_pencil_class_iff` (for (P),
`αu² + βu³ = (αs²)v² + (βs³)v³`). Writing `z = Σ_{|j| ≤ 3} c_j v^j`, Theorem E
(`laurent_conj_hull_two_by_three_configuration_iff`, `k = 3`) says that `W` carries a configuration
iff (P) or (Q) or (R), that is `Δ = 0`, or `N = 0` with `(A, D) ≠ 0`, or `|Δ|² = s²N²` with
`N ≠ 0`; since `A = D = 0` forces `Δ = 0`, this is `N Δ (|Δ|² − s² N²) = 0`.
-/

namespace R18_Eb

open DiazModulus

theorem span_mul_mem {S : Set ℂ} {c w : ℂ} (hc : c ∈ Qbar) (hw : w ∈ Submodule.span Qbar S) :
    c * w ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hw
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- `s² = u ū` with `u ≠ 0` makes `s` real. -/
theorem s_real {u s : ℂ} (hu0 : u ≠ 0) (hss : s * s = u * conj u) : conj s = s := by
  have h1 := congrArg Complex.im hss
  have h2 := congrArg Complex.re hss
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1 h2
  have hpos : 0 < u.re * u.re + u.im * u.im := by
    have := Complex.normSq_pos.2 hu0
    rw [Complex.normSq_apply] at this
    linarith
  apply Complex.ext
  · simp
  · simp only [Complex.conj_im]
    have : s.re * s.im = 0 := by linear_combination h1 / 2
    rcases mul_eq_zero.1 this with h | h
    · rw [h] at h2; nlinarith [sq_nonneg s.im]
    · rw [h, neg_zero]

/-- Rescaling `u = s v`, `ū = s v̄` (`s ≠ 0` in `Q̄`) does not change a hull. -/
theorem span_scale {u v s : ℂ} (hs : s ∈ Qbar) (hs0 : s ≠ 0) (hu : u = s * v)
    (hcu : conj u = s * conj v) (T : Set ℂ) :
    Submodule.span Qbar (insert 1 (insert u (insert (conj u) T))) =
      Submodule.span Qbar (insert 1 (insert v (insert (conj v) T))) := by
  have hv : v = s⁻¹ * u := by rw [hu, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  have hcv : conj v = s⁻¹ * conj u := by rw [hcu, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  apply le_antisymm <;> rw [Submodule.span_le] <;> intro x hx <;>
    simp only [Set.mem_insert_iff] at hx
  · rcases hx with h | h | h | h
    · rw [h]; exact Submodule.subset_span (by simp)
    · rw [h, hu]; exact span_mul_mem hs (Submodule.subset_span (by simp))
    · rw [h, hcu]; exact span_mul_mem hs (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ h)))
  · rcases hx with h | h | h | h
    · rw [h]; exact Submodule.subset_span (by simp)
    · rw [h, hv]; exact span_mul_mem (inv_mem hs) (Submodule.subset_span (by simp))
    · rw [h, hcv]; exact span_mul_mem (inv_mem hs) (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ h)))

theorem span_scale3 {u v s : ℂ} (hs : s ∈ Qbar) (hs0 : s ≠ 0) (hu : u = s * v)
    (hcu : conj u = s * conj v) :
    Submodule.span Qbar ({1, u, conj u} : Set ℂ) = Submodule.span Qbar ({1, v, conj v} : Set ℂ) := by
  have hv : v = s⁻¹ * u := by rw [hu, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  have hcv : conj v = s⁻¹ * conj u := by rw [hcu, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  apply le_antisymm <;> rw [Submodule.span_le] <;> intro x hx <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx <;> rcases hx with h | h | h <;>
    rw [h]
  · exact Submodule.subset_span (by simp)
  · rw [hu]; exact span_mul_mem hs (Submodule.subset_span (by simp))
  · rw [hcu]; exact span_mul_mem hs (Submodule.subset_span (by simp))
  · exact Submodule.subset_span (by simp)
  · rw [hv]; exact span_mul_mem (inv_mem hs) (Submodule.subset_span (by simp))
  · rw [hcv]; exact span_mul_mem (inv_mem hs) (Submodule.subset_span (by simp))

/-- The bookkeeping of the four statements. -/
theorem assemble {P Q R Cf X₁ X₂ X₃ X₄ : Prop} (h₁ : P ↔ X₁) (h₂ : Q ↔ X₂) (h₃ : R ↔ X₃)
    (h₄ : Cf ↔ (P ∨ Q ∨ R)) (h₅ : (X₁ ∨ X₂ ∨ X₃) ↔ X₄) :
    (P ↔ X₁) ∧ (Q ↔ X₂) ∧ (R ↔ X₃) ∧ (Cf ↔ X₄) :=
  ⟨h₁, h₂, h₃, h₄.trans ((or_congr h₁ (or_congr h₂ h₃)).trans h₅)⟩

end R18_Eb

open DiazModulus R18_Eb in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (z A B C D : ℂ) (hA : A ∈ Qbar) (hB : B ∈ Qbar) (hC : C ∈ Qbar) (hD : D ∈ Qbar)
    (hz : z - (A * conj u ^ 3 + B * conj u ^ 2 + C * u ^ 2 + D * u ^ 3) ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ))
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 5) :
    ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ↔ (A * conj C - B * conj D) = 0) ∧
    ((∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ↔
      ((A * conj A - D * conj D) = 0 ∧ (A ≠ 0 ∨ D ≠ 0))) ∧
    ((∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ)) ↔
      ((A * conj C - B * conj D) * conj (A * conj C - B * conj D) = s ^ 2 * (A * conj A - D * conj D) ^ 2 ∧ (A * conj A - D * conj D) ≠ 0)) ∧
    ((∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ↔
      (A * conj A - D * conj D) * (A * conj C - B * conj D) * ((A * conj C - B * conj D) * conj (A * conj C - B * conj D) - s ^ 2 * (A * conj A - D * conj D) ^ 2) = 0) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ zero_mem _)
  have hsr : conj s = s := s_real hu0 hss
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero, eq_comm, Complex.mul_conj, Complex.ofReal_eq_zero,
      Complex.normSq_eq_zero] at hss
    exact hu0 hss
  obtain ⟨v, hvdef⟩ : ∃ v, v = u / s := ⟨_, rfl⟩
  have hu' : u = s * v := by rw [hvdef, mul_div_cancel₀ _ hs0]
  have hcu' : conj u = s * conj v := by rw [hvdef, map_div₀, hsr, mul_div_cancel₀ _ hs0]
  have hv : v ∉ Qbar := fun h => hu (by rw [hu']; exact mul_mem hs h)
  have hv1 : v * conj v = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hs0 hs0)
    linear_combination -hss - conj u * hu' - (s * v) * hcu'
  rw [← hvdef]
  -- the window in `v`
  have hm : A * conj u ^ 3 + B * conj u ^ 2 + C * u ^ 2 + D * u ^ 3 = (A * s ^ 3) * conj v ^ 3 +
      (B * s ^ 2) * conj v ^ 2 + (C * s ^ 2) * v ^ 2 + (D * s ^ 3) * v ^ 3 := by
    rw [hcu', hu']; ring
  have hH := span_scale3 hs hs0 hu' hcu'
  have hz' := hz
  rw [hm, hH] at hz'
  have hW := span_scale hs hs0 hu' hcu' {z, conj z}
  have h5' := h5
  rw [hW] at h5'
  have hA3 := mul_mem hA (pow_mem hs 3)
  have hB2 := mul_mem hB (pow_mem hs 2)
  have hC2 := mul_mem hC (pow_mem hs 2)
  have hD3 := mul_mem hD (pow_mem hs 3)
  have E1 := DiazModulus.cubic_window_hull_polynomial_class_iff v hv hv1 z (A * s ^ 3) (B * s ^ 2)
    (C * s ^ 2) (D * s ^ 3) hA3 hB2 hC2 hD3 hz' h5'
  have E2 := DiazModulus.cubic_window_hull_involution_class_iff v hv hv1 z (A * s ^ 3) (B * s ^ 2)
    (C * s ^ 2) (D * s ^ 3) hA3 hB2 hC2 hD3 hz' h5'
  have E3 := DiazModulus.cubic_window_hull_real_pencil_class_iff v hv hv1 z (A * s ^ 3) (B * s ^ 2)
    (C * s ^ 2) (D * s ^ 3) hA3 hB2 hC2 hD3 hz'
  have e12 : A * s ^ 3 * conj (C * s ^ 2) - B * s ^ 2 * conj (D * s ^ 3) =
      s ^ 5 * (A * conj C - B * conj D) := by
    simp only [map_mul, map_pow, hsr]; ring
  have e14 : A * s ^ 3 * conj (A * s ^ 3) - D * s ^ 3 * conj (D * s ^ 3) =
      s ^ 6 * (A * conj A - D * conj D) := by
    simp only [map_mul, map_pow, hsr]; ring
  rw [e12] at E1 E3
  rw [e14] at E2 E3
  have hc5 : conj (s ^ 5 * (A * conj C - B * conj D)) = s ^ 5 * conj (A * conj C - B * conj D) := by
    rw [map_mul, map_pow, hsr]
  rw [hc5] at E3
  -- Theorem E with `k = 3`
  obtain ⟨h₀, h₁, h₂, hh⟩ : ∃ h₀ h₁ h₂ : ℂ, h₀ ∈ Qbar ∧ h₁ ∈ Qbar ∧ h₂ ∈ Qbar ∧
      z - ((A * s ^ 3) * conj v ^ 3 + (B * s ^ 2) * conj v ^ 2 + (C * s ^ 2) * v ^ 2 +
        (D * s ^ 3) * v ^ 3) = h₀ + h₁ * v + h₂ * conj v := by
    obtain ⟨c₁, w₁, hw₁, e1⟩ := Submodule.mem_span_insert.1 hz'
    obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
    obtain ⟨c₃, rfl⟩ := Submodule.mem_span_singleton.1 hw₂
    refine ⟨c₁, c₂, c₃, c₁.2, c₂.2, c₃.2, ?_⟩
    rw [e1]; simp only [Subfield.smul_def, smul_eq_mul]; ring
  obtain ⟨hh₀, hh₁, hh₂, hhz⟩ := hh
  obtain ⟨cf, hcf⟩ : ∃ cf : ℤ → ℂ, cf = fun j => if j = -3 then A * s ^ 3 else
      if j = -2 then B * s ^ 2 else if j = -1 then h₂ else if j = 0 then h₀ else if j = 1 then h₁
      else if j = 2 then C * s ^ 2 else if j = 3 then D * s ^ 3 else 0 := ⟨_, rfl⟩
  have hcfQ : ∀ j, cf j ∈ Qbar := by
    intro j
    have hite : ∀ {p : Prop} [Decidable p] {x y : ℂ}, x ∈ Qbar → y ∈ Qbar →
        (if p then x else y) ∈ Qbar := fun hx hy => by split <;> assumption
    rw [hcf]
    exact hite hA3 (hite hB2 (hite hh₂ (hite hh₀ (hite hh₁ (hite hC2 (hite hD3 (zero_mem _)))))))
  have hsum : ∑ j ∈ Finset.Icc (-((3 : ℕ) : ℤ)) ((3 : ℕ) : ℤ), cf j * v ^ j = z := by
    have hinv : v⁻¹ = conj v := inv_eq_of_mul_eq_one_right hv1
    have hI : Finset.Icc (-((3 : ℕ) : ℤ)) ((3 : ℕ) : ℤ) = {-3, -2, -1, 0, 1, 2, 3} := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hI, hcf]
    simp [Finset.sum_insert, zpow_neg]
    rw [← hinv] at hhz
    linear_combination -hhz
  have hE := DiazModulus.laurent_conj_hull_two_by_three_configuration_iff u s hu hs hss 3 cf hcfQ
  rw [← hvdef, hsum] at hE
  refine assemble ?_ ?_ ?_ (hE.trans (and_iff_right h5)) ?_
  · -- (P)
    rw [hW]
    refine Iff.trans ⟨fun ⟨α, β, hα, hβ, hne, hmem⟩ => ⟨α * s ^ 2, β * s ^ 3, mul_mem hα (pow_mem hs 2), mul_mem hβ (pow_mem hs 3),
      hne.imp (fun h => mul_ne_zero h (pow_ne_zero _ hs0)) (fun h => mul_ne_zero h (pow_ne_zero _ hs0)),
      by convert hmem using 1; rw [hu']; ring⟩,
      fun ⟨α, β, hα, hβ, hne, hmem⟩ => ⟨α * s⁻¹ ^ 2, β * s⁻¹ ^ 3,
      mul_mem hα (pow_mem (inv_mem hs) 2), mul_mem hβ (pow_mem (inv_mem hs) 3),
      hne.imp (fun h => mul_ne_zero h (pow_ne_zero _ (inv_ne_zero hs0)))
        (fun h => mul_ne_zero h (pow_ne_zero _ (inv_ne_zero hs0))),
      by convert hmem using 1; rw [hu']; field_simp⟩⟩ (E1.trans ?_)
    rw [mul_eq_zero, or_iff_right (pow_ne_zero 5 hs0)]
  · -- (Q)
    simp only [span_scale hs hs0 hu' hcu']
    refine E2.trans (and_congr ?_ (or_congr ?_ ?_))
    · rw [mul_eq_zero, or_iff_right (pow_ne_zero 6 hs0)]
    · exact mul_ne_zero_iff_right (pow_ne_zero 3 hs0)
    · exact mul_ne_zero_iff_right (pow_ne_zero 3 hs0)
  · -- (R)
    simp only [span_scale hs hs0 hu' hcu']
    refine E3.trans (and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_)
    · apply mul_left_cancel₀ (pow_ne_zero 10 hs0)
      linear_combination h
    · linear_combination s ^ 10 * h
    · exact (mul_ne_zero_iff_left (pow_ne_zero 6 hs0))
  · -- the criterion
    constructor
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · rw [h]; ring
      · rw [h]; ring
      · rw [h, sub_self, mul_zero]
    · intro h
      by_cases hΔ : A * conj C - B * conj D = 0
      · exact Or.inl hΔ
      by_cases hN : A * conj A - D * conj D = 0
      · by_cases had : A ≠ 0 ∨ D ≠ 0
        · exact Or.inr (Or.inl ⟨hN, had⟩)
        · push Not at had
          exact absurd (by rw [had.1, had.2]; simp) hΔ
      · refine Or.inr (Or.inr ⟨sub_eq_zero.1 ?_, hN⟩)
        exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero hN hΔ)
