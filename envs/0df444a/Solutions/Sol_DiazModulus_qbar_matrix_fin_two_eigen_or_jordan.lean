-- Prove2me | solution 1 for DiazModulus.qbar_matrix_fin_two_eigen_or_jordan
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:32:32.328633+00:00
-- url     : https://prove2.me/submissions/e0c7ec5b-c877-4ef3-9805-85bee6c6bbe8

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A `2 × 2` matrix over `Q̄` is scalar, has two eigenvalues, or is one Jordan block

Write `M = [[a, b], [c, d]]`. Everything is explicit, with `Fin 2` vectors `![x, y]`; two vectors
`![x, y]`, `![x', y']` are independent as soon as `x y' − y x' ≠ 0`.
- `b = 0`, `c = 0`: if `a = d` then `M = a • 1`; otherwise `![1, 0]`, `![0, 1]` are eigenvectors for
  `a ≠ d`.
- `b = 0`, `c ≠ 0`: if `a = d` then `v = ![0, c]`, `w = ![1, 0]` is a Jordan pair (`M w = a w + v`);
  otherwise `![0, 1]` and `![a − d, c]` are eigenvectors for `d ≠ a`.
- `b ≠ 0`: take a root `l ∈ Q̄` of `t² − (a + d) t + (ad − bc)`: a complex square root `s` of the
  discriminant is algebraic over `ℚ` (`IsAlgebraic.of_pow`), hence in `Q̄`, and `l = (a + d + s)/2`.
  The other root is `m = a + d − l`. If `l ≠ m`, `![b, l − a]` and `![b, m − a]` are eigenvectors
  (determinant `b (m − l) ≠ 0`); if `l = m`, `v = ![b, l − a]`, `w = ![0, 1]` is a Jordan pair.
No algebraic-closedness instance for `Q̄` is needed. -/

namespace R20_jordan

open DiazModulus

theorem exists_sqrt (D : ↥Qbar) : ∃ s : ↥Qbar, s * s = D := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (D : ℂ) (n := 2) (by norm_num)
  have hzq : z ∈ Qbar := mem_Qbar_iff.2 (IsAlgebraic.of_pow (n := 2) (by norm_num)
    (by rw [hz]; exact mem_Qbar_iff.1 D.2))
  exact ⟨⟨z, hzq⟩, Subtype.ext (by simp [← hz, sq])⟩

theorem exists_root2 (t e : ↥Qbar) : ∃ l : ↥Qbar, l * l - t * l + e = 0 := by
  obtain ⟨s, hs⟩ := exists_sqrt (t * t - 4 * e)
  have h2 : (2 : ↥Qbar) ≠ 0 := by
    intro h; have := congrArg (fun x : ↥Qbar => (x : ℂ)) h; norm_num at this
  refine ⟨(t + s) / 2, ?_⟩
  have hl : 2 * ((t + s) / 2) = t + s := mul_div_cancel₀ _ h2
  have h4 : (2 * 2) * (((t + s) / 2) * ((t + s) / 2) - t * ((t + s) / 2) + e) = 0 := by
    linear_combination (2 * ((t + s) / 2) + (t + s) - 2 * t) * hl + hs
  exact (mul_eq_zero.1 h4).resolve_left (mul_ne_zero h2 h2)

variable {K : Type*} [Field K]

theorem mulVec2 (a b c d x y : K) :
    !![a, b; c, d].mulVec ![x, y] = ![a * x + b * y, c * x + d * y] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eig (a b c d x y l : K) (h1 : a * x + b * y = l * x) (h2 : c * x + d * y = l * y) :
    !![a, b; c, d].mulVec ![x, y] = l • ![x, y] := by
  rw [mulVec2]; ext i; fin_cases i <;> simp [h1, h2]

theorem jor (a b c d x y x' y' l : K) (h1 : a * x + b * y = l * x + x')
    (h2 : c * x + d * y = l * y + y') :
    !![a, b; c, d].mulVec ![x, y] = l • ![x, y] + ![x', y'] := by
  rw [mulVec2]; ext i; fin_cases i <;> simp [h1, h2]

theorem li2 (x y x' y' : K) (h : x * y' - y * x' ≠ 0) :
    LinearIndependent K ![![x, y], ![x', y']] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul, Pi.zero_apply] at h0 h1
  constructor
  · have : s * (x * y' - y * x') = 0 := by linear_combination y' * h0 - x' * h1
    exact (mul_eq_zero.1 this).resolve_right h
  · have : t * (x * y' - y * x') = 0 := by linear_combination x * h1 - y * h0
    exact (mul_eq_zero.1 this).resolve_right h

end R20_jordan

open DiazModulus R20_jordan in
theorem solution (M : Matrix (Fin 2) (Fin 2) ↥Qbar) :
    (∃ c : ↥Qbar, M = c • (1 : Matrix (Fin 2) (Fin 2) ↥Qbar)) ∨
    (∃ (v w : Fin 2 → ↥Qbar) (c₁ c₂ : ↥Qbar), c₁ ≠ c₂ ∧ LinearIndependent (↥Qbar) ![v, w] ∧
        M.mulVec v = c₁ • v ∧ M.mulVec w = c₂ • w) ∨
    (∃ (v w : Fin 2 → ↥Qbar) (c : ↥Qbar), LinearIndependent (↥Qbar) ![v, w] ∧
        M.mulVec v = c • v ∧ M.mulVec w = c • w + v) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two M⟩
  by_cases hb : b = 0
  · subst hb
    by_cases hc : c = 0
    · subst hc
      by_cases had : a = d
      · subst had
        left
        exact ⟨a, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
      · right; left
        exact ⟨![1, 0], ![0, 1], a, d, had, li2 _ _ _ _ (by simp),
          eig _ _ _ _ _ _ _ (by ring) (by ring), eig _ _ _ _ _ _ _ (by ring) (by ring)⟩
    · by_cases had : a = d
      · subst had
        right; right
        refine ⟨![0, c], ![1, 0], a, li2 _ _ _ _ (by simpa using hc),
          eig _ _ _ _ _ _ _ (by ring) (by ring), ?_⟩
        exact jor _ _ _ _ _ _ _ _ _ (by ring) (by ring)
      · right; left
        refine ⟨![0, 1], ![a - d, c], d, a, Ne.symm had,
          li2 _ _ _ _ (by intro h; exact had (by linear_combination -h)),
          eig _ _ _ _ _ _ _ (by ring) (by ring), eig _ _ _ _ _ _ _ (by ring) (by ring)⟩
  · obtain ⟨l, hl⟩ := exists_root2 (a + d) (a * d - b * c)
    by_cases hlm : l = a + d - l
    · right; right
      refine ⟨![b, l - a], ![0, 1], l, li2 _ _ _ _ (by simpa using hb),
        eig _ _ _ _ _ _ _ (by ring) (by linear_combination (-1 : ↥Qbar) * hl), ?_⟩
      exact jor _ _ _ _ _ _ _ _ _ (by ring) (by linear_combination (-1 : ↥Qbar) * hlm)
    · right; left
      refine ⟨![b, l - a], ![b, (a + d - l) - a], l, a + d - l, hlm, li2 _ _ _ _ ?_,
        eig _ _ _ _ _ _ _ (by ring) (by linear_combination (-1 : ↥Qbar) * hl),
        eig _ _ _ _ _ _ _ (by ring) (by linear_combination (-1 : ↥Qbar) * hl)⟩
      intro h
      have h' : b * (a + d - l - l) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact hb h''
      · exact hlm (by linear_combination -h'')
