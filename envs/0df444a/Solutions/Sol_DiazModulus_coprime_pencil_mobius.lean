-- Prove2me | solution 1 for DiazModulus.coprime_pencil_mobius
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:32:29.619701+00:00
-- url     : https://prove2.me/submissions/f95815bd-0539-4264-84b5-ec2667b04f27

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A Möbius change of a coprime quadratic pencil

Let `p, q` be coprime with `max(deg p, deg q) = 2`, and put `p′ = ap + bq`, `q′ = cp + dq` with
`D = ad − bc ≠ 0`. Inverting the `2 × 2` change of basis gives `p = D⁻¹(dp′ − bq′)` and
`q = D⁻¹(aq′ − cp′)`. Coprimality: from a Bézout identity `xp + yq = 1`,
`D⁻¹(dx − cy)·p′ + D⁻¹(ay − bx)·q′ = xp + yq = 1`. Degree: `p′, q′` have degree at most 2 as
combinations of `p, q`; if both had degree at most 1, so would `p` and `q` by the inversion
formulas, against `max(deg p, deg q) = 2`. ∎
-/

namespace R20_mobius

open DiazModulus Polynomial

/-- `deg (C α * f + C β * g) ≤ max (deg f) (deg g)`. -/
theorem natDegree_comb_le {K : Type*} [Field K] (α β : K) (f g : K[X]) (n : ℕ)
    (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ n) : (C α * f + C β * g).natDegree ≤ n :=
  (natDegree_add_le _ _).trans
    (max_le ((natDegree_C_mul_le _ _).trans hf) ((natDegree_C_mul_le _ _).trans hg))

end R20_mobius

open DiazModulus R20_mobius Polynomial in
theorem solution {K : Type*} [Field K] (p q : K[X]) (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (a b c d : K) (had : a * d - b * c ≠ 0) :
    IsCoprime (C a * p + C b * q) (C c * p + C d * q) ∧
      max (C a * p + C b * q).natDegree (C c * p + C d * q).natDegree = 2 := by
  set D := a * d - b * c with hD
  have hinv : C D⁻¹ * (C a * C d - C b * C c) = (1 : K[X]) := by
    rw [← C_mul, ← C_mul, ← C_sub, ← hD, ← C_mul, inv_mul_cancel₀ had, C_1]
  have hp' : p = C (D⁻¹ * d) * (C a * p + C b * q) + C (-D⁻¹ * b) * (C c * p + C d * q) := by
    simp only [map_mul, map_neg]; linear_combination (-p) * hinv
  have hq' : q = C (-D⁻¹ * c) * (C a * p + C b * q) + C (D⁻¹ * a) * (C c * p + C d * q) := by
    simp only [map_mul, map_neg]; linear_combination (-q) * hinv
  refine ⟨?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hcop
    refine ⟨C D⁻¹ * (x * C d - y * C c), C D⁻¹ * (y * C a - x * C b), ?_⟩
    linear_combination (x * p + y * q) * hinv + hxy
  · have hp : p.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
    have hq : q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
    have h1 := natDegree_comb_le a b p q 2 hp hq
    have h2 := natDegree_comb_le c d p q 2 hp hq
    by_contra hne
    have h1' : (C a * p + C b * q).natDegree ≤ 1 := by omega
    have h2' : (C c * p + C d * q).natDegree ≤ 1 := by omega
    have hp1 : p.natDegree ≤ 1 := by
      rw [hp']; exact natDegree_comb_le _ _ _ _ 1 h1' h2'
    have hq1 : q.natDegree ≤ 1 := by
      rw [hq']; exact natDegree_comb_le _ _ _ _ 1 h1' h2'
    omega
