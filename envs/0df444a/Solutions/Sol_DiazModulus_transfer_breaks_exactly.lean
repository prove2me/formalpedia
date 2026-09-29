-- Prove2me | solution 1 for DiazModulus.transfer_breaks_exactly
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-13T10:45:55.693704+00:00
-- url     : https://prove2.me/submissions/af3f42a3-bff2-400c-aa51-3cb1c201004c

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazObstructionShape

open DiazModulus

/-! ## 0.  Ring endomorphisms of `ℂ` move algebraic numbers to algebraic numbers -/

/-- Every ring endomorphism of `ℂ` is a `ℚ`-algebra map, hence preserves algebraicity. -/
theorem map_isAlgebraic (Φ : ℂ →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ (Φ z) := by
  have h := IsAlgebraic.algHom Φ.toRatAlgHom hz
  simpa using h

/-! ## 1.  Rigidity: three of the four "failures" are one failure -/

/-- **Order preservation is free.**  A ring endomorphism of `ℂ` that maps real numbers to
real numbers is the identity on `ℝ`.  Neither continuity nor monotonicity is assumed:
`Real.RingHom.unique` supplies both. -/
theorem eq_self_on_real_of_mapsTo_real (Φ : ℂ →+* ℂ) (h : ∀ x : ℝ, (Φ (x : ℂ)).im = 0)
    (x : ℝ) : Φ (x : ℂ) = (x : ℂ) := by
  let ψ : ℝ →+* ℝ :=
    { toFun := fun y => (Φ (y : ℂ)).re
      map_one' := by simp
      map_mul' := by
        intro a b
        have hab : ((a * b : ℝ) : ℂ) = ((a : ℂ) * (b : ℂ)) := by push_cast; ring
        show (Φ ((a * b : ℝ) : ℂ)).re = (Φ ((a : ℝ) : ℂ)).re * (Φ ((b : ℝ) : ℂ)).re
        rw [hab, map_mul, Complex.mul_re, h a, h b]
        ring
      map_zero' := by simp
      map_add' := by
        intro a b
        have hab : ((a + b : ℝ) : ℂ) = ((a : ℂ) + (b : ℂ)) := by push_cast; ring
        show (Φ ((a + b : ℝ) : ℂ)).re = (Φ ((a : ℝ) : ℂ)).re + (Φ ((b : ℝ) : ℂ)).re
        rw [hab, map_add, Complex.add_re] }
  have hre : (Φ (x : ℂ)).re = x := Real.ringHom_apply ψ x
  exact Complex.ext (by simpa using hre) (by simpa using h x)

/-- A ring endomorphism of `ℂ` stabilising `ℝ` is the identity or complex conjugation. -/
theorem eq_id_or_conj_of_mapsTo_real (Φ : ℂ →+* ℂ) (h : ∀ x : ℝ, (Φ (x : ℂ)).im = 0) :
    Φ = RingHom.id ℂ ∨ Φ = starRingEnd ℂ := by
  have hsq : (Φ I - I) * (Φ I + I) = 0 := by
    have h2 : Φ I * Φ I = -1 := by
      rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
    linear_combination h2 - Complex.I_sq
  have key : ∀ z : ℂ, Φ z = (z.re : ℂ) + (z.im : ℂ) * Φ I := by
    intro z
    conv_lhs => rw [← Complex.re_add_im z]
    rw [map_add, map_mul, eq_self_on_real_of_mapsTo_real Φ h z.re,
      eq_self_on_real_of_mapsTo_real Φ h z.im]
  rcases mul_eq_zero.1 hsq with hI | hI
  · left
    have hI' : Φ I = I := sub_eq_zero.1 hI
    ext z
    rw [key z, hI']
    simp
  · right
    have hI' : Φ I = -I := by linear_combination hI
    ext z
    rw [key z, hI']
    simp [Complex.ext_iff]

/-- **Stabilising `ℝ` is the same as being `id` or `conj`.** -/
theorem mapsTo_real_iff_id_or_conj (Φ : ℂ →+* ℂ) :
    (∀ x : ℝ, (Φ (x : ℂ)).im = 0) ↔ (Φ = RingHom.id ℂ ∨ Φ = starRingEnd ℂ) := by
  refine ⟨eq_id_or_conj_of_mapsTo_real Φ, ?_⟩
  rintro (rfl | rfl) <;> intro x <;> simp

/-- **Commuting with conjugation globally is the same as being `id` or `conj`.**
Compare clause (c) of the transfer theorem, which asserts the commutation only on `Q̄(u)`:
on all of `ℂ` it would collapse `Φ` completely. -/
theorem conjComm_iff_id_or_conj (Φ : ℂ →+* ℂ) :
    (∀ z : ℂ, Φ (conj z) = conj (Φ z)) ↔ (Φ = RingHom.id ℂ ∨ Φ = starRingEnd ℂ) := by
  constructor
  · intro hc
    refine eq_id_or_conj_of_mapsTo_real Φ ?_
    intro x
    have hx : Φ ((x : ℂ)) = conj (Φ ((x : ℂ))) := by
      have := hc ((x : ℂ))
      rwa [Complex.conj_ofReal] at this
    have := congrArg Complex.im hx
    simp only [Complex.conj_im] at this
    linarith
  · rintro (rfl | rfl) <;> intro z <;> simp

/-- **Continuity is the same as being `id` or `conj`.**  One direction is Mathlib's
`Complex.ringHom_eq_id_or_conj_of_continuous`. -/
theorem continuous_iff_id_or_conj (Φ : ℂ →+* ℂ) :
    Continuous (Φ : ℂ → ℂ) ↔ (Φ = RingHom.id ℂ ∨ Φ = starRingEnd ℂ) := by
  constructor
  · intro hc
    exact Complex.ringHom_eq_id_or_conj_of_continuous hc
  · rintro (rfl | rfl)
    · exact continuous_id
    · exact Complex.continuous_conj

/-! ## 2.  What always transfers: the modulus, verbatim -/

/-- The modulus hypothesis is not merely transferred in the weak form "`|Φ u|` is again
algebraic": the image has **the same** modulus.  Only the fixing of `Q̄` and the
commutation with conjugation *at `u`* are used — exactly clauses (a) and (c) of the
transfer theorem. -/
theorem norm_map_eq_of_conjComm (Φ : ℂ →+* ℂ) (u : ℂ)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hconj : Φ (conj u) = conj (Φ u))
    (hmod : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) : ‖Φ u‖ = ‖u‖ := by
  have hsq : IsAlgebraic ℚ (((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    have : (((‖u‖ ^ 2 : ℝ) : ℂ)) = (((‖u‖ : ℝ) : ℂ)) ^ 2 := by push_cast; ring
    rw [this, ← mem_Qbar_iff]
    exact pow_mem (mem_Qbar_iff.2 hmod) 2
  have hu : u * conj u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : Φ u * conj (Φ u) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj, ← map_mul, hu, hfix _ hsq]
  have h2 : Φ u * conj (Φ u) = ((‖Φ u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : (‖Φ u‖ : ℝ) ^ 2 = (‖u‖ : ℝ) ^ 2 := by
    have := h1.symm.trans h2
    exact_mod_cast this.symm
  nlinarith [norm_nonneg (Φ u), norm_nonneg u, h3]

/-! ## 3.  The two load-bearing failures -/

/-- **If `Φ` respects `exp` at `u`, it carries a candidate to a candidate.**
So the exponential hypothesis is the whole of what the transfer construction has to
destroy: the other two clauses of candidacy are carried across by (a) and (c) alone. -/
theorem isCandidate_map_of_expComm (Φ : ℂ →+* ℂ) (u : ℂ)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hconj : Φ (conj u) = conj (Φ u))
    (hexp : Φ (Complex.exp u) = Complex.exp (Φ u))
    (hu : IsCandidate u) : IsCandidate (Φ u) := by
  obtain ⟨hu0, hmod, hexpalg⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    exact hu0 (Φ.injective (by rw [h0, map_zero]))
  · rw [norm_map_eq_of_conjComm Φ u hfix hconj hmod]
    exact hmod
  · rw [← hexp, hfix _ hexpalg]
    exact hexpalg

/-- **If `Φ` respects the real structure, it carries a candidate to a candidate.**
By §1 such a `Φ` is `id` or `conj`, and `conj u` is a candidate whenever `u` is. -/
theorem isCandidate_map_of_mapsTo_real (Φ : ℂ →+* ℂ) (u : ℂ)
    (hre : ∀ x : ℝ, (Φ (x : ℂ)).im = 0) (hu : IsCandidate u) : IsCandidate (Φ u) := by
  obtain ⟨hu0, hmod, hexpalg⟩ := hu
  rcases (mapsTo_real_iff_id_or_conj Φ).1 hre with rfl | rfl
  · exact ⟨hu0, hmod, hexpalg⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa using hu0
    · show IsAlgebraic ℚ ((‖(starRingEnd ℂ) u‖ : ℝ) : ℂ)
      rw [Complex.norm_conj]
      exact hmod
    · show IsAlgebraic ℚ (Complex.exp ((starRingEnd ℂ) u))
      rw [Complex.exp_conj]
      exact map_isAlgebraic (starRingEnd ℂ) hexpalg

/-- **The shape of the obstruction.**  Let `u` be a candidate and let `Φ` be any ring
endomorphism of `ℂ` fixing the algebraic numbers pointwise and commuting with conjugation
at `u` — clauses (a) and (c) of the transfer theorem.  If the image `Φ u` is *not* a
candidate, then:

* the modulus hypothesis was carried across unchanged, `‖Φ u‖ = ‖u‖`;
* `Φ` fails to commute with `exp` at `u`;
* `Φ` fails to stabilise `ℝ`, fails to commute with conjugation somewhere, is
  discontinuous, and is neither `id` nor `conj` — these four being one failure.

Read as a constraint on proofs: the only two resources a proof of Diaz's conjecture can
draw on are the exponential and the real structure of `ℂ`; the modulus hypothesis
supplies nothing that survives, and the three "analytic" failures are one resource, not
three. -/
theorem transfer_breaks_exactly (Φ : ℂ →+* ℂ) (u : ℂ)
    (hu : IsCandidate u)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hconj : Φ (conj u) = conj (Φ u))
    (hnot : ¬ IsCandidate (Φ u)) :
    ‖Φ u‖ = ‖u‖ ∧
      Φ (Complex.exp u) ≠ Complex.exp (Φ u) ∧
      (∃ x : ℝ, (Φ (x : ℂ)).im ≠ 0) ∧
      (∃ z : ℂ, Φ (conj z) ≠ conj (Φ z)) ∧
      ¬ Continuous (Φ : ℂ → ℂ) ∧
      Φ ≠ RingHom.id ℂ ∧ Φ ≠ starRingEnd ℂ := by
  have hnid : ¬ (Φ = RingHom.id ℂ ∨ Φ = starRingEnd ℂ) := by
    intro hor
    exact hnot (isCandidate_map_of_mapsTo_real Φ u ((mapsTo_real_iff_id_or_conj Φ).2 hor) hu)
  refine ⟨norm_map_eq_of_conjComm Φ u hfix hconj hu.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hexp
    exact hnot (isCandidate_map_of_expComm Φ u hfix hconj hexp hu)
  · by_contra hc
    exact hnid ((mapsTo_real_iff_id_or_conj Φ).1
      (fun x => not_not.1 (fun h => hc ⟨x, h⟩)))
  · by_contra hc
    exact hnid ((conjComm_iff_id_or_conj Φ).1
      (fun z => not_not.1 (fun h => hc ⟨z, h⟩)))
  · intro hc
    exact hnid ((continuous_iff_id_or_conj Φ).1 hc)
  · intro h; exact hnid (Or.inl h)
  · intro h; exact hnid (Or.inr h)


/-! ## 4.  `exp`-compatibility already sees `π`

A ring endomorphism fixing `Q̄` pointwise says nothing about transcendental constants.
Requiring in addition that it commute with `exp` pins `2πi`, hence `π`, immediately — so
the exponential is not merely a *different* failure from the real-structure failure, it is
itself a source of rigidity. -/

/-- `i` is algebraic over `ℚ`. -/
theorem isAlgebraic_I : IsAlgebraic ℚ (I : ℂ) :=
  ⟨Polynomial.X ^ 2 - Polynomial.C (-1),
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, by simp [Complex.I_sq]⟩

/-- If `Φ` fixes the algebraic numbers pointwise and commutes with `exp`, then `Φ` fixes
`2πi`. -/
theorem map_two_pi_I_of_expComm (Φ : ℂ →+* ℂ)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hcomm : ∀ z : ℂ, Φ (Complex.exp z) = Complex.exp (Φ z)) :
    Φ (2 * (Real.pi : ℂ) * I) = 2 * (Real.pi : ℂ) * I := by
  have h1 : Complex.exp (Φ (2 * (Real.pi : ℂ) * I)) = 1 := by
    rw [← hcomm, Complex.exp_two_pi_mul_I, map_one]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
  -- Testing `Φ` against an `n`-th root of unity shows `n ∣ k - 1`, for every `n ≥ 1`.
  have hdvd : ∀ n : ℕ, 0 < n → ∃ m : ℤ, k - 1 = m * (n : ℤ) := by
    intro n hnpos
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hcancel : (n : ℂ) * ((2 * (Real.pi : ℂ) * I) / n) = 2 * (Real.pi : ℂ) * I := by
      field_simp
    have hζn : (Complex.exp ((2 * (Real.pi : ℂ) * I) / n)) ^ n = 1 := by
      rw [← Complex.exp_nat_mul, hcancel, Complex.exp_two_pi_mul_I]
    have hζalg : IsAlgebraic ℚ (Complex.exp ((2 * (Real.pi : ℂ) * I) / n)) :=
      ⟨Polynomial.X ^ n - Polynomial.C 1,
        Polynomial.X_pow_sub_C_ne_zero hnpos 1, by simp [hζn]⟩
    have h5 : Φ (Complex.exp ((2 * (Real.pi : ℂ) * I) / n))
        = Complex.exp ((2 * (Real.pi : ℂ) * I) / n) := hfix _ hζalg
    have h6 : Φ (Complex.exp ((2 * (Real.pi : ℂ) * I) / n))
        = Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * I) / n) := by
      rw [hcomm, map_div₀, hk, map_natCast]
    have hex : Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * I) / n)
        = Complex.exp ((2 * (Real.pi : ℂ) * I) / n) := h6.symm.trans h5
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hex
    field_simp at hm
    have hmC : ((k : ℤ) : ℂ) = (((1 : ℤ) + (n : ℤ) * m : ℤ) : ℂ) := by
      push_cast
      linear_combination hm
    have hmZ : k = 1 + (n : ℤ) * m := by exact_mod_cast hmC
    exact ⟨m, by rw [hmZ]; ring⟩
  have hk1 : k = 1 := by
    obtain ⟨m, hm⟩ := hdvd ((k - 1).natAbs + 1) (by omega)
    by_contra hne
    have hd : k - 1 ≠ 0 := by omega
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hm
      exact hd hm
    have h1m : (1 : ℤ) ≤ |m| := by
      have := abs_pos.2 hm0
      omega
    have hN : (0 : ℤ) < (((k - 1).natAbs + 1 : ℕ) : ℤ) := by positivity
    have hle : (((k - 1).natAbs + 1 : ℕ) : ℤ) ≤ |k - 1| := by
      calc (((k - 1).natAbs + 1 : ℕ) : ℤ) = 1 * (((k - 1).natAbs + 1 : ℕ) : ℤ) := by ring
        _ ≤ |m| * (((k - 1).natAbs + 1 : ℕ) : ℤ) :=
            mul_le_mul_of_nonneg_right h1m (le_of_lt hN)
        _ = |m * (((k - 1).natAbs + 1 : ℕ) : ℤ)| := by rw [abs_mul, abs_of_pos hN]
        _ = |k - 1| := by rw [← hm]
    have habs : |k - 1| = (((k - 1).natAbs : ℕ) : ℤ) := Int.abs_eq_natAbs _
    rw [habs] at hle
    push_cast at hle
    omega
  rw [hk, hk1]
  push_cast
  ring

/-- Consequently such a `Φ` fixes `π`. -/
theorem map_pi_of_expComm (Φ : ℂ →+* ℂ)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hcomm : ∀ z : ℂ, Φ (Complex.exp z) = Complex.exp (Φ z)) :
    Φ ((Real.pi : ℂ)) = (Real.pi : ℂ) := by
  have h := map_two_pi_I_of_expComm Φ hfix hcomm
  rw [map_mul, map_mul, map_ofNat, hfix I isAlgebraic_I] at h
  exact mul_left_cancel₀ (two_ne_zero) (mul_right_cancel₀ Complex.I_ne_zero h)

/-- A `Φ` commuting with `exp` maps logarithms of algebraic numbers to logarithms of
algebraic numbers: `ℒ` is stable. -/
theorem mapsTo_logAlg_of_expComm (Φ : ℂ →+* ℂ)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hcomm : ∀ z : ℂ, Φ (Complex.exp z) = Complex.exp (Φ z))
    {z : ℂ} (hz : z ∈ LogAlg) : Φ z ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (Φ z))
  rw [← hcomm, hfix _ hz]
  exact hz

/-! ## 5.  Why the obstruction bites: the invariant data is satisfiable -/

/-- `exp i` is transcendental, given Hermite–Lindemann.  (The mission's own
`transcendental_exp_I`; reproved here so that this file imports no stub.) -/
theorem transcendental_exp_I (hHL : HermiteLindemann) :
    Transcendental ℚ (Complex.exp I) :=
  hHL I Complex.I_ne_zero isAlgebraic_I

/-- The comparison point `r · exp i` is non-zero and transcendental. -/
theorem ordinaryPoint_transcendental (hHL : HermiteLindemann) (r : ℝ) (hr : r ≠ 0)
    (hra : IsAlgebraic ℚ ((r : ℝ) : ℂ)) :
    ((r : ℂ)) * Complex.exp I ≠ 0 ∧ Transcendental ℚ (((r : ℂ)) * Complex.exp I) := by
  have hrne : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr
  refine ⟨mul_ne_zero hrne (Complex.exp_ne_zero I), ?_⟩
  intro halg
  have hmem : (((r : ℂ)) * Complex.exp I) ∈ Qbar := mem_Qbar_iff.2 halg
  have hrmem : ((r : ℂ)) ∈ Qbar := mem_Qbar_iff.2 hra
  have hsplit : Complex.exp I = (((r : ℂ)) * Complex.exp I) * ((r : ℂ))⁻¹ := by
    field_simp
  have : IsAlgebraic ℚ (Complex.exp I) := by
    rw [hsplit, ← mem_Qbar_iff]
    exact mul_mem hmem (inv_mem hrmem)
  exact transcendental_exp_I hHL this

/-- The comparison point lies on the circle of radius `|r|`. -/
theorem ordinaryPoint_mul_conj (r : ℝ) :
    (((r : ℂ)) * Complex.exp I) * conj (((r : ℂ)) * Complex.exp I) = ((r : ℂ)) ^ 2 := by
  have hc : conj (((r : ℂ)) * Complex.exp I) = ((r : ℂ)) * Complex.exp (-I) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  have hone : Complex.exp I * Complex.exp (-I) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [hc]
  calc ((r : ℂ)) * Complex.exp I * (((r : ℂ)) * Complex.exp (-I))
      = ((r : ℂ)) ^ 2 * (Complex.exp I * Complex.exp (-I)) := by ring
    _ = ((r : ℂ)) ^ 2 := by rw [hone, mul_one]

/-- **The transfer-invariant data is satisfiable.**  For every non-zero real algebraic `r`
there is a point of the circle of radius `|r|` which is non-zero, transcendental, and
satisfies `t · conj t = r²` — the point `r · exp i`. -/
theorem exists_ordinary_point (hHL : HermiteLindemann) (r : ℝ) (hr : r ≠ 0)
    (hra : IsAlgebraic ℚ ((r : ℝ) : ℂ)) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental ℚ t ∧ t * conj t = ((r : ℂ)) ^ 2 :=
  ⟨((r : ℂ)) * Complex.exp I, (ordinaryPoint_transcendental hHL r hr hra).1,
    (ordinaryPoint_transcendental hHL r hr hra).2, ordinaryPoint_mul_conj r⟩

/-- The comparison point is off the axes, and being off the axes is itself a
transfer-invariant condition: `u.re ≠ 0` says `u + conj u ≠ 0` and `u.im ≠ 0` says
`u ≠ conj u`, both formulas of the invariant language.  So the obstruction applies
verbatim to the mission's off-axes leaf: adding that hypothesis costs it nothing.
(Contrast the real-generic leaf, whose extra hypothesis `(exp u).im = 0` is *not*
invariant — see the accompanying note.) -/
theorem exists_ordinary_point_offAxes (hHL : HermiteLindemann) (r : ℝ) (hr : r ≠ 0)
    (hra : IsAlgebraic ℚ ((r : ℝ) : ℂ)) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental ℚ t ∧ t * conj t = ((r : ℂ)) ^ 2 ∧
      t.re ≠ 0 ∧ t.im ≠ 0 := by
  have hre : (Complex.exp I).re = Real.cos 1 := by
    rw [Complex.exp_re]; simp
  have him : (Complex.exp I).im = Real.sin 1 := by
    rw [Complex.exp_im]; simp
  have hsin : Real.sin 1 ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three]))
  have hcos : Real.cos 1 ≠ 0 := ne_of_gt Real.cos_one_pos
  refine ⟨((r : ℂ)) * Complex.exp I, (ordinaryPoint_transcendental hHL r hr hra).1,
    (ordinaryPoint_transcendental hHL r hr hra).2, ordinaryPoint_mul_conj r, ?_, ?_⟩
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre]
    simpa using mul_ne_zero hr hcos
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him]
    simpa using mul_ne_zero hr hsin

/-- **No argument whose only inputs are the transfer-invariant data can refute a
candidate.**  Those data — non-vanishing, transcendence over `ℚ`, and the exact relation
`v · conj v = r²` — are jointly satisfiable, by `r · exp i`.  Any derivation of `False`
from them alone would therefore be unsound.

This is the unconditional content of the transfer obstruction: what makes the comparison
point useful is not that it is "ordinary" — nothing is claimed about `exp t` — but that it
*exists*. -/
theorem invariant_data_cannot_refute (hHL : HermiteLindemann) (r : ℝ) (hr : r ≠ 0)
    (hra : IsAlgebraic ℚ ((r : ℝ) : ℂ)) :
    ¬ (∀ v : ℂ, v ≠ 0 → Transcendental ℚ v → v * conj v = ((r : ℂ)) ^ 2 → False) := by
  intro h
  obtain ⟨t, ht0, httr, htc⟩ := exists_ordinary_point hHL r hr hra
  exact h t ht0 httr htc

/-- The same, for the off-axes leaf. -/
theorem invariant_data_cannot_refute_offAxes (hHL : HermiteLindemann) (r : ℝ) (hr : r ≠ 0)
    (hra : IsAlgebraic ℚ ((r : ℝ) : ℂ)) :
    ¬ (∀ v : ℂ, v ≠ 0 → Transcendental ℚ v → v * conj v = ((r : ℂ)) ^ 2 →
        v.re ≠ 0 → v.im ≠ 0 → False) := by
  intro h
  obtain ⟨t, ht0, httr, htc, hre, him⟩ := exists_ordinary_point_offAxes hHL r hr hra
  exact h t ht0 httr htc hre him

/-! ## Axiom check -/


end DiazObstructionShape

open Complex ComplexConjugate in
open DiazModulus in
theorem solution (Φ : ℂ →+* ℂ) (u : ℂ) (hu : IsCandidate u)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hconj : Φ (conj u) = conj (Φ u))
    (hnot : ¬ IsCandidate (Φ u)) :
    ‖Φ u‖ = ‖u‖ ∧
      Φ (Complex.exp u) ≠ Complex.exp (Φ u) ∧
      (∃ x : ℝ, (Φ (x : ℂ)).im ≠ 0) ∧
      (∃ z : ℂ, Φ (conj z) ≠ conj (Φ z)) ∧
      ¬ Continuous (Φ : ℂ → ℂ) ∧
      Φ ≠ RingHom.id ℂ ∧ Φ ≠ starRingEnd ℂ :=
  DiazObstructionShape.transfer_breaks_exactly Φ u hu hfix hconj hnot
