-- Prove2me | solution 1 for DiazModulus.sixExponentials_cannot_refute_candidate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T19:25:21.317323+00:00
-- url     : https://prove2.me/submissions/c6214a32-efcc-42ca-bbc3-d211d26077f8

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# Six exponentials cannot refute a candidate through the candidate's own certificate span

Let `u` be a candidate (`IsCandidate u`: `u ≠ 0`, `‖u‖` algebraic, `exp u` algebraic) and put
`c = u * conj u`, which is `‖u‖ ^ 2` and therefore a non-zero algebraic number.  Everything a
six- or four-exponentials argument can certify about `u` out of `u` alone lives in the
`Q̄`-subspace

  `V = span_Q̄ {1, u, conj u}`,

because `1 ∈ ℒ̃`, `u ∈ ℒ`, `conj u ∈ ℒ` (as `exp (conj u) = conj (exp u)`), and `c ∈ Q̄` is
already `Q̄ · 1`.  Clause (1) below records that `V ≤ ℒ̃`, so every entry drawn from `V` is a
legitimate `ℒ̃`-certificate.

A `2 × n` *template* is a pair of `Q̄`-linearly independent families `x : Fin 2 → ℂ`,
`y : Fin n → ℂ` all of whose `2n` products `x i * y j` are certified.  The six exponentials
theorems are the `n = 3` case, the four exponentials theorems the `n = 2` case.  The content
here is:

* **(3) no `2 × 3` template lands in `V`** — and this holds for *every* `u : ℂ`, with no
  hypothesis whatsoever.  So a six-exponentials argument whose entries are certified by
  membership in `V` cannot exist, let alone produce a contradiction from `IsCandidate u`.
* **(2) sharpness**: under Hermite–Lindemann `V` has `Q̄`-dimension exactly `3`, and the
  `2 × 2` template `x = (1, conj u)`, `y = (1, u)` — entries `1, u, conj u, c` — *does* land
  in `V`.  That is exactly the template used by the mission's proved
  `diaz_of_strongFourExponentials_and_hermite_lindemann`, so the no-go permits the
  configuration that demonstrably works and forbids the next one up.

## The mechanism, and why `dim V = 3` is the whole story

`x` independent forces `x 0 ≠ 0` and `s := x 1 / x 0 ∉ Q̄`.  Put `z j = x 0 * y j`.  If `y` is
independent so is `z`, so `span z` has dimension `n`; if `dim V ≤ n` this forces
`span z = V`, and then `s * V = s * span z ⊆ V` because `s * z j = x 1 * y j ∈ V`.  A non-zero
finitely generated `Q̄`-submodule of `ℂ` stable under multiplication by `s` makes `s` integral
over `Q̄`, hence algebraic over `ℚ`, hence in `Q̄` — contradiction.  With `n = 2` the step
`span z = V` fails (dimension `2 < 3`), which is precisely why the four exponentials template
survives.  The threshold is the dimension of the certificate space and nothing else.

## What this does not do

This is **not** the free-ring no-go of the mission's decomposition draft §5, and it does not
formalise that proof.  The draft's certificate space also contains the other elements of a
`ℚ`-basis of `ℒ`, so it is infinite dimensional and the dimension argument above says nothing
about it; the draft handles that by a gcd-and-degree computation in `Q̄[X, {T_b}]`.  Forbidding
`2 × 3` templates with entries anywhere in `ℒ̃` is not a weaker statement one could hope to
prove here — it *is* `StrongFourExponentials`'s six-variable sibling, i.e. the strong six
exponentials conjecture, and is open.  What is proved below is the `u`-generated fragment,
which is the fragment that is a theorem about `ℂ`.

Nothing here assumes a candidate exists.  Clause (3), the no-go proper, is unconditional in
`u`; only clauses (1) and (2), which describe the candidate's certificate space, are stated
under `IsCandidate u`.
-/

namespace DiazModulus

private theorem qbar_smul (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

private instance qbar_isAlgebraic : Algebra.IsAlgebraic ℚ (↥Qbar) := by
  refine ⟨fun a => ?_⟩
  have h : IsAlgebraic ℚ ((a : ℂ)) := mem_Qbar_iff.mp a.2
  have hinj : Function.Injective (algebraMap (↥Qbar) ℂ) := Subtype.val_injective
  exact (isAlgebraic_algebraMap_iff hinj).mp h

/-- A complex number that preserves a non-zero finitely generated `Q̄`-submodule of `ℂ`
is itself algebraic. -/
private theorem mem_Qbar_of_mul_mem {N : Submodule (↥Qbar) ℂ} (hN : N ≠ ⊥) (hfg : N.FG)
    {s : ℂ} (hs : ∀ n ∈ N, s * n ∈ N) : s ∈ Qbar := by
  have hint : IsIntegral (↥Qbar) s :=
    isIntegral_of_smul_mem_submodule N hN hfg s (by
      intro n hn
      simpa [smul_eq_mul] using hs n hn)
  have halg : IsAlgebraic (↥Qbar) s := hint.isAlgebraic
  exact mem_Qbar_iff.mpr (halg.restrictScalars ℚ)

/-- Scaling a `Q̄`-independent family by a non-zero complex number keeps it independent. -/
private theorem linearIndependent_const_mul {n : ℕ} {a : ℂ} (ha : a ≠ 0) {y : Fin n → ℂ}
    (hy : LinearIndependent (↥Qbar) y) : LinearIndependent (↥Qbar) (fun j => a * y j) := by
  rw [Fintype.linearIndependent_iff] at hy ⊢
  intro g hg j
  refine hy g ?_ j
  have : a * ∑ j, (g j : ℂ) * y j = 0 := by
    rw [Finset.mul_sum]
    simpa [qbar_smul, mul_left_comm, mul_assoc] using hg
  have h2 : ∑ j, (g j : ℂ) * y j = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha
    · exact h
  simpa [qbar_smul] using h2

/-- **The linear-algebraic core.**  If a `Q̄`-subspace `V` of `ℂ` has dimension at most `n`,
then no `2 × n` template lands inside it: there are no `Q̄`-independent families
`x : Fin 2 → ℂ` and `y : Fin n → ℂ` with all `2n` products `x i * y j` in `V`. -/
private theorem no_template_of_finrank_le {n : ℕ} (hn : 0 < n) {V : Submodule (↥Qbar) ℂ}
    [FiniteDimensional (↥Qbar) V] (hV : Module.finrank (↥Qbar) V ≤ n)
    {x : Fin 2 → ℂ} {y : Fin n → ℂ}
    (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (h : ∀ i j, x i * y j ∈ V) : False := by
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  set z : Fin n → ℂ := fun j => x 0 * y j with hz_def
  have hz : LinearIndependent (↥Qbar) z := linearIndependent_const_mul hx0 hy
  set N : Submodule (↥Qbar) ℂ := Submodule.span (↥Qbar) (Set.range z) with hN_def
  have hNle : N ≤ V := by
    rw [hN_def]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨j, rfl⟩
    exact h 0 j
  have hrankN : Module.finrank (↥Qbar) N = n := by
    rw [hN_def]
    simpa using finrank_span_eq_card (R := ↥Qbar) hz
  have hNV : N = V := Submodule.eq_of_le_of_finrank_le hNle (by rw [hrankN]; exact hV)
  -- the multiplier
  set s : ℂ := x 1 / x 0 with hs_def
  have hsz : ∀ j, s * z j = x 1 * y j := by
    intro j
    rw [hs_def, hz_def]
    field_simp
  have hstab : ∀ w ∈ N, s * w ∈ N := by
    have hle : N ≤ N.comap (LinearMap.mulLeft (↥Qbar) s) := by
      rw [hN_def]
      refine Submodule.span_le.mpr ?_
      rintro w ⟨j, rfl⟩
      have : s * z j ∈ N := by rw [hsz j, hNV]; exact h 1 j
      simpa [LinearMap.mulLeft_apply] using this
    intro w hw
    have := hle hw
    simpa [LinearMap.mulLeft_apply] using this
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hmem : z ⟨0, hn⟩ ∈ N := Submodule.subset_span ⟨⟨0, hn⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hz.ne_zero ⟨0, hn⟩ hmem
  have hsQ : s ∈ Qbar := mem_Qbar_of_mul_mem hNne (Submodule.fg_span (Set.finite_range z)) hstab
  -- `x 1 = s * x 0` with `s` algebraic contradicts independence of `x`
  rw [Fintype.linearIndependent_iff] at hx
  have := hx ![-(⟨s, hsQ⟩ : ↥Qbar), 1] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, qbar_smul]
    push_cast
    rw [hs_def]
    field_simp
    ring) 1
  simp at this

/-! ### The certificate span of a candidate -/

private theorem range_triple (a b c : ℂ) : Set.range ![a, b, c] = ({a, b, c} : Set ℂ) := by
  ext w
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private instance finiteDimensional_span_triple (a b c : ℂ) :
    FiniteDimensional (↥Qbar) (Submodule.span (↥Qbar) ({a, b, c} : Set ℂ)) :=
  FiniteDimensional.span_of_finite (↥Qbar) (Set.toFinite _)

private theorem finrank_span_triple_le (a b c : ℂ) :
    Module.finrank (↥Qbar) (Submodule.span (↥Qbar) ({a, b, c} : Set ℂ)) ≤ 3 := by
  rw [← range_triple a b c]
  simpa [Set.finrank] using finrank_range_le_card (R := ↥Qbar) ![a, b, c]

/-- Algebraicity over `ℚ` survives complex conjugation. -/
private theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hpz⟩ := h
  refine ⟨p, hp0, ?_⟩
  have hc := congrArg (starRingEnd ℂ) hpz
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, map_sum, Polynomial.sum]
    using hc

private theorem conj_mem_LogAlg {u : ℂ} (h : u ∈ LogAlg) : conj u ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (conj u))
  rw [Complex.exp_conj]
  exact isAlgebraic_conj h

private theorem mul_conj_mem_Qbar {u : ℂ} (hu : IsCandidate u) : u * conj u ∈ Qbar := by
  have hnorm : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr hu.2.1
  have key : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [key]
  exact pow_mem hnorm 2

private theorem pair_one_independent {w : ℂ} (hw : w ∉ Qbar) :
    LinearIndependent (↥Qbar) ![(1 : ℂ), w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [qbar_smul, mul_one] at hst
  by_cases ht : (t : ℂ) = 0
  · rw [ht, zero_mul, add_zero] at hst
    exact ⟨Subtype.ext hst, Subtype.ext ht⟩
  · exact absurd (by
      have : w = -(s : ℂ) / (t : ℂ) := by field_simp; linear_combination hst
      rw [this]
      exact div_mem (neg_mem s.2) t.2) hw

/-- A complex number satisfying a monic quadratic over `Q̄` is algebraic:
`Q̄ · 1 + Q̄ · w` is then stable under multiplication by `w`. -/
private theorem mem_Qbar_of_sq {w : ℂ} (a b : ↥Qbar) (h : w ^ 2 = (a : ℂ) * w + (b : ℂ)) :
    w ∈ Qbar := by
  set N : Submodule (↥Qbar) ℂ := Submodule.span (↥Qbar) ({1, w} : Set ℂ) with hN_def
  have hone : (1 : ℂ) ∈ N := Submodule.subset_span (by simp)
  have hw : w ∈ N := Submodule.subset_span (by simp)
  have hstab : ∀ m ∈ N, w * m ∈ N := by
    have hle : N ≤ N.comap (LinearMap.mulLeft (↥Qbar) w) := by
      rw [hN_def]
      refine Submodule.span_le.mpr ?_
      rintro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with h1 | h1
      · rw [h1]
        simpa [LinearMap.mulLeft_apply] using hw
      · rw [h1]
        have hsq : w * w ∈ N := by
          have hww : w * w = a • w + b • (1 : ℂ) := by
            simp only [qbar_smul, mul_one]
            linear_combination h
          rw [hww]
          exact N.add_mem (N.smul_mem a hw) (N.smul_mem b hone)
        simpa [LinearMap.mulLeft_apply] using hsq
    intro m hm
    simpa [LinearMap.mulLeft_apply] using hle hm
  have hNne : N ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hone
    exact one_ne_zero hone
  exact mem_Qbar_of_mul_mem hNne (Submodule.fg_span (Set.toFinite _)) hstab

/-- For a candidate `u`, the certificate generators `1`, `u`, `conj u` are `Q̄`-independent,
so the certificate span has `Q̄`-dimension exactly `3`. -/
private theorem candidate_triple_independent {u : ℂ} (hu : IsCandidate u)
    (hHL : HermiteLindemann) : LinearIndependent (↥Qbar) ![(1 : ℂ), u, conj u] := by
  obtain ⟨hu0, hmod, hexp⟩ := hu
  have huQ : u ∉ Qbar := fun h => hHL u hu0 (mem_Qbar_iff.mp h) hexp
  have hcuQ : conj u ∉ Qbar := by
    intro h
    exact huQ (by
      have := mem_Qbar_iff.mpr (isAlgebraic_conj (mem_Qbar_iff.mp h))
      simpa using this)
  have hc : u * conj u ∈ Qbar := mul_conj_mem_Qbar ⟨hu0, hmod, hexp⟩
  have hcu0 : conj u ≠ 0 := by simpa using hu0
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hrel : (g 0 : ℂ) + (g 1 : ℂ) * u + (g 2 : ℂ) * conj u = 0 := by
    rw [Fin.sum_univ_three] at hg
    simpa [qbar_smul] using hg
  have hB : (g 1 : ℂ) = 0 := by
    by_contra hBne
    refine huQ (mem_Qbar_of_sq (⟨-(g 0 : ℂ) / (g 1 : ℂ), div_mem (neg_mem (g 0).2) (g 1).2⟩)
      (⟨-((g 2 : ℂ) * (u * conj u)) / (g 1 : ℂ),
        div_mem (neg_mem (mul_mem (g 2).2 hc)) (g 1).2⟩) ?_)
    have hq : u ^ 2 * (g 1 : ℂ) = -(g 0 : ℂ) * u - (g 2 : ℂ) * (u * conj u) := by
      linear_combination u * hrel
    show u ^ 2 = (-(g 0 : ℂ) / (g 1 : ℂ)) * u + -((g 2 : ℂ) * (u * conj u)) / (g 1 : ℂ)
    have hrw : (-(g 0 : ℂ) / (g 1 : ℂ)) * u + -((g 2 : ℂ) * (u * conj u)) / (g 1 : ℂ)
        = (u ^ 2 * (g 1 : ℂ)) / (g 1 : ℂ) := by
      rw [hq]; ring
    rw [hrw, mul_div_assoc, div_self hBne, mul_one]
  have hrel2 : (g 0 : ℂ) + (g 2 : ℂ) * conj u = 0 := by
    rw [hB] at hrel; linear_combination hrel
  have hA : (g 0 : ℂ) = 0 := by
    by_contra hAne
    have hCne : (g 2 : ℂ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, add_zero] at hrel2
      exact hAne hrel2
    refine hcuQ ?_
    have : conj u = -(g 0 : ℂ) / (g 2 : ℂ) := by field_simp; linear_combination hrel2
    rw [this]
    exact div_mem (neg_mem (g 0).2) (g 2).2
  have hC : (g 2 : ℂ) = 0 := by
    rw [hA, zero_add] at hrel2
    rcases mul_eq_zero.mp hrel2 with h0 | h0
    · exact h0
    · exact absurd h0 hcu0
  fin_cases i
  · exact ZeroMemClass.coe_eq_zero.mp hA
  · exact ZeroMemClass.coe_eq_zero.mp hB
  · exact ZeroMemClass.coe_eq_zero.mp hC

/-! ### The no-go theorem -/

theorem sixExponentials_cannot_refute_candidate_aux (u : ℂ) :
    (IsCandidate u → Submodule.span Qbar ({1, u, conj u} : Set ℂ) ≤ LogAlgTilde) ∧
    (IsCandidate u → HermiteLindemann →
      Module.finrank Qbar (Submodule.span Qbar ({1, u, conj u} : Set ℂ)) = 3 ∧
      ∃ x y : Fin 2 → ℂ,
        LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) ∧
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x →
      LinearIndependent (↥Qbar) y →
      ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) := by
  set V : Submodule (↥Qbar) ℂ := Submodule.span Qbar ({1, u, conj u} : Set ℂ) with hV_def
  have hone : (1 : ℂ) ∈ V := Submodule.subset_span (by simp)
  have huV : u ∈ V := Submodule.subset_span (by simp)
  have hcuV : conj u ∈ V := Submodule.subset_span (by simp)
  refine ⟨?_, ?_, ?_⟩
  -- (1) for a candidate the span is a legitimate certificate space: it lies inside `ℒ̃`
  · rintro ⟨hu0, hmod, hexp⟩
    refine Submodule.span_le.mpr ?_
    rintro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ hexp)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (conj_mem_LogAlg hexp))
  -- (2) sharpness: the span is exactly `3`-dimensional and the working `2 × 2` template fits
  · rintro ⟨hu0, hmod, hexp⟩ hHL
    have hrank : Module.finrank Qbar (Submodule.span Qbar ({1, u, conj u} : Set ℂ)) = 3 := by
      rw [← range_triple (1 : ℂ) u (conj u)]
      simpa using
        finrank_span_eq_card (R := ↥Qbar) (candidate_triple_independent ⟨hu0, hmod, hexp⟩ hHL)
    refine ⟨hrank, ?_⟩
    have huQ : u ∉ Qbar := fun h => hHL u hu0 (mem_Qbar_iff.mp h) hexp
    have hcuQ : conj u ∉ Qbar := by
      intro h
      exact huQ (by
        have := mem_Qbar_iff.mpr (isAlgebraic_conj (mem_Qbar_iff.mp h))
        simpa using this)
    refine ⟨![1, conj u], ![1, u], pair_one_independent hcuQ, pair_one_independent huQ, ?_⟩
    intro i j
    have hc : conj u * u ∈ V := by
      have hq : conj u * u ∈ Qbar := by
        have := mul_conj_mem_Qbar ⟨hu0, hmod, hexp⟩
        rw [mul_comm] at this
        exact this
      have := Submodule.smul_mem V (⟨conj u * u, hq⟩ : ↥Qbar) hone
      simpa [qbar_smul] using this
    fin_cases i <;> fin_cases j
    · simpa using hone
    · simpa using huV
    · simpa using hcuV
    · simpa using hc
  -- (3) the no-go: no `2 × 3` template fits — and this needs no hypothesis on `u` at all
  · intro x y hx hy hcon
    exact no_template_of_finrank_le (by norm_num)
      (finrank_span_triple_le (1 : ℂ) u (conj u)) hx hy (fun i j => hcon i j)

end DiazModulus

open DiazModulus in
theorem solution (u : ℂ) :
    (IsCandidate u → Submodule.span Qbar ({1, u, conj u} : Set ℂ) ≤ LogAlgTilde) ∧
    (IsCandidate u → HermiteLindemann →
      Module.finrank Qbar (Submodule.span Qbar ({1, u, conj u} : Set ℂ)) = 3 ∧
      ∃ x y : Fin 2 → ℂ,
        LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) ∧
    (∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x →
      LinearIndependent (↥Qbar) y →
      ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :=
  DiazModulus.sixExponentials_cannot_refute_candidate_aux u
