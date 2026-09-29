-- Prove2me | solution 1 for DirichletLFunctions.LFunction_center_lower
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:58:15.000519+00:00
-- url     : https://prove2.me/submissions/a8b83ca4-67d0-4868-bce7-1cece0694259

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.SW.ZeroCount =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, wave S2 — the L'/L zero-counting cluster

Design: `docs/blueprints/sw.md`, wave S2 (the L'/L partial-fractions + zero-counting
cluster, the technical heart's first half). This module lands the *mathlib-first*
pieces of the classical Davenport §12–13 zero-counting apparatus for Dirichlet
L-functions, uniform in the modulus `q`.

Namespace `Salt.SW`; independent of `Salt/SW/Psi1Identity.lean`. Depends only on
mathlib (analytic continuation of L-functions, Jensen/Nevanlinna, Borel–Carathéodory,
the Cauchy derivative estimate) and on the corpus nowhere — a self-contained slice.

## What landed here

The classical setup normalizes the disks at `s₀ = 1 + it₀` by working from the
comfortable center `c = 2 + it₀` (where `Re s = 2 > 1`, so the Dirichlet series
converges and `L` is bounded below by an absolute constant), counting zeros in a
smaller disk that reaches down toward the 1-line.

* **The center lower bound** (`LFunction_center_lower`, the `‖L(2+it,χ)‖ ≥ 2 − ζ(2)`
  input, sharpened to the clean explicit constant `1/4`). For `Re s ≥ 2` and *any*
  `χ` (trivial or not), `1/4 ≤ ‖L(s,χ)‖`. Route: on `Re s > 1`,
  `L(s,χ) = ∑ₙ χ(n)/nˢ` (`LFunction_eq_LSeries`); split off the `n = 1` term (`= 1`)
  and bound the tail `‖∑_{n≥2} χ(n)/nˢ‖ ≤ ∑_{n≥2} 1/n² = π²/6 − 1` via
  `hasSum_zeta_two`; then `‖L‖ ≥ 1 − (π²/6 − 1) = 2 − π²/6 ≥ 1/4` (using `π < 3.15`).
  This is the nonvanishing-at-center hypothesis Jensen's inequality consumes.

* **Z2 — the Jensen zero count** (`LFunction_zero_count_le`, the S2 keystone). For a
  nontrivial `χ` and `0 < r < R`, if `‖L(·,χ)‖ ≤ M` (with `M ≥ 1`) on the sphere
  `|s − (2+it₀)| = R`, then the number of zeros of `L(·,χ)` in the disk
  `|s − (2+it₀)| ≤ r`, counted with multiplicity, is `≤ log(4M)/log(R/r)`. Route:
  mathlib's Nevanlinna consumption `AnalyticOnNhd.sum_divisor_le` (`L` is entire for
  `χ ≠ 1` by `differentiable_LFunction`; the center value is bounded below by the
  clause above, folded into the `4M`). The sup-bound `M` is left as a *hypothesis*
  — this is exactly the Z1 interface (see below): once the classical growth bound
  `M = C·(q(2+|t|))ᴬ` lands, feeding it here gives the `≤ C·log(q(2+|t₀|))` count.

* **The reusable Borel–Carathéodory derivative bound** (`norm_deriv_le_of_re_le`,
  the abstract "Landau lemma" for Z3). For `g` analytic on `‖z‖ < R` with `g 0 = 0`
  and `Re(g z) ≤ M`, and any center `w` with `‖w‖ ≤ ρ` and `ρ + s < R`,
  `‖g'(w)‖ ≤ 2M(ρ+s) / (s(R−ρ−s))`. Route: mathlib's `borelCaratheodory_zero`
  bounds `‖g‖` on the mid-disk, and the Cauchy estimate
  `norm_deriv_le_of_forall_mem_sphere_norm_le` (a circle of radius `s` about `w`,
  which stays inside `‖z‖ < R`) converts that sup-bound into the derivative bound.
  This is the L-independent heart of Z3's log-derivative partial-fraction estimate:
  applied to `g = log(L(·,χ)/L(c,χ))` (whose derivative is `L'/L`) it yields the
  `−Re(L'/L) ≤ −Σ_ρ Re(1/(s−ρ)) + O(log q(|t|+2))` bound.

## What is flagged (precise next-node specs for future sessions)

* **Z1 — the growth bound** `‖L(s,χ)‖ ≤ C·q·(2+|t|)` (for `Re s ≥ δ`, the disks that
  dip below the 1-line). This is the honest analytic gap: it needs Pólya–Vinogradov
  partial summation `L(s,χ) = s·∫₁^∞ Sχ(u)·u^{−s−1} du` (with `Sχ(u) = ∑_{n≤u} χ(n)`,
  `‖Sχ‖ ≤ √q(1+log q)` from the *landed* `Salt.BV.polya_vinogradov`) analytically
  continued to `Re s > 0` and identified with mathlib's `LFunction χ` by the identity
  theorem. The corpus PV lemma is ready, but the Abel-summation-of-an-L-series-to-its-
  continuation plumbing is a from-scratch multi-lemma build (mathlib's L-series
  machinery here is Hurwitz-zeta-based, and the corpus `Salt/LS/*` L-series tooling
  is large-sieve oriented, not growth-bound oriented). Left as the `M`-hypothesis of
  `LFunction_zero_count_le`.

* **Z3 — the L-specific assembly**: constructing the analytic branch
  `g = log(L(·,χ)/L(c,χ))` on the zero-free-by-construction disk (finitely many zeros
  factored out via Z2) and identifying `deriv g = L'/L − Σ_ρ 1/(s−ρ)`, then invoking
  `norm_deriv_le_of_re_le` above. The reusable derivative bound is landed; the analytic-
  logarithm construction (a primitive of `L'/L` on a simply-connected domain) is the
  flagged plumbing.

* **The χ₀ (principal character) variant** of Z2. `LFunction_zero_count_le` requires
  `χ ≠ 1` (`differentiable_LFunction`). For the trivial character the pole at `s = 1`
  enters the disk; mirror mathlib's `LFunctionTrivChar₁` (the entire pole-stripped
  object `(s−1)·L`, `Differentiable` by `differentiable_LFunctionTrivChar₁`), whose
  own center lower bound at `2+it₀` needs the `(s−1)·∏(1−p^{−s})·ζ(s)` factorization.
-/

namespace Salt.SW

open Complex Metric DirichletCharacter
open scoped LSeries.notation

/-! ## 1. The center lower bound (the nonvanishing input for Jensen) -/

/-- **The center lower bound** (the classical `‖L(2+it,χ)‖ ≥ 2 − ζ(2)`, sharpened to
the clean explicit constant `1/4`). For `Re s ≥ 2` and *any* Dirichlet character `χ`
(trivial or not), `1/4 ≤ ‖L(s,χ)‖`.

On `Re s > 1` the L-function is the Dirichlet series `∑ₙ χ(n)/nˢ` (`LFunction_eq_LSeries`);
the `n = 1` term is `1`, and the tail obeys
`‖∑_{n≥2} χ(n)/nˢ‖ ≤ ∑_{n≥2} 1/n² = π²/6 − 1` (via `hasSum_zeta_two` and `‖χ(n)‖ ≤ 1`),
so `‖L‖ ≥ 1 − (π²/6 − 1) = 2 − π²/6 ≥ 1/4` (using `π < 3.15`). This is the lower bound
on `‖L(c,·)‖` at the center `c = 2 + it₀` that Jensen's inequality consumes. -/
theorem LFunction_center_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 2 ≤ s.re) : (1 : ℝ) / 4 ≤ ‖LFunction χ s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hLS : LFunction χ s = LSeries (χ ·) s := LFunction_eq_LSeries χ hs1
  have hsum : LSeriesSummable (χ ·) s := LSeriesSummable_of_one_lt_re χ hs1
  set g : ℕ → ℂ := LSeries.term (χ ·) s with hg
  have hgsum : Summable g := hsum
  set T : ℂ := ∑' n, g (n + 2) with hT
  have hg0 : g 0 = 0 := LSeries.term_zero _ _
  have hg1 : g 1 = 1 := by rw [hg, LSeries.term_of_ne_zero (by norm_num)]; simp
  have hrange2 : (∑ i ∈ Finset.range 2, g i) = 1 := by
    simp [Finset.sum_range_succ, hg0, hg1]
  have hsum_eq : (∑ i ∈ Finset.range 2, g i) + T = ∑' n, g n := by
    rw [hT]; exact hgsum.sum_add_tsum_nat_add 2
  have hL1T : LFunction χ s = 1 + T := by
    rw [hLS]
    have hdef : LSeries (χ ·) s = ∑' n, g n := rfl
    rw [hdef, ← hsum_eq, hrange2]
  -- termwise tail bound `‖g (n+2)‖ ≤ 1/(n+2)²`
  have hterm_le : ∀ n : ℕ, ‖g (n + 2)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hbase : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hpow : ((n : ℝ) + 2) ^ (2 : ℝ) ≤ ((n : ℝ) + 2) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    have hstep1 : ‖g (n + 2)‖ ≤ 1 / ((n : ℝ) + 2) ^ s.re := by
      rw [hg, LSeries.norm_term_eq, if_neg (by omega), hcast]
      have hnb : ‖χ ((n + 2 : ℕ) : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      gcongr
    have hstep2 : (1 : ℝ) / ((n : ℝ) + 2) ^ s.re ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
      rw [← Real.rpow_two]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) 2) hpow
    exact le_trans hstep1 hstep2
  -- the dominating tail sums to `π²/6 − 1`
  have hzsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have htailsum : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) ^ 2) := by
    have h := (summable_nat_add_iff 2).mpr hzsum
    refine h.congr (fun n => ?_); congr 1; push_cast; ring
  have htailVal : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2) = Real.pi ^ 2 / 6 - 1 := by
    have hz : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    have hshift := hzsum.sum_add_tsum_nat_add 2
    have hr2 : (∑ i ∈ Finset.range 2, (1 : ℝ) / (i : ℝ) ^ 2) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]; norm_num
    have hcong : (∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2)
        = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2 := by
      refine tsum_congr (fun n => ?_); congr 1; push_cast; ring
    rw [hr2, hcong, hz] at hshift
    linarith
  have hnormsum : Summable (fun n : ℕ => ‖g (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le htailsum
  have hTnorm : ‖T‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    calc ‖T‖ = ‖∑' n, g (n + 2)‖ := by rw [hT]
      _ ≤ ∑' n, ‖g (n + 2)‖ := norm_tsum_le_tsum_norm hnormsum
      _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2 := hnormsum.tsum_le_tsum hterm_le htailsum
      _ = Real.pi ^ 2 / 6 - 1 := htailVal
  -- assemble: `‖1 + T‖ ≥ 1 − ‖T‖ ≥ 2 − π²/6 ≥ 1/4`
  have heq : (1 : ℂ) + T + -T = 1 := by ring
  have hle := norm_add_le ((1 : ℂ) + T) (-T)
  rw [heq, norm_neg, norm_one] at hle
  rw [hL1T]
  have hpisq : Real.pi ^ 2 < 10.5 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  linarith [hle, hTnorm]

/-! ## 2. Z2 — the Jensen zero count -/

open MeromorphicOn in
/-- **Z2 — the Jensen zero count** (the S2 keystone). For a nontrivial Dirichlet
character `χ` and radii `0 < r < R`, if `‖L(·,χ)‖ ≤ M` (with `1 ≤ M`) on the sphere
`|s − (2+it₀)| = R`, then the number of zeros of `L(·,χ)` in the disk
`|s − (2+it₀)| ≤ r`, counted with multiplicity (the `MeromorphicOn.divisor`
finsum), is `≤ log(4M)/log(R/r)`.

Route: `L(·,χ)` is entire for `χ ≠ 1` (`differentiable_LFunction`), hence
`AnalyticOnNhd` on the closed disk; mathlib's Nevanlinna estimate
`AnalyticOnNhd.sum_divisor_le` bounds the zero count by `log(M/‖L(c,χ)‖)/log(R/r)`,
and the center value `‖L(c,χ)‖ ≥ 1/4` (`LFunction_center_lower`, at `Re c = 2`) folds
the denominator into the clean `4M`. The sup-bound `M` is a hypothesis — it is the
Z1 growth-bound interface (see the module docstring's flag); feeding `M = C(q(2+|t|))ᴬ`
yields the classical `≤ C log(q(2+|t₀|))` count uniform in `q`. -/
theorem LFunction_zero_count_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t₀ : ℝ) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hbnd : ∀ z ∈ sphere (2 + (t₀ : ℂ) * I) R, ‖LFunction χ z‖ ≤ M) :
    ((∑ᶠ u, divisor (LFunction χ) (closedBall (2 + (t₀ : ℂ) * I) r) u : ℤ) : ℝ)
      ≤ Real.log (4 * M) / Real.log (R / r) := by
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  have hcre : c.re = 2 := by rw [hc]; simp
  have hRpos : 0 < R := hr.trans hrR
  have habsr : |r| = r := abs_of_pos hr
  have habsR : |R| = R := abs_of_pos hRpos
  have hcenter : (1 : ℝ) / 4 ≤ ‖LFunction χ c‖ := LFunction_center_lower χ (le_of_eq hcre.symm)
  have hcnorm : (0 : ℝ) < ‖LFunction χ c‖ := by linarith
  have hcne : LFunction χ c ≠ 0 := by
    intro h; rw [h, norm_zero] at hcnorm; exact lt_irrefl 0 hcnorm
  have hdiff : DifferentiableOn ℂ (LFunction χ) Set.univ :=
    (differentiable_LFunction hχ).differentiableOn
  have hana : AnalyticOnNhd ℂ (LFunction χ) (closedBall c |R|) :=
    (hdiff.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hjensen := hana.sum_divisor_le (by rw [habsr]; exact hr) (by rw [habsr, habsR]; exact hrR)
    hM hcne (by rw [habsR]; exact hbnd)
  rw [habsr] at hjensen
  refine le_trans hjensen ?_
  have hRr : 1 < R / r := (one_lt_div hr).mpr hrR
  have hlogpos : 0 < Real.log (R / r) := Real.log_pos hRr
  have hMpos : (0 : ℝ) < M := by linarith
  have hle1 : M / ‖LFunction χ c‖ ≤ 4 * M := by
    rw [div_le_iff₀ hcnorm]; nlinarith [hcenter, hMpos]
  have hlog : Real.log (M / ‖LFunction χ c‖) ≤ Real.log (4 * M) :=
    Real.log_le_log (div_pos hMpos hcnorm) hle1
  rw [div_le_div_iff_of_pos_right hlogpos]
  exact hlog

/-! ## 3. The reusable Borel–Carathéodory derivative bound (Landau lemma for Z3) -/

/-- **The Borel–Carathéodory derivative bound** (the reusable abstract "Landau lemma"
for Z3). For `g` analytic on the open disk `‖z‖ < R` with `g 0 = 0` and real part
bounded, `Re(g z) ≤ M` (with `0 < M`), and any evaluation point `w` with `‖w‖ ≤ ρ`
where `ρ + s < R` and `0 < s`,
`‖g'(w)‖ ≤ 2M(ρ+s) / (s(R − ρ − s))`.

Route: mathlib's `borelCaratheodory_zero` bounds `‖g‖ ≤ 2M‖z‖/(R−‖z‖)` on the disk,
which on the circle `|z − w| = s` (contained in `‖z‖ < R` since `‖z‖ ≤ ρ + s < R`)
is `≤ 2M(ρ+s)/(R−ρ−s)`; the Cauchy estimate
`norm_deriv_le_of_forall_mem_sphere_norm_le` divides by `s` to bound `‖g'(w)‖`.

This is the L-independent heart of the classical log-derivative partial-fraction
estimate (Z3): applied to `g = log(L(·,χ)/L(c,χ))` — whose derivative is `L'/L`, with
the finitely many nearby zeros (counted by `LFunction_zero_count_le`) factored out so
`g` is analytic and its real part is `log(‖L‖/‖L(c)‖)`, bounded by Z1+Z2 — it delivers
`‖L'/L − Σ_ρ 1/(s−ρ)‖ ≤ C·log(q(|t₀|+2))`. The L-specific `g`-construction (the
analytic-logarithm plumbing) is the flagged remainder. -/
theorem norm_deriv_le_of_re_le {g : ℂ → ℂ} {M R ρ s : ℝ} {w : ℂ}
    (hM : 0 < M) (hdiff : DifferentiableOn ℂ g (ball 0 R))
    (hg0 : g 0 = 0) (hgM : ∀ z ∈ ball (0 : ℂ) R, (g z).re ≤ M)
    (hs : 0 < s) (hw : ‖w‖ ≤ ρ) (hlt : ρ + s < R) :
    ‖deriv g w‖ ≤ 2 * M * (ρ + s) / (s * (R - ρ - s)) := by
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg w) hw
  have hRpos : 0 < R := by linarith
  have hmaps : Set.MapsTo g (ball (0 : ℂ) R) {z | z.re ≤ M} := fun z hz => hgM z hz
  -- the circle of radius `s` about `w` stays inside `‖z‖ < R`
  have hsub : closedBall w s ⊆ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
      have := norm_add_le w (z - w); rwa [show w + (z - w) = z by ring] at this
    linarith
  have hdcc : DiffContOnCl ℂ g (ball w s) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w hs.ne']
    exact hdiff.mono hsub
  -- boundary bound via Borel–Carathéodory
  have hC : ∀ z ∈ sphere w s, ‖g z‖ ≤ 2 * M * (ρ + s) / (R - ρ - s) := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hzball : z ∈ ball (0 : ℂ) R :=
      hsub (by rw [mem_closedBall, dist_eq_norm]; exact le_of_eq hz)
    have hbc := Complex.borelCaratheodory_zero hM hdiff hmaps hRpos hzball hg0
    have hznorm : ‖z‖ ≤ ρ + s := by
      have h1 : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
        have := norm_add_le w (z - w); rwa [show w + (z - w) = z by ring] at this
      linarith
    have hzlt : ‖z‖ < R := by rw [mem_ball, dist_zero_right] at hzball; exact hzball
    have hd1 : (0 : ℝ) < R - ‖z‖ := by linarith
    have hd2 : (0 : ℝ) < R - ρ - s := by linarith
    calc ‖g z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := hbc
      _ ≤ 2 * M * (ρ + s) / (R - ρ - s) := by
          rw [div_le_div_iff₀ hd1 hd2]
          have hprod : (0 : ℝ) ≤ 2 * M * R * (ρ + s - ‖z‖) :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM.le) hRpos.le) (by linarith)
          nlinarith [hprod]
  -- Cauchy estimate at `w`
  have hfin := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs hdcc hC
  calc ‖deriv g w‖ ≤ 2 * M * (ρ + s) / (R - ρ - s) / s := hfin
    _ = 2 * M * (ρ + s) / (s * (R - ρ - s)) := by rw [div_div, mul_comm (R - ρ - s) s]

end Salt.SW

end




section
open Complex Metric DirichletCharacter
open scoped LSeries.notation

theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 2 ≤ s.re) : (1 : ℝ) / 4 ≤ ‖LFunction χ s‖ := by
  apply Salt.SW.LFunction_center_lower <;> assumption

end

