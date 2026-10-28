-- Prove2me | solution 1 for DiffractionCore.gammaR_analyticAt_of_im_ne
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:33:29.987982+00:00
-- url     : https://prove2.me/submissions/9b1dc157-7b9c-4cde-90e6-73a56f5b9c78

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- TURING RUNG T2, brick 1: the Riemann–Siegel theta function, defined BRANCH-CUT-FREE as the
   integral of an explicit real integrand (TURING_METHOD_SCOPING §3, rung T2).

   Classically `θ(t) = Im logΓ(1/4 + it/2) − (t/2)·log π` with a continuously-tracked branch of
   `logΓ` — awkward to formalize.  Instead we DEFINE

     `θ(t) := ∫_0^t ( (1/2)·Re ψ(1/4 + i·u/2) − (1/2)·log π ) du`,

   where `ψ = Complex.digamma = logDeriv Γ` (Mathlib).  This agrees with the classical `θ`
   (both vanish at `0` and have the same derivative `θ'(u) = (1/2)·Re ψ(1/4 + iu/2) − (1/2)·log π`)
   and needs NO branch tracking: the integrand is a plain continuous real function of `u`.

   This brick: the ray `1/4 + (u/2)·i` avoids all Γ-poles (`Re = 1/4 > 0`), Γ is ANALYTIC there
   (differentiable on the open right half-plane ⟹ analytic), `ψ` is continuous on the ray
   (`deriv Γ / Γ`, with `Γ ≠ 0` by `Gamma_ne_zero_of_re_pos`), hence the integrand is continuous,
   `θ` is well-defined with `θ(0) = 0` and `θ' = integrand` (FTC for continuous integrands).

   Later bricks (T2 cont.): effective two-sided bounds `θ(t) = (t/2)log(t/2π) − t/2 − π/8 +
   O*(explicit/t)` via Binet-type digamma estimates; then T3 wires `θ` into the rectangle
   argument identity `N(T) = θ(T)/π + 1 + S(T)`.

   conjecture1_proved = False. -/


open Complex

namespace ZeroFreeBridge























/-! ## Brick 2: the Archimedean bridge — `θ'` IS the `Gammaℝ` log-derivative on the critical line.

`Gammaℝ s = π^(-s/2)·Γ(s/2)` is the Archimedean factor of the completed zeta
(`Λ = Gammaℝ · ζ` up to the `s(s-1)` polynomial), the object the T3 rectangle identity
splits off of `logDeriv Λ`.  We compute `logDeriv Gammaℝ s = -(log π)/2 + (1/2)·ψ(s/2)`
on `Re(s/2) > 0` and specialize to the critical line `s = 1/2 + iu`, where `s/2 = thetaRay u`:
the θ integrand is EXACTLY `Re (logDeriv Gammaℝ (1/2 + iu))`.  This hard-wires the
branch-cut-free `θ` into the counting formula's Archimedean term. -/



theorem gammaRArch_exp :
    gammaRArch = fun z => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) :=
  funext fun z => Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) _

theorem gammaRArch_hasDerivAt (s : ℂ) :
    HasDerivAt gammaRArch
      (Complex.exp (Complex.log (Real.pi : ℂ) * (-s / 2))
        * (Complex.log (Real.pi : ℂ) * (-(1 / 2)))) s := by
  rw [gammaRArch_exp]
  have hL : HasDerivAt (fun z : ℂ => Complex.log (Real.pi : ℂ) * (-z / 2))
      (Complex.log (Real.pi : ℂ) * (-(1 / 2))) s := by
    have hbase : HasDerivAt (fun z : ℂ => -z / 2) (-(1 / 2) : ℂ) s := by
      have h1 : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) s := (hasDerivAt_id s).neg
      have h2 := h1.div_const 2
      norm_num at h2
      exact h2
    exact hbase.const_mul _
  exact hL.cexp









/-! ## Brick 3a: the θ-asymptotics skeleton (T2 rung, first sub-brick).

Target (brick 3 complete): `θ(t) = (t/2)·log(t/(2π)) − t/2 − π/8 + O*(explicit/t)`.
This sub-brick ships the three UNCONDITIONAL pieces every derivation route needs:

  * `digamma_shift` — the iterated recursion `ψ(s+N) = ψ(s) + Σ_{k<N} (s+k)⁻¹` (from Mathlib's
    single-step `digamma_apply_add_one`), which moves the evaluation point right, where the
    Stirling comparison is easy;
  * `norm_inv_sub_log_one_add_inv_le` — the telescoping step bound
    `‖s⁻¹ − log(1+s⁻¹)‖ ≤ ‖s⁻¹‖²·(1−‖s⁻¹‖)⁻¹/2` (Mathlib `norm_log_one_add_sub_self_le`):
    the summand of the Binet-series `ψ(s) − log s = −Σ_{k≥0} [(s+k)⁻¹ − log(1+(s+k)⁻¹)] + …`
    is quadratically small, so the telescoped series converges with an explicit `O(1/‖s‖)` tail;
  * `thetaMain` + `thetaMain_hasDerivAt` — the main term and its derivative
    `(log(t/(2π)))/2`, matching `θ'`'s leading behaviour, so brick 3c can compare the two via
    FTC on `[t₀, t]`.

Remaining sub-bricks: 3b = sum the telescoped series (Summable + tail bound ⟹ effective
`|ψ(s) − log s| ≤ C/‖s‖` on `Re s ≥ 1`, plus the anchor `ψ(s+N) − log(s+N) → 0`); 3c = integrate
`θ' − thetaMain'` and fix the `−π/8` constant.  conjecture1_proved = False. -/













/-! ## Brick 3b: the telescoped Binet series — `|ψ(s) − log s| ≤ 1/(Re s − 1)` modulo the anchor.

Telescoping `d(s) = ψ(s) − log s` with `d(s+1) − d(s) = s⁻¹ − log(1+s⁻¹)` (branch-safe on
`Re s > 0` since `|arg| < π/2` on the right half-plane) gives the FINITE identity
`d(s) = d(s+N) − Σ_{k<N} [(s+k)⁻¹ − log(1+(s+k)⁻¹)]`; the 3a step bound + an elementary
inline telescoping estimate `Σ_{k<N} 1/(x+k)² ≤ 1/(x−1)` bound the sum UNIFORMLY in `N`;
letting `N → ∞` against the anchor `d(s+N) → 0` (the ONE remaining analytic input, carried as
an explicit hypothesis — brick 3b′ discharges it) yields the effective Binet bound.
conjecture1_proved = False. -/













/-! ## Brick 3b′-i: the INTEGER anchor — `ψ(1+N) − log(1+N) → 0`.

The first of the anchor's three sub-bricks (3b′ plan: (i) integer anchor via the Euler–Mascheroni
limit, (ii) real-axis sandwich via `ψ` monotonicity (log-convexity of `Γ`) killing the 1-periodic
ambiguity `L(s+1) = L(s)` on a full real interval, (iii) identity theorem
(`eqOn_of_preconnected_of_frequently_eq`, the corpus `DlvpTransfer` pattern) extending `L ≡ 0`
to all `Re s > 1`).  Here: `ψ(1+N) = −γ + H_N` (our `digamma_shift` at `s = 1` + Mathlib
`digamma_one`), so `ψ(1+N) − log(1+N) = −γ + (H_N − log(N+1)) → −γ + γ = 0` by Mathlib's
`Real.tendsto_harmonic_sub_log_add_one`.  conjecture1_proved = False. -/



/-! ## Brick 3b′-ii-a: `ψ` is REAL on the positive reals, equals `deriv (log ∘ Γ)`, and that
derivative is MONOTONE (log-convexity of `Γ`, Bohr–Mollerup).  These are the sandwich's two
pillars; 3b′-ii-b squeezes `ψ(x+N) − log(x+N) → 0` for real `x` between integer anchors. -/







/-! ## Brick 3b′-ii-b: the REAL-AXIS SQUEEZE — the anchor discharged on `[1, 3]`.

Sandwich `d(x+N) = ψ(x+N) − log(x+N)` for real `x ∈ [1,3]` between the integer-anchor
sequences: `ψ` monotone (pillar ii-a) gives `ψ(1+N) ≤ ψ(x+N) ≤ ψ(3+N)`; `log` monotone gives
the reverse for the log part; both outer sequences → 0 by the integer anchor (3b′-i, plus its
`N ↦ N+2` shift) and the vanishing log gap (`Real.tendsto_log_comp_add_sub_log`).  Squeeze ⟹
`d(x+N) → 0` for every real `x ∈ [1,3]` — the anchor hypothesis of
`norm_digamma_sub_log_le_of_anchor` is DISCHARGED on the real segment, yielding the first
UNCONDITIONAL effective Binet points (`norm_digamma_sub_log_le_ofReal`).  Brick (iii) extends
to complex `s` by the identity theorem.  conjecture1_proved = False. -/

















/-! ## Brick 3b′-iii: the IDENTITY THEOREM — the anchor discharged for ALL `Re s ≥ 2`.

The limit function `binetLimit s := (ψ(s) − log s) + Σ′_k [(s+k)⁻¹ − log(1+(s+k)⁻¹)]` is the
`N → ∞` limit of `ψ(s+N) − log(s+N)` (partial sums = the telescoped Binet identity).  It is
HOLOMORPHIC on `U = {Re > 3/2}` (Weierstrass M-test: `‖tail_k‖ ≤ (3/2)/(3/2+k)²`, uniform on
`U`, summable by our own partial-sum lemma), and VANISHES on the real segment `[2,3]` (brick
ii-b's squeeze + uniqueness of limits).  The identity theorem on the convex half-plane then
forces `binetLimit ≡ 0` on all of `U` — so the anchor `ψ(s+N) − log(s+N) → 0` holds for EVERY
`s` with `Re s ≥ 2`, and the effective Binet bound `‖ψ(s) − log s‖ ≤ 1/(Re s − 1)` is
UNCONDITIONAL.  The analytic heart of Turing rung T2 is complete.
conjecture1_proved = False. -/

























end ZeroFreeBridge


/-  DIFFRACTION CORE (Dyson/quasicrystal axis, QC2 brick 1): the WEIGHTED rectangle pole formula.

    The T-ladder counts zeros (`rect_winding_generic`: `Bd((·-ρ)⁻¹) = 2πi`, the `g ≡ 1` case).
    The Dyson/Weil axis needs WEIGHTED sums over zeros — `Σ_ρ g(ρ)` for analytic test weights —
    because the explicit formula IS the diffraction identity: weighted zero-sums on one side,
    Bragg peaks at `k·log p` (prime sums) on the other.  This brick proves the single-pole
    mechanism over a rectangle:

      `Bd(g·(·-ρ)⁻¹) = 2πi·g(ρ)`   (g holomorphic near the closed box, ρ strictly interior).

    Proof: the removable-singularity split `g(z)·(z-ρ)⁻¹ = dslope g ρ z + g(ρ)·(z-ρ)⁻¹` (off ρ);
    `dslope g ρ` is holomorphic ACROSS ρ (Mathlib `has_fpower_series_dslope_fslope`), so its
    boundary integral vanishes by the generic rectangle Goursat (`rect_arg_principle_generic`);
    the remainder is `g(ρ)` times the counting winding (`rect_winding_generic`).

    Downstream (QC ladder): QC2 brick 2 = finite-sum version over a zero Finset (mirrors
    `box_residue_sum_generic`); QC3 = the finite-height Guinand–Weil identity, pushing the
    right edge to `Re > 1` where Mathlib's `LSeries_vonMangoldt_eq` (`L Λ = -ζ'/ζ`) turns the
    contour into PRIME SUMS — the Bragg peaks, kernel-side.  The Archimedean term is already
    built (`ZeroFreeBridge.logDeriv_gammaR`, the θ-bridge).

    conjecture1_proved = False. -/






open Complex MeasureTheory Real
open scoped Topology

section
namespace DiffractionCore
end DiffractionCore
open DiffractionCore









/-! ## Brick 4 (P1): the prime keystone — `logDeriv ζ = −L(Λ)` on `Re s > 1`.

Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` supplies the arithmetic side whole:
`L(Λ) s = −ζ′(s)/ζ(s)` for `Re s > 1`.  Restated in the harness's `logDeriv` vocabulary, this is
the identity that lets `bd_weighted_logDeriv_zeta`'s RIGHT EDGE (placed in `Re > 1`) speak primes:
the edge integrand `g·logDeriv ζ` becomes `−g·Σ Λ(n) n^{−s}` — the Bragg peaks at `k·log p`,
awaiting only the series–integral interchange (P2: dominated convergence along the compact edge,
`|Λ(n)n^{−s}| = Λ(n)n^{−σ₁}` summable).  conjecture1_proved = False. -/





/-! ## Brick 5 (P2): the series–integral interchange on the right edge.

With the right edge at `Re = σ₁ > 1`, the weighted edge integral of `L(Λ)` expands TERMWISE:
`∫ g·L(Λ) = Σ'_n ∫ g·term(Λ, n)` — dominated convergence with the `y`-independent majorant
`C·‖term(Λ, σ₁, n)‖` (vertical-line norm invariance is Mathlib's `norm_term_eq`: the norm
depends only on `Re s`; summability is `LSeriesSummable_vonMangoldt` + `summable_norm_iff`).
Combined with brick 4 this makes the right edge of `bd_weighted_logDeriv_zeta` a sum of
prime-power integrals `−Σ Λ(n)·∫ g·n^{−s}` — the Bragg peaks.  conjecture1_proved = False. -/



/-! ## Brick 6 (ASSEMBLY): the finite-height explicit formula — zeros = primes + boundary.

Composing bricks 3, 4, 5: place the box's right edge at `Re = σ₁ > 1`.  Brick 3 evaluates the
weighted boundary integral as the ZERO side (`2πi·Σ d(ρ)g(ρ)` over the actual divisor); brick 4
turns the right-edge integrand into `−g·L(Λ)` pointwise; brick 5 expands it termwise into
PRIME-POWER integrals.  The result — every hypothesis explicit, every step kernel-checked:

  `2πi · Σ_ρ d(ρ)·g(ρ)  =  (bottom edge) − (top edge) − i·Σ′_n Λ(n)-term integrals − i·(left edge)`

the rectangular Guinand–Weil / explicit-formula identity at finite height: **weighted sums over
zeta zeros equal von Mangoldt (prime-power) sums plus three boundary integrals.**  The right-edge
zeta non-vanishing is DERIVED (`Re > 1`, `riemannZeta_ne_zero_of_one_le_re`), and the test-weight
edge bound is DERIVED (extreme value theorem on the compact edge) — the Arb trust surface is only:
three off-prime-side edge non-vanishings + strict interiority of the ball's zero support.

Classically the three remaining edges are estimated and sent to limits (`T0 → −∞` symmetrically,
`σ₀ → −∞` via the functional equation); here they stand as honest, explicit remainder terms.
conjecture1_proved = False. -/



/-! ## Brick 7 (W1): the Bragg amplitude in closed form.

The prime-side integrals of `rect_explicit_formula` (constant weight `g ≡ 1`) evaluate in
CLOSED FORM: the `n`-th term is a pure oscillation of frequency `log n` —

  `∫_{T0}^{T1} Λ(n)·n^{−(σ+iy)} dy  =  [term at T1 − term at T0] / (−i·log n)`,

amplitude `Λ(n)·n^{−σ}/log n`, Bragg frequency `log n` (nonzero exactly at prime powers).
This is the diffraction pattern of the zeros, prime-side, as concrete arithmetic — the first
W1 (second-axis) brick: the formula meeting computable prime data.  conjecture1_proved = False. -/



/-! ## Brick 8 (EDGES-TO-LIMITS, structural half): the reflection identities — the LEFT edge
speaks primes and Archimedean, with ZERO Arb inputs.

The classical route sends the explicit formula's remaining edges to limits via the functional
equation: `Λ(1−s) = Λ(s)` reflects the left edge (`Re < 0`) into the prime region (`Re > 1`).
Here, kernel-side:

  * `logDeriv_completedZeta_reflect` — `(log Λ)′(1−s) = −(log Λ)′(s)` (the FE, differentiated);
  * `logDeriv_zeta_add_gammaR` — the split `(log Λ)′ = (log ζ)′ + (log Γℝ)′`;
  * `logDeriv_zeta_reflect` — the ζ reflection identity;
  * `left_edge_prime_reflection` — **for `Re s < 0`, `Im s ≠ 0`:**

      `(log ζ)′(s) = L(Λ)(1−s) − (log Γℝ)′(s) − (log Γℝ)′(1−s)`

    with EVERY hypothesis derived (`s ∉ {0,1}` from `Re < 0`; `ζ(s) ≠ 0` from the strip-location
    theorem; `ζ(1−s) ≠ 0` and `Γℝ(1−s) ≠ 0` from `Re(1−s) > 1`; `Γℝ(s) ≠ 0` from `Im ≠ 0`;
    the prime keystone at `1−s`).  The LEFT edge of any explicit-formula box in `Re < 0` is
    therefore prime sums (mirrored) + two Archimedean `ψ`-integrals (`logDeriv_gammaR` expands
    them into digammas — where the θ/Binet machinery lives) — **no ζ data, no Arb input**.

    Remaining for the full classical limit: the horizontal edges as `T → ∞`, which requires the
    `|ζ′/ζ| = O(log² T)` corridor lemma (zero-avoiding heights) — genuine further analysis,
    honestly out of scope here.  conjecture1_proved = False. -/









/-! ## Brick 9 (T3 ground — the ζ-side of Riemann–von Mangoldt): the box zero-count IS the
boundary winding of `ζ′/ζ`.

The `g ≡ 1` specialization of `bd_weighted_logDeriv_zeta`: the four-segment boundary integral of
`ζ′/ζ` around the box equals `2πi · (number of ζ-zeros in the box, with multiplicity)`.  This is
the argument principle for `ζ` in closed kernel form — the LEFT side of RvM
(`N(T) = θ(T)/π + 1 + S(T)`), which classically is obtained by taking this box to the half-line
`[1/2, ∞) × [0, T]` and splitting the boundary contour into the Γ-argument (→ `θ`, our
`riemannSiegelTheta` via the Archimedean bridge) and the ζ-argument remainder (→ `πS`).  The
half-line limit + the `S`-identification are the remaining research content
(see `docs/RVM_T3_T4_SCOPING`).  conjecture1_proved = False. -/



/-! ## Brick 10 (the argument-change infrastructure — closing the T3 "true gap" branch-free).

RvM's `S(T)` was flagged as needing a continuous `arg`-along-a-path, absent from Mathlib.  But
the CONTINUOUS ARGUMENT CHANGE along a zero-avoiding path IS the imaginary part of the
log-derivative line integral — `Im ∫ f′/f = Δ arg f`, `Re ∫ f′/f = Δ log‖f‖` — with NO branch
function, exactly as `riemannSiegelTheta` was defined by an integral rather than a branch of
`logΓ`.  These definitions + the box identity (from `bd_logDeriv_zeta_eq_count` by taking `.im`)
give the argument principle in ARGUMENT-CHANGE form: total argument change around the box =
`2π · (zero-count)`.  This is the scaffold `S` sits on: as the box opens to the half-plane, the
vertical-edge argument change on the near-critical side becomes `π·S(T)` and the horizontal/Γ
contributions become `θ(T)`.  conjecture1_proved = False. -/







/-! ## Brick 11 (RvM bookkeeping, phase 1): `S(T)` defined branch-free, and
`θ(T)` IS the Archimedean argument-change up the critical line.

With the argChange vocabulary the classical objects become DEFINITIONS, not constructions:

  * `riemannS T` — the argument of `ζ` at `1/2 + iT` by continuous variation along the standard
    zero-avoiding path (`2 → 2 + iT → 1/2 + iT`), divided by `π`.  Branch-free: each leg is an
    `Im`/`Re` of a log-derivative integral.  (Total function; its RvM meaning requires the path
    to avoid zeros, i.e. `T` not a zero-ordinate — the classical caveat, honestly inherited.)
  * `theta_eq_argChangeVert_gammaR` — **`θ(T) = argChangeVert Γℝ (1/2) 0 T`**: the Riemann–Siegel
    phase IS the continuous Archimedean argument change up the critical line, welding the
    `DlvpTheta` campaign to the argument-principle machinery.  (Proof: the Archimedean bridge
    `thetaIntegrand_eq_re_logDeriv_gammaR` + `intervalIntegral_re`; integrability from the
    digamma ray continuity built in `DlvpTheta`.)

Remaining RvM assembly: the Λ-split of the box argument-change (linearity over
`logDeriv_zeta_add_gammaR`), the FE-fold, and the `s(s−1)/2` pole bookkeeping — assembly on
these pieces.  conjecture1_proved = False. -/









/-! ## Brick 12 (RvM bookkeeping, phase 2): THE S-DIFFERENCE COUNTING IDENTITY.

Fold brick 10's box argument-principle into the continuous-argument function: define
`argZeta σ T` — the continuous argument of `ζ` at `σ + iT` along the standard route
`2 → 2+iT → σ+iT` (so `π·riemannS T = argZeta (1/2) T`).  Then for a box `[σ0, 2] × [T0, T1]`
with admissible boundary, the count identity becomes

  `2π · N_box  =  (argZeta σ0 T1 − argZeta σ0 T0)  −  argChangeVert ζ σ0 T0 T1`

— **the zero-count is the jump of the continuous argument at the left abscissa, minus the
left-edge remainder.**  The right edge (`Re = 2`) is absorbed by vertical additivity (its zeta
non-vanishing and integrability are THEOREMS), the horizontals by the route's definition.  At
`σ0` in zero-free territory the left edge is computable (reflection/primes); as `σ0 → 1/2` this
is the classical "`S` counts the zeros".  conjecture1_proved = False. -/











/-! ## Brick 13a (the FE-fold toolkit): log-derivatives under conjugation.

The FE-fold turns the left-edge argument change into mirror-edge data at NEGATIVE heights;
Schwarz reflection (`f(s̄) = conj (f s)`) folds those back to positive heights.  Kernel form:
Mathlib's `HasDerivAt.star_conj` gives the anti-holomorphic chain rule, whence for any
conj-symmetric `f`, `logDeriv f (s̄) = conj (logDeriv f s)` — instantiated for `ζ`
(`riemannZeta_conj`) and `Γℝ` (proved here from `Gamma_conj` + `exp_conj`).  Since
`Re ∘ conj = Re`, every `argChangeVert` at a negative height mirrors to its positive-height
twin — the fold's computability toolkit.  conjecture1_proved = False. -/











/-! ## Brick 13b-infra (the FE-fold edge-integrability): `logDeriv ζ` and `logDeriv Γℝ`
continuous along GENERAL vertical lines.

The symmetric fold's `integral_congr` needs the four edge integrands continuous on arbitrary
vertical segments — not just the `Re = 1/2`, `Re = 2` lines hardcoded in bricks 11–12.  These
generalize those to any `Re = σ` (`σ > 1` for `ζ`, `σ > 0` for `Γℝ`), via a reusable general
digamma continuity (`digamma_continuousAt_of_re_pos`, absent from Mathlib).  With them, every
`argChangeVert` in the fold is a well-defined integral of a continuous function.
conjecture1_proved = False. -/







/-! ## Brick 13b (THE SYMMETRIC FOLD IDENTITY): the left-edge argument change equals minus the
Archimedean argument changes, both edges at the same height.

Reflection (`logDeriv_zeta_reflect`) sends `σ₀ + iy ↦ (1−σ₀) − iy`; the conjugation toolkit
(`logDeriv_zeta_conj`, `logDeriv_gammaR_conj`) folds that `−iy` back to `+iy`, so the mirror
data lands on the `Re = 1−σ₀` line at the SAME positive height.  Taking real parts (RvM's
argument changes) gives, for `σ₀ < 0` and `y > 0`, the pointwise integrand of the fold
`AV(ζ,σ₀) + AV(ζ,1−σ₀) = −AV(Γℝ,σ₀) − AV(Γℝ,1−σ₀)`.  Every hypothesis is DERIVED: `ζ(σ₀+iy) ≠ 0`
from the strip-location theorem; `ζ((1−σ₀)+iy) ≠ 0` from `Re > 1`; the `Γℝ` non-vanishings from
`Im ≠ 0`.  conjecture1_proved = False. -/





/-! ## Brick 13b-wrap (THE FOLD, integral form): `AV(ζ,σ₀)+AV(ζ,1−σ₀) = −AV(Γℝ,σ₀)−AV(Γℝ,1−σ₀)`.

Integrate `fold_pointwise` over a positive-height segment `0 < T0 ≤ T1` (the classical
zero-avoiding requirement).  Edge continuity off the real axis: `Γℝ` analytic where `Im ≠ 0`
(the `Γ`-poles are real), `ζ` continuous off its zeros; `intervalIntegral.integral_congr` +
`intervalIntegral_re` do the rest.  conjecture1_proved = False. -/


theorem solution {s : ℂ} (him : s.im ≠ 0) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {w : ℂ | w.im ≠ 0} :=
    isOpen_compl_singleton.preimage Complex.continuous_im
  have hdiff : DifferentiableOn ℂ Gammaℝ {w : ℂ | w.im ≠ 0} := by
    intro w hw
    have hwim : w.im ≠ 0 := hw
    have hpole : ∀ m : ℕ, w / 2 ≠ -(m : ℂ) := by
      intro m hm
      apply hwim
      have := congrArg Complex.im hm
      simp only [Complex.div_im, Complex.neg_im, Complex.natCast_im] at this
      simpa using this
    have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) w := by
      simpa using (hasDerivAt_id w).div_const 2
    have hB : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
        (deriv Complex.Gamma (w / 2) * (1 / 2)) w :=
      ((Complex.differentiableAt_Gamma _ hpole).hasDerivAt).comp w hhalf
    have hGdef : Gammaℝ = fun z : ℂ => ZeroFreeBridge.gammaRArch z * Complex.Gamma (z / 2) := rfl
    rw [hGdef]
    exact (((ZeroFreeBridge.gammaRArch_hasDerivAt w).differentiableAt).mul
      hB.differentiableAt).differentiableWithinAt
  exact (hdiff.analyticOnNhd hopen) s him
