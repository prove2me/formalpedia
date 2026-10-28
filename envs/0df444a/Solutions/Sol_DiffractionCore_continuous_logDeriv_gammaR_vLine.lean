-- Prove2me | solution 1 for DiffractionCore.continuous_logDeriv_gammaR_vLine
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:47:32.969984+00:00
-- url     : https://prove2.me/submissions/a71d145f-7a2c-4823-bf66-6c507b12b707

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_DiffractionCore_digamma_continuousAt_of_re_pos
import Theorems.Thm_ZeroFreeBridge_logDeriv_gammaR

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




theorem solution {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun y : ℝ => logDeriv Gammaℝ ((σ : ℂ) + y * I)) := by
  have hfun : (fun y : ℝ => logDeriv Gammaℝ ((σ : ℂ) + y * I))
      = fun y : ℝ => -(Real.log Real.pi : ℂ) / 2
          + (1 / 2) * Complex.digamma (((σ : ℂ) + y * I) / 2) := by
    funext y
    have hs : 0 < (((σ : ℂ) + y * I) / 2).re := by
      simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
      positivity
    rw [ZeroFreeBridge.logDeriv_gammaR _ hs]
  rw [hfun]
  refine continuous_const.add (continuous_const.mul ?_)
  have hpath : Continuous (fun y : ℝ => ((σ : ℂ) + y * I) / 2) := by fun_prop
  have hc : (fun y : ℝ => Complex.digamma (((σ : ℂ) + y * I) / 2))
      = Complex.digamma ∘ (fun y : ℝ => ((σ : ℂ) + y * I) / 2) := rfl
  rw [hc]
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hzre : 0 < (((σ : ℂ) + y * I) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    positivity
  exact ContinuousAt.comp (g := Complex.digamma) (f := fun t : ℝ => ((σ : ℂ) + t * I) / 2)
    (digamma_continuousAt_of_re_pos hzre) hpath.continuousAt
