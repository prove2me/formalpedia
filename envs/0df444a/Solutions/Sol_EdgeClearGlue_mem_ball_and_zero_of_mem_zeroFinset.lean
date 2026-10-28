-- Prove2me | solution 1 for EdgeClearGlue.mem_ball_and_zero_of_mem_zeroFinset
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:38:37.545817+00:00
-- url     : https://prove2.me/submissions/6fc2dc6c-bc70-4a2c-9375-28763e26f678

import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

namespace RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/







/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/





/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/



/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/











/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/





theorem mem_zeroFinset {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R) {ρ : ℂ} :
    ρ ∈ zeroFinset c R hs1 ↔
      ρ ∈ (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).support := by
  rw [zeroFinset, Set.Finite.mem_toFinset]



/-! ## Part F: the parameterized capstone. -/



end RHInBoxAnalytic


/-  EdgeClearGlue.lean -- brick K1 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `hArbT_nonvanishing_of_edge_clear`).

    Every emitted Turing band `RHInBoxT_*.rh_in_box_*` states the canonical
    `TuringBand.BandStatement` and takes an Arb binder `hArbT` with nine conjuncts.  The first four
    are non-vanishing and confinement facts about the RvM rectangle `[-1, 2] x [T0, T1]` and the
    Blaschke ball `ball c R` that covers it:

      hnzb : ∀ x ∈ [-1, 2], ζ(x + T0 i) ≠ 0                      (H2a, bottom edge)
      hnzt : ∀ x ∈ [-1, 2], ζ(x + T1 i) ≠ 0                      (H2a, top edge)
      hnzl : ∀ y ∈ [T0, T1], ζ(-1 + y i) ≠ 0                     (H2b, left edge)
      hins : every zero of ζ in `ball c R` lies in (-1, 2) x (T0, T1)   (H2c, confinement)

    This file derives all four from
      * `ZetaZeroConfinement.zeta_zero_re_mem_strip`: an off-real zero of ζ has 0 < Re < 1;
      * the ball geometry: three rational/sqrt inequalities about c, R, T0, T1 (decidable per band);
      * two EDGE-CLEARANCE facts, the memo's E(T0, δ0) and E(T1, δ1), as zero-free SLABS on the
        OUTER side of each edge: `SlabClear (T0 - δ0) T0` and `SlabClear T1 (T1 + δ1)`, where
        `SlabClear a b` says ζ has no zero with 0 < Re < 1 and a ≤ Im ≤ b.

    H2b needs no input at all: `hnzl_discharged` proves the conjunct for EVERY `T0`, `T1`, with no
    hypotheses (off the real axis by the strip theorem; at y = 0 by ζ(-1) = -1/12).  That removes
    one binder from each of the 10,379 bands of the h280000 ladder.

    What remains numerical after this file: two one-sided slab facts per band, about the open strip
    0 < Re < 1 only.  WHY ONE-SIDED, AND HOW TALL (measured on the h280000 ladder with the float
    zero list at grid 0.01, the tight cases refined with mpmath; untrusted numerics, design only):
      * ONE-SIDED: at about 2,831 band edges a zero lies on the INNER side of the edge closer than
        the ball cap (as close as the grid resolves), so even a two-sided window of half-height
        equal to the cap would be false there.  Inner-side zeros are counted by the band; only
        the outer side must be clear, and that is all `hins` needs.
      * TALL ENOUGH, NOT TOO TALL: the slab must reach past the ball cap (δ ≥ cap; caps are 0.0574
        to 0.0922) and must stop before the nearest zero beyond the edge.  The margin between the
        two is as small as 4.3e-5 (top edge 154974: cap 0.092160, zero at 154974.092203).  So δ
        must be the band's own cap rounded up finely (emit_band_glue.py uses 1e-6); a round
        δ = 1/10 would make the slab hypothesis false at about 385 of the 10,379 bands.

    Trust: no hypotheses beyond those named in each statement; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  This is glue for a finite verification up to a fixed height; it
    says nothing about the Riemann Hypothesis. -/




open Complex

section
namespace EdgeClearGlue
end EdgeClearGlue
open EdgeClearGlue

/-! ## Zeta off the critical strip -/











/-! ## Edge clearance: zero-free slabs -/







/-! ## Confinement of the Blaschke-ball zeros -/


theorem solution {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    {ρ : ℂ} (h : ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1) :
    ρ ∈ Metric.ball c R ∧ riemannZeta ρ = 0 := by
  rw [RHInBoxAnalytic.mem_zeroFinset] at h
  have hU : ρ ∈ Metric.ball c R :=
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).supportWithinDomain h
  refine ⟨hU, ?_⟩
  have hUsub : Metric.ball c R ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hζU : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) := analyticOn_riemannZeta.mono hUsub
  by_contra hne
  rw [Function.mem_support] at h
  apply h
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hU,
    (hζU ρ hU).analyticOrderAt_eq_zero.mpr hne]
  simp
