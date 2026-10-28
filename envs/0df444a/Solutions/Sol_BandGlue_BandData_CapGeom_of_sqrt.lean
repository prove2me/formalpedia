-- Prove2me | solution 1 for BandGlue.BandData.CapGeom.of_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:31:47.17368+00:00
-- url     : https://prove2.me/submissions/fbe16f74-1bb9-49f6-9b82-8f94dff39447

import Definitions.Def_ArdaRH65K_Turing121_BandGlue
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

namespace EdgeClearGlue

/-! ## Zeta off the critical strip -/











/-! ## Edge clearance: zero-free slabs -/







/-! ## Confinement of the Blaschke-ball zeros -/









/-! ## Ball geometry for a `Real.sqrt` radius (the emitted bands use `R = √q`, `q` rational) -/

/-- Bottom cap: `T0 - δ0 ≤ c.im - √q` from `q ≤ (c.im - T0 + δ0)²` with `0 ≤ c.im - T0 + δ0`. -/
theorem cap_lo_of_sq {cim T0 δ0 q : ℝ} (hb : 0 ≤ cim - T0 + δ0) (hq : q ≤ (cim - T0 + δ0) ^ 2) :
    T0 - δ0 ≤ cim - Real.sqrt q := by
  have h : Real.sqrt q ≤ cim - T0 + δ0 := Real.sqrt_le_iff.mpr ⟨hb, hq⟩
  linarith

/-- Top cap: `c.im + √q ≤ T1 + δ1` from `q ≤ (T1 + δ1 - c.im)²` with `0 ≤ T1 + δ1 - c.im`. -/
theorem cap_hi_of_sq {cim T1 δ1 q : ℝ} (hb : 0 ≤ T1 + δ1 - cim) (hq : q ≤ (T1 + δ1 - cim) ^ 2) :
    cim + Real.sqrt q ≤ T1 + δ1 := by
  have h : Real.sqrt q ≤ T1 + δ1 - cim := Real.sqrt_le_iff.mpr ⟨hb, hq⟩
  linarith

/-- Ball above the real axis: `0 ≤ c.im - √q` from `q ≤ c.im²` with `0 ≤ c.im`. -/
theorem ball_above_of_sq {cim q : ℝ} (hb : 0 ≤ cim) (hq : q ≤ cim ^ 2) :
    0 ≤ cim - Real.sqrt q := by
  have h : Real.sqrt q ≤ cim := Real.sqrt_le_iff.mpr ⟨hb, hq⟩
  linarith

end EdgeClearGlue


/-  BandGlue.lean -- brick K0 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `segBandHyp_of_bands`).

    THE GAP IT CLOSES.  The h280000 capstone
    `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000` takes
    `hbands : ∀ k, k < 280 → SegBandHyp k`, and each `SegBandHyp k` is a list of BOX CLAIMS
    ("every zero of ζ in `[1/4000000, 3999999/4000000] x [segLo k i, segHi k i]` is on the line").
    Every box claim is the conclusion of one emitted band theorem `RHInBoxT_*.rh_in_box_*`, but the
    capstone ASSUMES the claims: nothing composes them.  This file makes the composition a theorem,
    parametric in the per-band Arb inputs, so a future evaluator only has to supply those inputs.

    CONTENTS.
      * `BandData`: the parameters of one Turing band, i.e. the arguments of the canonical
        `TuringBand.BandStatement` other than the strip.  `Stmt`, `LineHyp`, `ArbHyp`, `EnclHyp`,
        `Box`, `Inputs`.  `stmt_iff` checks, by `Iff.rfl`, that `LineHyp`/`ArbHyp` are EXACTLY the
        two binders of `BandStatement` (so `Inputs` is what `hLine`/`hArbT` ask for, verbatim).
      * `stmt_of_valid`: the band statement from its decidable side conditions (pins, ball
        geometry), via `TuringBand.turing_band_on_line`; the generic proof of every `rh_in_box_*`.
      * K0 generic: `segBandHyp_of_bands` (indexed band table: the `SegBandHyp` shape),
        `segBandHyp_of_bandList` (a `List` of bands), `ladder_of_bands` (a ladder of segments: the
        `∀ k, k < K → SegBandHyp k` shape the capstone consumes).  Bands may COVER their boxes
        (`T0 ≤ lo`, `hi ≤ T1`); the emitted ladder has equality.
      * K0 + K1: `ReducedInputs` (on-line zeros, two one-sided edge-clearance slabs, five
        enclosures) and `CapGeom` (decidable ball-cap geometry); `inputs_of_reduced`,
        `segBandHyp_of_reduced`, `ladder_of_reduced` (per-band slab heights).  With K1 the `hnzl`
        binder disappears and `hnzb`/`hnzt`/`hins` reduce to two zero-free slabs per band.
      * Certificate form: `BoxCert σ0 σ1 lo hi` (some band covering the box, with its statement
        and its inputs), constructors `of_stmt` / `of_valid` / `of_reduced`, and
        `segBandHyp_of_certs`, `ladder_of_certs`.  A future evaluator may pick its own band
        parameters here (for instance enclosures much wider than the 1e-12 Arb ones, as long as
        the pins hold), which the fixed-table form does not allow.

    The real-segment instantiation (segment 0 of the ladder, 25 bands, the real `rh_in_box_*`
    theorems) is `BandGlue_h1000.lean`.

    Trust: every theorem here is proved outright from its stated hypotheses; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height; nothing
    here says anything about the Riemann Hypothesis. -/





open Complex

section
namespace BandGlue
end BandGlue
open BandGlue





section
namespace BandGlue.BandData
end BandGlue.BandData
open BandGlue.BandData

variable (σ0 σ1 : ℝ) (d : BandData)















variable {σ0 σ1 d}







/-! ## K1 inside the band: the reduced per-band input -/






theorem solution {δ0 δ1 : ℝ} {d : BandData} (t0 t1 cim q : ℝ)
    (hT0v : d.T0 = t0) (hT1v : d.T1 = t1) (hcv : d.c.im = cim) (hRv : d.R = Real.sqrt q)
    (ht0 : t0 ≠ 0) (ht1 : t1 ≠ 0) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1)
    (hc0 : 0 ≤ cim) (hq0 : q ≤ cim ^ 2)
    (hlo0 : 0 ≤ cim - t0 + δ0) (hlo : q ≤ (cim - t0 + δ0) ^ 2)
    (hhi0 : 0 ≤ t1 + δ1 - cim) (hhi : q ≤ (t1 + δ1 - cim) ^ 2) :
    d.CapGeom δ0 δ1 := by
  refine ⟨?_, ?_, hδ0, hδ1, ?_, ?_, ?_⟩
  · rw [hT0v]; exact ht0
  · rw [hT1v]; exact ht1
  · rw [hcv, hRv]; exact EdgeClearGlue.ball_above_of_sq hc0 hq0
  · rw [hT0v, hcv, hRv]; exact EdgeClearGlue.cap_lo_of_sq hlo0 hlo
  · rw [hT1v, hcv, hRv]; exact EdgeClearGlue.cap_hi_of_sq hhi0 hhi
