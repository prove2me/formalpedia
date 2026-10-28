-- Prove2me | solution 1 for EdgeClearGlue.hins_of_slabClear
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:22.67399+00:00
-- url     : https://prove2.me/submissions/94dc8f49-75e3-4a4f-9ffa-2b6789493776

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
import Theorems.Thm_EdgeClearGlue_mem_ball_and_zero_of_mem_zeroFinset
import Theorems.Thm_ZetaZeroConfinement_zeta_zero_iff_completed_zero_of_im_ne
/- CONFINEMENT (kernel): every nontrivial zeta zero up to height T lies in the band [a, 1-a].

   This is the "confinement" half of the "all zeros up to height T are on the line" project:
   box-localization (all zeros IN a box on the line, PR #312) + confinement (all zeros ARE in the
   box, this file).  We prove the confinement:

     `zero_in_band` :  a nontrivial zero `ρ` (`ζ ρ = 0`, `0 < ρ.im ≤ T`) with `a ≤ dlvpRateC/log T`
                       satisfies  `a ≤ ρ.re ≤ 1 - a`.

   Both edges come from the SELF-CONTAINED effective de la Vallée Poussin zero-free region
   `ZeroFreeBridge.riemannZeta_ne_zero_region` (PR #318 -- no multiplicity input, β≥3/4 discharged
   internally): `ζ(β+iγ) ≠ 0` for `|γ| ≥ 55/16` and `β > 1 - dlvpRateC/log|γ|`.

   - RIGHT edge `ρ.re ≤ 1-a`:  contrapositive of the region at `ρ` gives `ρ.re ≤ 1 - dlvpRateC/log|γ|`,
     and `dlvpRateC/log|γ| ≥ dlvpRateC/log T ≥ a` (log monotone, `|γ| = ρ.im ≤ T`; `dlvpRateC > 0`).
   - LEFT edge `a ≤ ρ.re`:  reflect through the functional equation.  `ζ ρ = 0` ⟹ `Λ ρ = 0`
     (unconditional strip bridge: `ρ.im ≠ 0` ⟹ `Gammaℝ ρ ≠ 0`) ⟹ `Λ (1-ρ) = 0`
     (`completedRiemannZeta_one_sub`) ⟹ `ζ (1-ρ) = 0` (strip bridge again, `(1-ρ).im = -ρ.im ≠ 0`).
     The reflected zero has real part `1-ρ.re`, height `-ρ.im`, `|-ρ.im| = |ρ.im| ≥ 55/16`.  The
     region contrapositive on it gives `1-ρ.re ≤ 1 - dlvpRateC/log|γ| ≤ 1 - a`, i.e. `ρ.re ≥ a`.

   RESIDUAL (documented, honest -- a genuine Mathlib gap, NOT a fake).  Mathlib has no "no zeta
   zeros with `|Im| < 14`" fact (the first nontrivial zero is at height ~14.13 > 55/16 ~ 3.44), so
   the region's height-floor hypothesis `55/16 ≤ |ρ.im|` is carried as an ADDED hypothesis `hγ` on
   `zero_in_band`.  It is a small classical fact, discharged at the concrete T=100 instantiation
   from the on-line sweep (all 29 zeros up to 100 have height ≥ 14 > 55/16).  No multiplicity input,
   no `β ≥ 3/4` casework, no `0 < ρ.re` strip hypothesis (the FE strip bridge here is unconditional
   for `ρ.im ≠ 0`).

   conjecture1_proved = False (a kernel-verified reduction of confinement to the effective dVP
   region + the functional equation, NOT a proof of RH).
-/



open Complex

namespace ZetaZeroConfinement



/-- **The functional-equation reflection of an off-real zeta zero.**  `ζ ρ = 0` with `ρ.im ≠ 0`
    forces `ζ (1 - ρ) = 0`. -/
theorem zeta_zero_reflect {ρ : ℂ} (him : ρ.im ≠ 0) (hzero : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 := by
  have hΛ : completedRiemannZeta ρ = 0 := (zeta_zero_iff_completed_zero_of_im_ne him).1 hzero
  have hΛ' : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub]; exact hΛ
  have him' : (1 - ρ).im ≠ 0 := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]; exact him
  exact (zeta_zero_iff_completed_zero_of_im_ne him').2 hΛ'



/-- **Critical-strip location of a nontrivial (off-real) zeta zero.**  `ζ ρ = 0` with `ρ.im ≠ 0`
    forces `0 < ρ.re ∧ ρ.re < 1`.  `Re < 1` is `riemannZeta_ne_zero_of_one_le_re` directly; `0 < Re`
    is the same lemma applied to the functional-equation reflection `1 - ρ` (`zeta_zero_reflect`),
    whose real part `1 - ρ.re ≥ 1` when `ρ.re ≤ 0`.  Off-real is essential — the trivial zeros lie
    on the real axis at the negative even integers (`Re ≤ 0`). -/
theorem zeta_zero_re_mem_strip {ρ : ℂ} (him : ρ.im ≠ 0) (hz : riemannZeta ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have hrefl : riemannZeta (1 - ρ) = 0 := zeta_zero_reflect him hz
    have hge : (1 : ℝ) ≤ (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact riemannZeta_ne_zero_of_one_le_re hge hrefl
  · by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hz



end ZetaZeroConfinement


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



/-- The imaginary part of a point of `ball c R` lies strictly within `R` of `c.im`. -/
theorem im_mem_of_mem_ball {c ρ : ℂ} {R : ℝ} (h : ρ ∈ Metric.ball c R) :
    c.im - R < ρ.im ∧ ρ.im < c.im + R := by
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have h1 : |(ρ - c).im| ≤ ‖ρ - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h1
  have h2 := abs_lt.mp (lt_of_le_of_lt h1 h)
  constructor <;> linarith [h2.1, h2.2]





/-! ## Ball geometry for a `Real.sqrt` radius (the emitted bands use `R = √q`, `q` rational) -/







end EdgeClearGlue


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






theorem solution {T0 T1 δ0 δ1 : ℝ} {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hpos : 0 ≤ c.im - R) (hlo : T0 - δ0 ≤ c.im - R) (hhi : c.im + R ≤ T1 + δ1)
    (hE0 : SlabClear (T0 - δ0) T0) (hE1 : SlabClear T1 (T1 + δ1)) :
    ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1 := by
  intro ρ hρ
  obtain ⟨hball, hz⟩ := mem_ball_and_zero_of_mem_zeroFinset hs1 hρ
  obtain ⟨him_lo, him_hi⟩ := im_mem_of_mem_ball hball
  have him : ρ.im ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨hre0, hre1⟩ := ZetaZeroConfinement.zeta_zero_re_mem_strip him hz
  have hρeq : ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = ρ := Complex.re_add_im ρ
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · by_contra hle'
    have hle : ρ.im ≤ T0 := not_lt.mp hle'
    exact hE0 ρ.re ρ.im hre0 hre1 (by linarith) hle (by rw [hρeq]; exact hz)
  · by_contra hle'
    have hle : T1 ≤ ρ.im := not_lt.mp hle'
    exact hE1 ρ.re ρ.im hre0 hre1 hle (by linarith) (by rw [hρeq]; exact hz)
