-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:43:02.809284+00:00
-- url     : https://prove2.me/submissions/4fd5c44c-71f9-4ea7-ba1f-3a28ee96b410
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_ratio_bound
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_cumulative_laplace_of_monotone
import Theorems.Thm_AvramDividend_Classical_positive_esscher_shift_laplace_domain
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
# The Wiener–Hopf cumulative representation in the Gaussian branch

Kuznetsov–Kyprianou–Rivero (2012), *Theory of Scale Functions*, §4: in the
unbounded-variation branch with a positive Gaussian coefficient, there is a
positive cumulative ladder-potential measure `β` and a positive Esscher root
`φ` with `ψ φ = q` such that the Esscher-normalised `q`-scale function
`e^{-φ x} W x` is the cumulative of `β`:

    β (Iic x) = e^{-φ x} W x,

equivalently (in the Laplace-transform sense actually used here) the two
integrands `e^{-θ x} e^{-φ x} W x` and `e^{-θ x} (β (Iic x)).toReal` have
the same integral for every admissible `θ`.

## The reduction

The proof is a composition of the mission's own Proved results, with one
imported Open child.

1. **The exit-decay bound.**  The authoritative child
   `unbounded_esscher_ratio_bound` (`8ec2b84f`) provides the Cramér-root
   decay estimate: there is `φ > 0` with `ψ φ = q` and
   `W x / W y ≤ e^{-φ (y - x)}` for `0 < x ≤ y`.  Since `W y > 0`, this is
   `W x ≤ e^{-φ (y - x)} · W y`.

2. **The tilted monotonicity.**  The Proved
   `exit_decay_implies_tilted_monotone` (`d9758234`) turns that bound into
   `MonotoneOn (fun x => e^{-φ x} W x) (Ioi 0)`.

3. **The remaining hypotheses of the Proved construction.**
   `esscher_cumulative_laplace_of_monotone` (`ffbb7361`) also needs
   `W 0 = 0`, `0 < W x` and the Esscher Laplace cut:
   * `W 0 = 0` comes from the Proved
     `scaleFunction_zero_origin_gaussian_without_standing` (`20b1acb4`);
   * `0 < W x` comes from the Proved
     `scaleFunction_strict_pos_of_standing` (`59531c77`);
   * the cut comes from the Proved `psi_eventually_gt_of_gaussian`
     (`f5a240ce`) fed into the Proved
     `positive_esscher_shift_laplace_domain` (`f3a9c68b`).

4. **The construction.**  The Proved `ffbb7361` now applies and returns
   exactly the statement of this target.

## What this candidate is, and is not

The imported child `8ec2b84f` is still **Open**: its content is the
Cramér-root decay estimate, whose proof is the Esscher-tilted two-sided exit
identity — the same fluctuation input as the mission's root
`two_sided_exit_stopped_scale_identity` (`09663d0d`).  So this candidate is
a source-faithful *reduction*, not a proof; it is expected to return
`SKETCH_ACCEPTED`, and the target stays `Open` until the imported child is
discharged.

The reduction matters because `8ec2b84f` is the leaf whose discharge unblocks
the whole regularity chain: `8ec2b84f` → `d2e374c7` (this target) → the Proved
`02d57749` / `89b8d623` → tilted monotonicity → `8d7288ac` → `6b0b9766` →
`44b032f3` → `e8fbc763` → `88d146b8` (the mission's goal), and also
`6b0b9766` → `7bb43015` (`cstar_lt_top`) → `00fcfc56` (`cstar_optimal_barrier`).
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal := by
  -- Step 1: the Cramér-root decay estimate.  A positive Gaussian coefficient
  -- excludes the bounded-variation case, so the unbounded child applies.
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    have hσzero : X.σ = 0 := hbv.1
    have hposσ : (0 : ℝ) < X.σ := hσ
    rw [hσzero] at hposσ
    exact absurd hposσ (by norm_num)
  obtain ⟨φ, hφ, hroot, hdecay⟩ :=
    unbounded_esscher_ratio_bound X q hq W hW hnbv
  -- Step 2: the decay bound in multiplicative form, and the tilted
  -- monotonicity it induces.
  have hWpos : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    exact scaleFunction_strict_pos_of_standing X hX q hq W hW x hx
  have hdecayMul : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp ((-φ) * (y - x)) * W y := by
    intro x y hx hxy
    have hratio := hdecay x y hx hxy
    have hWyp : 0 < W y := hWpos y (lt_of_lt_of_le hx hxy)
    have hexp : Real.exp (-(φ * (y - x))) = Real.exp ((-φ) * (y - x)) := by
      congr 1
      rw [neg_mul]
    -- Multiply the ratio inequality by the positive `W y`, then cancel it.
    have hmult : (W x / W y) * W y ≤ Real.exp (-(φ * (y - x))) * W y :=
      mul_le_mul_of_nonneg_right hratio (le_of_lt hWyp)
    have hmult' : W y * (W x / W y) ≤ W y * Real.exp (-(φ * (y - x))) := by
      simpa only [mul_comm] using hmult
    have hcancel : W x / W y ≤ Real.exp (-(φ * (y - x))) :=
      le_of_mul_le_mul_left hmult' hWyp
    have hback : W y * (W x / W y) ≤ W y * Real.exp (-(φ * (y - x))) :=
      mul_le_mul_of_nonneg_left hcancel (le_of_lt hWyp)
    have hfinal : W x ≤ Real.exp (-(φ * (y - x))) * W y := by
      calc W x = W y * (W x / W y) := by
              field_simp [ne_of_gt hWyp]
            _ ≤ W y * Real.exp (-(φ * (y - x))) := hback
            _ = Real.exp (-(φ * (y - x))) * W y := by rw [mul_comm]
    rw [← hexp]
    exact hfinal
  have htilt : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    exit_decay_implies_tilted_monotone W φ hdecayMul
  -- Step 3: the remaining hypotheses of the Proved construction.
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  obtain ⟨β0, hβ0nonneg, hψ⟩ := psi_eventually_gt_of_gaussian X q hσ
  have hcut : ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ + φ ∧ q < X.ψ (θ + φ) :=
    positive_esscher_shift_laplace_domain X.ψ q φ β0 hφ hψ
  -- Step 4: the Proved construction, which is exactly the goal.
  exact esscher_cumulative_laplace_of_monotone X q W hW hzero φ hφ hWpos htilt hcut
