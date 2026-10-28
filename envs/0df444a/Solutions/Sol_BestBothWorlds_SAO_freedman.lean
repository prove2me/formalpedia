-- Prove2me | solution 1 for BestBothWorlds.SAO.freedman
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T10:05:39.955754+00:00
-- url     : https://prove2.me/submissions/beea4cf0-d672-49cd-b20b-21a1cb7cb6b0

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory

open MeasureTheory

/-! Bernstein remainder and conditional MGF step for `BestBothWorlds.SAO.freedman`
(graph-scout %72). Helpers only; this file does not prove the frozen target.

Owner interface: analysis-prover's freedman-bernstein INTERFACE.md v1 (sha256 a5342a80).

* `exp_le_bernstein`: `exp y ≤ 1 + y + y²/(2(1 - κ/3))` for `0 ≤ κ < 3`, `y ≤ κ`.
  For `y ≤ 0` this is `exp y ≤ 1 + y + y²/2`. For `0 ≤ y` it follows from the exponential series
  and `(k+2)! ≥ 2·3^k`.
* `condExp_exp_le_bernstein` (exported last): for `|X| ≤ b`, `condExp X = 0`, `0 < λ` and `λb < 3`,
  `E[e^{λX} | m] ≤ exp (λ²/(2(1 - λb/3)) · E[X² | m])` almost everywhere, with integrability.

Reused verbatim, renamed with the `gsBern_` prefix:
* `exp_neg_le_quadratic` from the accepted lemma_6 source (submission 2cab6d49, namespace
  `NativeScaleFreeLower`);
* `condExp_quadratic_envelope` and `condExp_exp_le_exp_of_ae_quadratic` from the accepted
  Freedman source d7ef840c (namespace `FreedmanNative.ConditionalMGF`), without its
  autoImplicit option line. -/

namespace BestBothWorlds.SAO.GSBern

section GSBernScalarReused

open Set

theorem gsBern_exp_neg_le_quadratic (s : ℝ) (hs : 0 ≤ s) :
    Real.exp (-s) ≤ 1 - s + s ^ 2 / 2 := by
  have hf (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    apply ((Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)).congr_deriv
    ring
  have hg (x : ℝ) :
      HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (x - 1) x := by
    apply (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const (2 : ℝ))).congr_deriv
    simp only [id_eq]
    ring
  have hbound (x : ℝ) : -Real.exp (-x) ≤ x - 1 := by
    have hexp := Real.add_one_le_exp (-x)
    linarith
  exact image_le_of_deriv_right_le_deriv_boundary
    (a := 0) (b := s)
    (f := fun x : ℝ => Real.exp (-x))
    (f' := fun x : ℝ => -Real.exp (-x))
    (B := fun x : ℝ => 1 - x + x ^ 2 / 2)
    (B' := fun x : ℝ => x - 1)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).hasDerivWithinAt)
    (by simp)
    (fun x _ => (hg x).continuousAt.continuousWithinAt)
    (fun x _ => (hg x).hasDerivWithinAt)
    (fun x _ => hbound x)
    (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩)

end GSBernScalarReused

section GSBernConditionalReused

open scoped MeasureTheory

variable {Ω : Type*}
variable {m mΩ : MeasurableSpace Ω}
variable {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

/-- Conditional expectation of the quadratic upper envelope, with its exact
canonical conditional-expectation representatives. -/
theorem gsBern_condExp_quadratic_envelope {X : Ω → ℝ} {lam c : ℝ}
    (hm : m ≤ mΩ) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hzero : condExp m P X =ᵐ[P] 0) :
    condExp m P (fun ω => 1 + lam * X ω + (c * lam ^ 2) * X ω ^ 2) =ᵐ[P]
      (fun ω => 1 + (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
  have hlinInt : Integrable (fun ω => lam * X ω) P := hint.const_mul lam
  have hquadInt : Integrable (fun ω => (c * lam ^ 2) * X ω ^ 2) P :=
    hint2.const_mul (c * lam ^ 2)
  have hadd₁ := condExp_add (μ := P) (integrable_const (1 : ℝ)) hlinInt m
  have hadd₂ := condExp_add (μ := P) ((integrable_const (1 : ℝ)).add hlinInt) hquadInt m
  have hlin := condExp_smul (μ := P) lam X m
  have hquad := condExp_smul (μ := P) (c * lam ^ 2) (fun ω => X ω ^ 2) m
  filter_upwards [hadd₁, hadd₂, hlin, hquad, hzero] with ω h₁ h₂ hL hQ hZ
  change condExp m P (fun u => 1 + lam * X u) ω =
    condExp m P (fun _ : Ω => (1 : ℝ)) ω +
      condExp m P (fun u => lam * X u) ω at h₁
  change condExp m P (fun u => 1 + lam * X u + (c * lam ^ 2) * X u ^ 2) ω =
    condExp m P (fun u => 1 + lam * X u) ω +
      condExp m P (fun u => (c * lam ^ 2) * X u ^ 2) ω at h₂
  change condExp m P (fun u => lam * X u) ω = lam * condExp m P X ω at hL
  change condExp m P (fun u => (c * lam ^ 2) * X u ^ 2) ω =
    (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω at hQ
  change condExp m P X ω = 0 at hZ
  have hconst : condExp m P (fun _ : Ω => (1 : ℝ)) ω = 1 := by
    rw [condExp_const hm]
  calc
    condExp m P (fun u => 1 + lam * X u + (c * lam ^ 2) * X u ^ 2) ω =
        condExp m P (fun u => 1 + lam * X u) ω +
          condExp m P (fun u => (c * lam ^ 2) * X u ^ 2) ω := h₂
    _ = 1 + (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω := by
      rw [h₁, hL, hQ, hconst, hZ]
      ring

/-- The conditional MGF step needs integrability of the exponential, not
integrability of its random conditional-variance exponential. -/
theorem gsBern_condExp_exp_le_exp_of_ae_quadratic {X : Ω → ℝ} {lam c : ℝ}
    (hm : m ≤ mΩ) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hexp : Integrable (fun ω => Real.exp (lam * X ω)) P)
    (hzero : condExp m P X =ᵐ[P] 0)
    (hbound : ∀ᵐ ω ∂P, Real.exp (lam * X ω) ≤
      1 + lam * X ω + (c * lam ^ 2) * X ω ^ 2) :
    ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u)) ω ≤
      Real.exp ((c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
  have hdomInt : Integrable
      (fun ω => 1 + lam * X ω + (c * lam ^ 2) * X ω ^ 2) P :=
    ((integrable_const (1 : ℝ)).add (hint.const_mul lam)).add
      (hint2.const_mul (c * lam ^ 2))
  have hmono := condExp_mono (m := m) (μ := P) hexp hdomInt hbound
  have henv := gsBern_condExp_quadratic_envelope (lam := lam) (c := c) hm hint hint2 hzero
  filter_upwards [hmono, henv] with ω hM hE
  calc
    condExp m P (fun u => Real.exp (lam * X u)) ω ≤
        condExp m P (fun u => 1 + lam * X u + (c * lam ^ 2) * X u ^ 2) ω := hM
    _ = 1 + (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω := hE
    _ ≤ Real.exp ((c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
      linarith [Real.add_one_le_exp ((c * lam ^ 2) *
        condExp m P (fun u => X u ^ 2) ω)]

end GSBernConditionalReused

/-- `2 · 3^k ≤ (k + 2)!`. -/
private theorem gsBern_factorial_ge (k : ℕ) : 2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h3 : 3 ≤ k + 2 + 1 := by omega
    rw [show k + 1 + 2 = k + 2 + 1 by ring]
    calc 2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ (k + 2 + 1) * (k + 2).factorial := Nat.mul_le_mul h3 ih
      _ = (k + 2 + 1).factorial := (Nat.factorial_succ (k + 2)).symm

/-- Series bound for `0 ≤ y < 3`: `exp y ≤ 1 + y + (y²/2)·(1 - y/3)⁻¹`. -/
private theorem gsBern_exp_le_of_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 * (1 - y / 3)⁻¹ := by
  have hs : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  have hshift := (hasSum_nat_add_iff' 2).mpr hs
  have hgeom := (hasSum_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ y / 3)
    (by linarith : y / 3 < 1)).mul_left (y ^ 2 / 2)
  have key : ∀ k : ℕ, y ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ y ^ 2 / 2 * (y / 3) ^ k := by
    intro k
    have hf : (2 * 3 ^ k : ℝ) ≤ ((k + 2).factorial : ℝ) := by
      exact_mod_cast gsBern_factorial_ge k
    have hpos : (0 : ℝ) < 2 * 3 ^ k := by positivity
    calc y ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ y ^ (k + 2) / (2 * 3 ^ k) :=
          div_le_div_of_nonneg_left (by positivity) hpos hf
      _ = y ^ 2 / 2 * (y / 3) ^ k := by
          rw [div_pow]
          ring
  have hle := hasSum_le key hshift hgeom
  have hfirst : ∑ i ∈ Finset.range 2, y ^ i / (i.factorial : ℝ) = 1 + y := by
    norm_num [Finset.sum_range_succ]
  rw [hfirst] at hle
  linarith

/-- **Bernstein remainder.** For `0 ≤ κ < 3` and `y ≤ κ`,
`exp y ≤ 1 + y + y² / (2 (1 - κ/3))`. -/
theorem exp_le_bernstein {κ y : ℝ} (hκ0 : 0 ≤ κ) (hκ3 : κ < 3) (hy : y ≤ κ) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - κ / 3)) := by
  have hd : 0 < 2 * (1 - κ / 3) := by linarith
  rcases le_or_gt y 0 with hy0 | hy0
  · have h := gsBern_exp_neg_le_quadratic (-y) (by linarith)
    rw [neg_neg] at h
    have hhalf : y ^ 2 / 2 ≤ y ^ 2 / (2 * (1 - κ / 3)) :=
      div_le_div_of_nonneg_left (sq_nonneg y) hd (by linarith)
    linarith
  · have h := gsBern_exp_le_of_nonneg hy0.le (by linarith : y < 3)
    have h2 : y ^ 2 / 2 * (1 - y / 3)⁻¹ ≤ y ^ 2 / (2 * (1 - κ / 3)) := by
      rw [← div_eq_mul_inv, div_div]
      exact div_le_div_of_nonneg_left (sq_nonneg y) hd (by linarith)
    linarith

/-- **One conditional step.** With `|X| ≤ b`, `condExp X = 0`, `0 < λ` and `λ b < 3`:
`E[e^{λX} | m] ≤ exp ((1/(2(1 - λb/3))) λ² E[X² | m])` a.e., and `e^{λX}` is integrable. -/
theorem condExp_exp_le_bernstein {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {b lam : ℝ} (hb : 0 < b)
    (hX : Measurable X) (hbd : ∀ᵐ ω ∂P, |X ω| ≤ b)
    (hlam0 : 0 < lam) (hlamb : lam * b < 3)
    (hmart : condExp m P X =ᵐ[P] 0) :
    Integrable (fun ω => Real.exp (lam * X ω)) P ∧
      condExp m P (fun ω => Real.exp (lam * X ω)) ≤ᵐ[P]
        fun ω => Real.exp (1 / (2 * (1 - lam * b / 3)) * lam ^ 2 *
          condExp m P (fun ω => X ω ^ 2) ω) := by
  have hint : Integrable X P :=
    Integrable.of_bound hX.aestronglyMeasurable b (by
      filter_upwards [hbd] with ω h
      rwa [Real.norm_eq_abs])
  have hint2 : Integrable (fun ω => X ω ^ 2) P :=
    Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (b ^ 2) (by
      filter_upwards [hbd] with ω h
      rw [Real.norm_eq_abs, abs_pow]
      nlinarith [abs_nonneg (X ω)])
  have hexp : Integrable (fun ω => Real.exp (lam * X ω)) P :=
    Integrable.of_bound ((hX.const_mul lam).exp).aestronglyMeasurable (Real.exp (lam * b)) (by
      filter_upwards [hbd] with ω h
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h) hlam0.le))
  have hbound : ∀ᵐ ω ∂P, Real.exp (lam * X ω) ≤
      1 + lam * X ω + (1 / (2 * (1 - lam * b / 3)) * lam ^ 2) * X ω ^ 2 := by
    filter_upwards [hbd] with ω h
    have hy : lam * X ω ≤ lam * b :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h) hlam0.le
    have hB := exp_le_bernstein (mul_nonneg hlam0.le hb.le) hlamb hy
    have heq : (lam * X ω) ^ 2 / (2 * (1 - lam * b / 3)) =
        (1 / (2 * (1 - lam * b / 3)) * lam ^ 2) * X ω ^ 2 := by
      ring
    rw [heq] at hB
    exact hB
  exact ⟨hexp, gsBern_condExp_exp_le_exp_of_ae_quadratic hm hint hint2 hexp hmart hbound⟩

end BestBothWorlds.SAO.GSBern

open MeasureTheory

namespace BestBothWorlds.SAO.AABernOptimizer

theorem positive_variance_optimizer (b ε V : ℝ) (hb : 0 < b)
    (hε : 0 < ε) (hV : 0 < V) :
    let lam := ε / (V + b * ε / 3)
    0 < lam ∧ lam * b < 3 ∧
      0 ≤ 1 / (2 * (1 - lam * b / 3)) ∧
      -lam * ε + 1 / (2 * (1 - lam * b / 3)) * lam ^ 2 * V =
        -ε ^ 2 / (2 * V + 2 * b * ε / 3) := by
  let d : ℝ := V + b * ε / 3
  let lam : ℝ := ε / d
  let r : ℝ := 1 - lam * b / 3
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hlam0 : 0 < lam := div_pos hε hd
  have hlamd : lam * d = ε := by
    dsimp only [lam]
    field_simp [hd.ne']
  have hlamb : lam * b < 3 := by
    dsimp only [lam]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).2
    dsimp only [d]
    nlinarith
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hrd : r * d = V := by
    calc
      r * d = d - (lam * d) * b / 3 := by dsimp only [r]; ring
      _ = V := by rw [hlamd]; dsimp only [d]; ring
  have hcr : (1 / (2 * r)) * r = 1 / 2 := by
    calc
      (1 / (2 * r)) * r = (2 : ℝ)⁻¹ * (r⁻¹ * r) := by
        rw [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = 1 / 2 := by rw [inv_mul_cancel₀ hr.ne']; norm_num
  have hcV : (1 / (2 * r)) * V = d / 2 := by
    calc
      (1 / (2 * r)) * V = (1 / (2 * r)) * (r * d) := by rw [hrd]
      _ = ((1 / (2 * r)) * r) * d := by ring
      _ = d / 2 := by rw [hcr]; ring
  have hquad : (1 / (2 * r)) * lam ^ 2 * V = lam * ε / 2 := by
    calc
      (1 / (2 * r)) * lam ^ 2 * V = ((1 / (2 * r)) * V) * lam ^ 2 := by ring
      _ = (d / 2) * lam ^ 2 := by rw [hcV]
      _ = (lam * d) * lam / 2 := by ring
      _ = lam * ε / 2 := by rw [hlamd]; ring
  have hhalf : -(lam * ε) / 2 = -ε ^ 2 / (2 * d) := by
    dsimp only [lam]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hden : 2 * V + 2 * b * ε / 3 = 2 * d := by
    dsimp only [d]
    ring
  have hexponent :
      -lam * ε + 1 / (2 * r) * lam ^ 2 * V =
        -ε ^ 2 / (2 * V + 2 * b * ε / 3) := by
    calc
      -lam * ε + 1 / (2 * r) * lam ^ 2 * V = -(lam * ε) / 2 := by
        rw [hquad]
        ring
      _ = -ε ^ 2 / (2 * d) := hhalf
      _ = -ε ^ 2 / (2 * V + 2 * b * ε / 3) := by rw [hden]
  exact ⟨hlam0, hlamb, one_div_nonneg.mpr (mul_nonneg (by norm_num) hr.le), hexponent⟩

theorem zero_variance_optimizer (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    let lam := 3 / (2 * b)
    0 < lam ∧ lam * b < 3 ∧
      0 ≤ 1 / (2 * (1 - lam * b / 3)) ∧
      -lam * ε = -ε ^ 2 / (2 * b * ε / 3) := by
  let lam : ℝ := 3 / (2 * b)
  have hlam0 : 0 < lam := by
    dsimp only [lam]
    positivity
  have hlamb : lam * b = 3 / 2 := by
    dsimp only [lam]
    field_simp [hb.ne']
  have hlam3 : lam * b < 3 := by rw [hlamb]; norm_num
  have hr : 0 < 1 - lam * b / 3 := by linarith
  have hden : 0 < 2 * b * ε / 3 := by positivity
  have hexponent : -lam * ε = -ε ^ 2 / (2 * b * ε / 3) := by
    apply (eq_div_iff hden.ne').2
    calc
      (-lam * ε) * (2 * b * ε / 3) = -(lam * b) * (2 / 3) * ε ^ 2 := by ring
      _ = -ε ^ 2 := by rw [hlamb]; ring
  exact ⟨hlam0, hlam3, one_div_nonneg.mpr (mul_nonneg (by norm_num) hr.le), hexponent⟩

end BestBothWorlds.SAO.AABernOptimizer

namespace BestBothWorlds.SAO.AABernNull

theorem measure_event_eq_zero_of_variance_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S W : Ω → ℝ) (hW0 : 0 ≤ᵐ[P] W) (ε V : ℝ) (hV : V < 0) :
    P {ω | ε ≤ S ω ∧ W ω ≤ V} = 0 := by
  refine measure_mono_null ?_ (ae_iff.mp hW0)
  intro ω hω hnonneg
  change ε ≤ S ω ∧ W ω ≤ V at hω
  change 0 ≤ W ω at hnonneg
  exact (not_le_of_gt hV) (hnonneg.trans hω.2)

theorem real_event_eq_zero_of_variance_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (S W : Ω → ℝ) (hW0 : 0 ≤ᵐ[P] W) (ε V : ℝ) (hV : V < 0) :
    P.real {ω | ε ≤ S ω ∧ W ω ≤ V} = 0 := by
  show (P {ω | ε ≤ S ω ∧ W ω ≤ V}).toReal = 0
  rw [measure_event_eq_zero_of_variance_neg P S W hW0 ε V hV, ENNReal.toReal_zero]

end BestBothWorlds.SAO.AABernNull

namespace BestBothWorlds.SAO.AABern

theorem chernoff_fixed_parameter {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (S W : Ω → ℝ)
    (ε V c lam : ℝ) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hZint : Integrable (fun ω => Real.exp (lam * S ω - c * lam ^ 2 * W ω)) P)
    (hZmean : (∫ ω, Real.exp (lam * S ω - c * lam ^ 2 * W ω) ∂P) ≤ 1) :
    P.real {ω | ε ≤ S ω ∧ W ω ≤ V} ≤
      Real.exp (-lam * ε + c * lam ^ 2 * V) := by
  let a : ℝ := lam * ε - c * lam ^ 2 * V
  let Z : Ω → ℝ := fun ω => Real.exp (lam * S ω - c * lam ^ 2 * W ω)
  have hsub : {ω | ε ≤ S ω ∧ W ω ≤ V} ⊆ {ω | Real.exp a ≤ Z ω} := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    exact sub_le_sub (mul_le_mul_of_nonneg_left hω.1 hlam)
      (mul_le_mul_of_nonneg_left hω.2 (mul_nonneg hc (sq_nonneg lam)))
  have hmarkov : Real.exp a * P.real {ω | Real.exp a ≤ Z ω} ≤ 1 := by
    exact (mul_meas_ge_le_integral_of_nonneg
      (ae_of_all P fun ω => (Real.exp_pos _).le) hZint (Real.exp a)).trans hZmean
  have hbound : P.real {ω | Real.exp a ≤ Z ω} ≤ 1 / Real.exp a := by
    apply (le_div_iff₀ (Real.exp_pos a)).mpr
    simpa only [mul_comm] using hmarkov
  calc
    P.real {ω | ε ≤ S ω ∧ W ω ≤ V} ≤
        P.real {ω | Real.exp a ≤ Z ω} := measureReal_mono hsub
    _ ≤ 1 / Real.exp a := hbound
    _ = Real.exp (-lam * ε + c * lam ^ 2 * V) := by
      rw [one_div, ← Real.exp_neg]
      congr 1
      dsimp only [a]
      ring

end BestBothWorlds.SAO.AABern

namespace BestBothWorlds.SAO.AABern

theorem chernoff_bernstein {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (S W : Ω → ℝ) (hW0 : 0 ≤ᵐ[P] W)
    (b : ℝ) (hb : 0 < b) (ε V : ℝ) (hε : 0 < ε)
    (hproc : ∀ lam : ℝ, 0 < lam → lam * b < 3 →
      Integrable (fun ω => Real.exp (lam * S ω -
        1 / (2 * (1 - lam * b / 3)) * lam ^ 2 * W ω)) P ∧
      (∫ ω, Real.exp (lam * S ω -
        1 / (2 * (1 - lam * b / 3)) * lam ^ 2 * W ω) ∂P) ≤ 1) :
    P.real {ω | ε ≤ S ω ∧ W ω ≤ V} ≤
      Real.exp (-ε ^ 2 / (2 * V + 2 * b * ε / 3)) := by
  rcases lt_trichotomy V 0 with hVneg | hVzero | hVpos
  · rw [AABernNull.real_event_eq_zero_of_variance_neg P S W hW0 ε V hVneg]
    exact (Real.exp_pos _).le
  · subst V
    obtain ⟨hlam0, hlamb, hc, hexp⟩ :=
      AABernOptimizer.zero_variance_optimizer b ε hb hε
    obtain ⟨hZint, hZmean⟩ := hproc (3 / (2 * b)) hlam0 hlamb
    calc
      P.real {ω | ε ≤ S ω ∧ W ω ≤ (0 : ℝ)} ≤
          Real.exp (-(3 / (2 * b)) * ε +
            1 / (2 * (1 - (3 / (2 * b)) * b / 3)) *
              (3 / (2 * b)) ^ 2 * 0) :=
        chernoff_fixed_parameter P S W ε 0
          (1 / (2 * (1 - (3 / (2 * b)) * b / 3))) (3 / (2 * b))
          hc hlam0.le hZint hZmean
      _ = Real.exp (-ε ^ 2 / (2 * 0 + 2 * b * ε / 3)) := by
        simpa only [mul_zero, add_zero, zero_add] using congrArg Real.exp hexp
  · obtain ⟨hlam0, hlamb, hc, hexp⟩ :=
      AABernOptimizer.positive_variance_optimizer b ε V hb hε hVpos
    obtain ⟨hZint, hZmean⟩ := hproc (ε / (V + b * ε / 3)) hlam0 hlamb
    calc
      P.real {ω | ε ≤ S ω ∧ W ω ≤ V} ≤
          Real.exp (-(ε / (V + b * ε / 3)) * ε +
            1 / (2 * (1 - (ε / (V + b * ε / 3)) * b / 3)) *
              (ε / (V + b * ε / 3)) ^ 2 * V) :=
        chernoff_fixed_parameter P S W ε V
          (1 / (2 * (1 - (ε / (V + b * ε / 3)) * b / 3)))
          (ε / (V + b * ε / 3)) hc hlam0.le hZint hZmean
      _ = Real.exp (-ε ^ 2 / (2 * V + 2 * b * ε / 3)) :=
        congrArg Real.exp hexp

end BestBothWorlds.SAO.AABern

open MeasureTheory

namespace BestBothWorlds.SAO.Owner

open scoped MeasureTheory

/-! Reused verbatim from the accepted TamingMonster Freedman source (round d7ef840c, namespaces
`NativeFreedmanInduction` and `NativeFreedmanStep`); only their autoImplicit option lines are dropped. -/

section Reused

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Integrating a conditional bound. The integrability premise on `Y` is kept explicit
for composition with the process construction; total-integral preservation is unconditional. -/
theorem integral_le_of_condExp_le
    (P : Measure Ω) [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {Y Z : Ω → ℝ}
    (_hY : Integrable Y P) (hZ : Integrable Z P)
    (hstep : P[Y | m] ≤ᵐ[P] Z) :
    (∫ ω, Y ω ∂P) ≤ ∫ ω, Z ω ∂P := by
  calc
    (∫ ω, Y ω ∂P) = ∫ ω, P[Y | m] ω ∂P :=
      (integral_condExp (μ := P) (f := Y) hm).symm
    _ ≤ ∫ ω, Z ω ∂P :=
      integral_mono_ae integrable_condExp hZ hstep

/-- A finite-horizon conditional step decreases the integral at that step. -/
theorem integral_process_step_le
    (P : Measure Ω) [IsFiniteMeasure P]
    (m : ℕ → MeasurableSpace Ω) (process : ℕ → Ω → ℝ)
    (n : ℕ) (hm : m n ≤ mΩ)
    (hnext : Integrable (process (n + 1)) P)
    (hnow : Integrable (process n) P)
    (hstep : P[process (n + 1) | m n] ≤ᵐ[P] process n) :
    (∫ ω, process (n + 1) ω ∂P) ≤ ∫ ω, process n ω ∂P := by
  exact integral_le_of_condExp_le P hm hnext hnow hstep

/-- No adaptedness or monotonicity of `m` is needed once the exact conditional steps
and their integrability have been proved. All premises are exposed to the caller. -/
theorem integral_process_le_one
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ → MeasurableSpace Ω) (process : ℕ → Ω → ℝ)
    (hm : ∀ n, m n ≤ mΩ)
    (hint : ∀ n, Integrable (process n) P)
    (hzero : process 0 =ᵐ[P] fun _ : Ω => (1 : ℝ))
    (hstep : ∀ n, P[process (n + 1) | m n] ≤ᵐ[P] process n)
    (n : ℕ) : (∫ ω, process n ω ∂P) ≤ 1 := by
  induction n with
  | zero =>
      calc
        (∫ ω, process 0 ω ∂P) = ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_congr_ae hzero
        _ ≤ 1 := by simp
  | succ n ih =>
      exact (integral_process_step_le P m process n (hm n)
        (hint (n + 1)) (hint n) (hstep n)).trans ih

/-- Horizon-restricted form: no assumptions at times beyond `T` are required. -/
theorem integral_process_le_one_finite
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (m : ℕ → MeasurableSpace Ω) (process : ℕ → Ω → ℝ)
    (hm : ∀ n, n < T → m n ≤ mΩ)
    (hint : ∀ n, n ≤ T → Integrable (process n) P)
    (hzero : process 0 =ᵐ[P] fun _ : Ω => (1 : ℝ))
    (hstep : ∀ n, n < T → P[process (n + 1) | m n] ≤ᵐ[P] process n) :
    ∀ n, n ≤ T → (∫ ω, process n ω ∂P) ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro _hn
      calc
        (∫ ω, process 0 ω ∂P) = ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_congr_ae hzero
        _ ≤ 1 := by simp
  | succ n ih =>
      intro hn
      have hnlt : n < T := Nat.lt_of_succ_le hn
      have hnle : n ≤ T := Nat.le_of_lt hnlt
      exact (integral_process_step_le P m process n (hm n hnlt)
        (hint (n + 1) hn) (hint n hnle) (hstep n hnlt)).trans (ih hnle)

/-- A conditional exponential bound gives the compensated one-step bound.
All conditional expectations retain their original function representatives. -/
theorem condExp_compensated_step
    (P : Measure Ω) (m : MeasurableSpace Ω)
    (s v x a : Ω → ℝ) (c lam : ℝ)
    (hfactor : StronglyMeasurable[m]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * (v ω + a ω))))
    (hnext : Integrable
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) P)
    (hinc : Integrable (fun ω => Real.exp (lam * x ω)) P)
    (hmgf : condExp m P (fun ω => Real.exp (lam * x ω)) ≤ᵐ[P]
      (fun ω => Real.exp (c * lam ^ 2 * a ω))) :
    condExp m P
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) ≤ᵐ[P]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * v ω)) := by
  let F : Ω → ℝ := fun ω => Real.exp (lam * s ω - c * lam ^ 2 * (v ω + a ω))
  let E : Ω → ℝ := fun ω => Real.exp (lam * x ω)
  have hprod :
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) =
        F * E := by
    funext ω
    change Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    ring
  have hprodInt : Integrable (F * E) P := hprod ▸ hnext
  have hpull : condExp m P (F * E) =ᵐ[P] F * condExp m P E :=
    condExp_mul_of_stronglyMeasurable_left hfactor hprodInt hinc
  rw [hprod]
  filter_upwards [hpull, hmgf] with ω hp hm
  calc
    condExp m P (F * E) ω = F ω * condExp m P E ω := hp
    _ ≤ F ω * Real.exp (c * lam ^ 2 * a ω) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (lam * s ω - c * lam ^ 2 * v ω) := by
      dsimp [F]
      rw [← Real.exp_add]
      congr 1
      ring

/-- The polynomial conditional bound is enough; `1 + z ≤ exp z` supplies
the exponential conditional bound used by the transition theorem. -/
theorem condExp_compensated_step_of_linear_mgf
    (P : Measure Ω) (m : MeasurableSpace Ω)
    (s v x a : Ω → ℝ) (c lam : ℝ)
    (hfactor : StronglyMeasurable[m]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * (v ω + a ω))))
    (hnext : Integrable
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) P)
    (hinc : Integrable (fun ω => Real.exp (lam * x ω)) P)
    (hmgf : condExp m P (fun ω => Real.exp (lam * x ω)) ≤ᵐ[P]
      (fun ω => 1 + c * lam ^ 2 * a ω)) :
    condExp m P
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) ≤ᵐ[P]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * v ω)) := by
  apply condExp_compensated_step (mΩ := mΩ) P m s v x a c lam hfactor hnext hinc
  filter_upwards [hmgf] with ω hω
  exact hω.trans (by simpa [add_comm] using Real.add_one_le_exp (c * lam ^ 2 * a ω))

/-- The upper bound is one-sided: negative increments need no absolute bound. -/
theorem integrable_exp_of_upper_bound
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) {R lam : ℝ} (hlam : 0 ≤ lam)
    (hupper : ∀ᵐ ω ∂P, X ω ≤ R) :
    Integrable (fun ω => Real.exp (lam * X ω)) P := by
  apply (integrable_const (Real.exp (lam * R))).mono'
    ((hX.const_mul lam).exp.aestronglyMeasurable)
  filter_upwards [hupper] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hlam))

/-- The index recurrence is proved from membership, without changing the
frozen `Icc 1 n` convention into a different summation convention. -/
theorem sum_Icc_one_succ (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 (n + 1), f t) =
      (∑ t ∈ Finset.Icc 1 n, f t) + f (n + 1) := by
  have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert hnot]
  ring

/-- Finite-sum form of the compensated transition, ready to instantiate
`A t` by the exact conditional expectation of the squared increment. -/
theorem condExp_sum_process_succ
    (P : Measure Ω) (m : MeasurableSpace Ω)
    (Xs A : ℕ → Ω → ℝ) (c lam : ℝ) (n : ℕ)
    (hfactor : StronglyMeasurable[m]
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) - c * lam ^ 2 *
          ((∑ t ∈ Finset.Icc 1 n, A t ω) + A (n + 1) ω))))
    (hnext : Integrable
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 (n + 1), Xs t ω) - c * lam ^ 2 *
          (∑ t ∈ Finset.Icc 1 (n + 1), A t ω))) P)
    (hinc : Integrable (fun ω => Real.exp (lam * Xs (n + 1) ω)) P)
    (hmgf : condExp m P (fun ω => Real.exp (lam * Xs (n + 1) ω)) ≤ᵐ[P]
      (fun ω => Real.exp (c * lam ^ 2 * A (n + 1) ω))) :
    condExp m P
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 (n + 1), Xs t ω) - c * lam ^ 2 *
          (∑ t ∈ Finset.Icc 1 (n + 1), A t ω))) ≤ᵐ[P]
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) - c * lam ^ 2 *
          (∑ t ∈ Finset.Icc 1 n, A t ω))) := by
  have hnext' : Integrable
      (fun ω => Real.exp
        (lam * ((∑ t ∈ Finset.Icc 1 n, Xs t ω) + Xs (n + 1) ω) -
          c * lam ^ 2 * ((∑ t ∈ Finset.Icc 1 n, A t ω) + A (n + 1) ω))) P := by
    simpa only [sum_Icc_one_succ] using hnext
  simpa only [sum_Icc_one_succ] using
    condExp_compensated_step (mΩ := mΩ) P m
      (fun ω => ∑ t ∈ Finset.Icc 1 n, Xs t ω)
      (fun ω => ∑ t ∈ Finset.Icc 1 n, A t ω)
      (Xs (n + 1)) (A (n + 1)) c lam hfactor hnext' hinc hmgf

end Reused

/-- The Bernstein exponential process `exp(λ S_k − c λ² W_k)` with the exact conditional
variances of the frozen statement: `W_k = ∑_{t ∈ Icc 1 k} E[X_t² | ℱ (t-1)]`. -/
noncomputable def ownerB_proc {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (c lam : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lam * (∑ t ∈ Finset.Icc 1 k, X t ω) -
    c * lam ^ 2 * (∑ t ∈ Finset.Icc 1 k, condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω))

theorem ownerB_proc_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (c lam : ℝ) (k : ℕ) (ω : Ω) :
    0 ≤ ownerB_proc P ℱ X c lam k ω :=
  (Real.exp_pos _).le

/-- The conditional variance sum is almost surely nonnegative. -/
theorem ownerB_condVar_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (k : ℕ) :
    ∀ᵐ ω ∂P, 0 ≤ ∑ t ∈ Finset.Icc 1 k, condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω := by
  have hall : ∀ᵐ ω ∂P, ∀ t : ℕ, 0 ≤ condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω :=
    ae_all_iff.2 (fun t => condExp_nonneg
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (X t ω))))
  filter_upwards [hall] with ω hω
  exact Finset.sum_nonneg (fun t _ht => hω t)

/-- Up to the horizon, the process is a.e. bounded by `exp (λ k b)`. -/
theorem ownerB_proc_ae_le {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (b c lam : ℝ) (hc : 0 ≤ c)
    (hlam : 0 ≤ lam) (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b) {k : ℕ} (hk : k ≤ n) :
    ∀ᵐ ω ∂P, ownerB_proc P ℱ X c lam k ω ≤ Real.exp (lam * ((k : ℝ) * b)) := by
  have hxall : ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 n, |X t ω| ≤ b := by
    refine ae_all_iff.2 ?_
    intro t
    by_cases ht : t ∈ Finset.Icc 1 n
    · exact (hbd t ht).mono (fun _ω hω => fun _hmem => hω)
    · exact Filter.Eventually.of_forall (fun _ω hmem => False.elim (ht hmem))
  filter_upwards [hxall, ownerB_condVar_nonneg P ℱ X k] with ω hx hV
  have hsum : (∑ t ∈ Finset.Icc 1 k, X t ω) ≤ (k : ℝ) * b := by
    calc
      (∑ t ∈ Finset.Icc 1 k, X t ω) ≤ ∑ _t ∈ Finset.Icc 1 k, b := by
        apply Finset.sum_le_sum
        intro t ht
        have htn : t ∈ Finset.Icc 1 n :=
          Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2.trans hk⟩
        exact (le_abs_self _).trans (hx t htn)
      _ = (k : ℝ) * b := by simp
  have hpen : 0 ≤ c * lam ^ 2 *
      (∑ t ∈ Finset.Icc 1 k, condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω) :=
    mul_nonneg (mul_nonneg hc (sq_nonneg lam)) hV
  unfold ownerB_proc
  apply Real.exp_le_exp.mpr
  exact (sub_le_self _ hpen).trans (mul_le_mul_of_nonneg_left hsum hlam)

/-- Up to the horizon, the process is measurable for the ambient σ-algebra. -/
theorem ownerB_proc_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t)) (c lam : ℝ) {k : ℕ} (hk : k ≤ n) :
    Measurable (ownerB_proc P ℱ X c lam k) := by
  have hS : Measurable (fun ω => ∑ t ∈ Finset.Icc 1 k, X t ω) := by
    apply Finset.measurable_sum
    intro t ht
    have htn : t ∈ Finset.Icc 1 n :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2.trans hk⟩
    exact (hmeas t htn).mono (ℱ.le t) le_rfl
  have hV : Measurable (fun ω => ∑ t ∈ Finset.Icc 1 k,
      condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω) := by
    apply Finset.measurable_sum
    intro t _ht
    have hCE : StronglyMeasurable[ℱ (t - 1)]
        (condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2)) := stronglyMeasurable_condExp
    exact (hCE.mono (ℱ.le (t - 1))).measurable
  unfold ownerB_proc
  exact ((hS.const_mul lam).sub (hV.const_mul (c * lam ^ 2))).exp

/-- Up to the horizon, the process is integrable. -/
theorem ownerB_proc_integrable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (b : ℝ)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b) (c lam : ℝ) (hc : 0 ≤ c)
    (hlam : 0 ≤ lam) {k : ℕ} (hk : k ≤ n) :
    Integrable (ownerB_proc P ℱ X c lam k) P := by
  refine (integrable_const (μ := P) (Real.exp (lam * ((k : ℝ) * b)))).mono'
    (ownerB_proc_measurable P ℱ X n hmeas c lam hk).aestronglyMeasurable ?_
  filter_upwards [ownerB_proc_ae_le P ℱ X n b c lam hc hlam hbd hk] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (ownerB_proc_nonneg P ℱ X c lam k ω)] using hω

/-- The step factor `exp(λ S_k − c λ² (W_k + A_{k+1}))` is `ℱ k`-strongly measurable. -/
theorem ownerB_factor {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t)) (c lam : ℝ) {k : ℕ} (hk : k < n) :
    StronglyMeasurable[ℱ k] (fun ω => Real.exp (lam * (∑ t ∈ Finset.Icc 1 k, X t ω) -
      c * lam ^ 2 * ((∑ t ∈ Finset.Icc 1 k, condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω) +
        condExp (ℱ (k + 1 - 1)) P (fun ω' => X (k + 1) ω' ^ 2) ω))) := by
  have hS : Measurable[ℱ k] (fun ω => ∑ t ∈ Finset.Icc 1 k, X t ω) := by
    apply Finset.measurable_sum
    intro t ht
    have hmem := Finset.mem_Icc.mp ht
    exact (hmeas t (Finset.mem_Icc.mpr ⟨hmem.1, by omega⟩)).mono (ℱ.mono hmem.2) le_rfl
  have hV : Measurable[ℱ k] (fun ω => ∑ t ∈ Finset.Icc 1 k,
      condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω) := by
    apply Finset.measurable_sum
    intro t ht
    have hmem := Finset.mem_Icc.mp ht
    have hCE : StronglyMeasurable[ℱ (t - 1)]
        (condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2)) := stronglyMeasurable_condExp
    exact (hCE.mono (ℱ.mono (by omega))).measurable
  have hA : Measurable[ℱ k] (condExp (ℱ (k + 1 - 1)) P (fun ω' => X (k + 1) ω' ^ 2)) := by
    have hCE : StronglyMeasurable[ℱ (k + 1 - 1)]
        (condExp (ℱ (k + 1 - 1)) P (fun ω' => X (k + 1) ω' ^ 2)) := stronglyMeasurable_condExp
    exact (hCE.mono (ℱ.mono (by omega))).measurable
  exact ((hS.const_mul lam).sub ((hV.add hA).const_mul (c * lam ^ 2))).exp.stronglyMeasurable

/-- One conditional step of the supermartingale inequality, from the one-step conditional
moment generating function bound at time `k + 1`. -/
theorem ownerB_step {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (b : ℝ)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b) (c lam : ℝ) (hc : 0 ≤ c)
    (hlam : 0 ≤ lam)
    (hinc : ∀ t ∈ Finset.Icc 1 n, Integrable (fun ω => Real.exp (lam * X t ω)) P)
    (hmgf : ∀ t ∈ Finset.Icc 1 n,
      condExp (ℱ (t - 1)) P (fun ω => Real.exp (lam * X t ω)) ≤ᵐ[P]
        fun ω => Real.exp (c * lam ^ 2 * condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω))
    {k : ℕ} (hk : k < n) :
    condExp (ℱ k) P (ownerB_proc P ℱ X c lam (k + 1)) ≤ᵐ[P] ownerB_proc P ℱ X c lam k := by
  have ht : k + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hnext := ownerB_proc_integrable P ℱ X n b hmeas hbd c lam hc hlam (k := k + 1) (by omega)
  exact condExp_sum_process_succ P (ℱ k) X
    (fun t => condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2)) c lam k
    (ownerB_factor P ℱ X n hmeas c lam hk) hnext (hinc (k + 1) ht) (hmgf (k + 1) ht)

/-- The supermartingale bound `E[exp(λ S_n − c λ² W_n)] ≤ 1`, with integrability, for the given
filtration, from the one-step conditional bounds on `Icc 1 n`. -/
theorem ownerB_process_le_one {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (b : ℝ)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b) (c lam : ℝ) (hc : 0 ≤ c)
    (hlam : 0 ≤ lam)
    (hinc : ∀ t ∈ Finset.Icc 1 n, Integrable (fun ω => Real.exp (lam * X t ω)) P)
    (hmgf : ∀ t ∈ Finset.Icc 1 n,
      condExp (ℱ (t - 1)) P (fun ω => Real.exp (lam * X t ω)) ≤ᵐ[P]
        fun ω => Real.exp (c * lam ^ 2 * condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω)) :
    Integrable (ownerB_proc P ℱ X c lam n) P ∧ ∫ ω, ownerB_proc P ℱ X c lam n ω ∂P ≤ 1 := by
  have hint : ∀ k, k ≤ n → Integrable (ownerB_proc P ℱ X c lam k) P := fun k hk =>
    ownerB_proc_integrable P ℱ X n b hmeas hbd c lam hc hlam hk
  have hzero : ownerB_proc P ℱ X c lam 0 =ᵐ[P] fun _ : Ω => (1 : ℝ) :=
    Filter.Eventually.of_forall (fun ω => by simp [ownerB_proc])
  refine ⟨hint n le_rfl, ?_⟩
  exact integral_process_le_one_finite P n (fun k => ℱ k) (ownerB_proc P ℱ X c lam)
    (fun k _hk => ℱ.le k) hint hzero
    (fun k hk => ownerB_step P ℱ X n b hmeas hbd c lam hc hlam hinc hmgf hk) n le_rfl

end BestBothWorlds.SAO.Owner

namespace BestBothWorlds.SAO

/-- Theorem 4.3, equation (19) (p. 14): Freedman's Bernstein inequality with the paper's
two-sided bound `|X_t| ≤ b` and predictable variation `V_n`. -/
theorem freedman {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (b : ℝ) (hb : 0 < b)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (ε V : ℝ) (hε : 0 < ε) :
    P.real {ω | ε ≤ ∑ t ∈ Finset.Icc 1 n, X t ω ∧
        ∑ t ∈ Finset.Icc 1 n, P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)] ω ≤ V} ≤
      Real.exp (-ε ^ 2 / (2 * V + 2 * b * ε / 3)) := by
  -- `hn` is a frozen binder; the bound holds for every `n`.
  have _hn_frozen : 1 ≤ n := hn
  have hW0 : 0 ≤ᵐ[P] fun ω => ∑ t ∈ Finset.Icc 1 n, P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)] ω :=
    Owner.ownerB_condVar_nonneg P ℱ X n
  refine AABern.chernoff_bernstein P (fun ω => ∑ t ∈ Finset.Icc 1 n, X t ω)
    (fun ω => ∑ t ∈ Finset.Icc 1 n, P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)] ω) hW0 b hb ε V hε ?_
  intro lam hlam0 hlamb
  have hone : ∀ t ∈ Finset.Icc 1 n, Integrable (fun ω => Real.exp (lam * X t ω)) P ∧
      condExp (ℱ (t - 1)) P (fun ω => Real.exp (lam * X t ω)) ≤ᵐ[P]
        fun ω => Real.exp (1 / (2 * (1 - lam * b / 3)) * lam ^ 2 *
          condExp (ℱ (t - 1)) P (fun ω' => X t ω' ^ 2) ω) := fun t ht =>
    GSBern.condExp_exp_le_bernstein (ℱ.le (t - 1)) hb ((hmeas t ht).mono (ℱ.le t) le_rfl)
      (hbd t ht) hlam0 hlamb (hmds t ht)
  have hc : 0 ≤ 1 / (2 * (1 - lam * b / 3)) := one_div_nonneg.mpr (by linarith)
  exact Owner.ownerB_process_le_one P ℱ X n b hmeas hbd (1 / (2 * (1 - lam * b / 3))) lam hc
    hlam0.le (fun t ht => (hone t ht).1) (fun t ht => (hone t ht).2)

end BestBothWorlds.SAO

end Prove2SwarmSubmission

open MeasureTheory
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (b : ℝ) (hb : 0 < b)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (ε V : ℝ) (hε : 0 < ε) :
    P.real {ω | ε ≤ ∑ t ∈ Finset.Icc 1 n, X t ω ∧
        ∑ t ∈ Finset.Icc 1 n, P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)] ω ≤ V} ≤
      Real.exp (-ε ^ 2 / (2 * V + 2 * b * ε / 3)) := by
  exact Prove2SwarmSubmission.BestBothWorlds.SAO.freedman P ℱ X n hn b hb hmeas hmds hbd ε V hε
