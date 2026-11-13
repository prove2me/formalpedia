-- Prove2me | solution 2 for FiniteEnergyPlane.exists_smooth_qPoint_rep
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T22:50:58.472626+00:00
-- url     : https://prove2.me/submissions/4f0cce66-1e97-48be-ae44-026953f1b1f7

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Mathlib
import Theorems.Thm_Nemytskii_exists_contDiff_superposition
import Theorems.Thm_Nemytskii_iteratedFDeriv_bounds_of_comp_compact
import Theorems.Thm_Nemytskii_iteratedFDeriv_bounds_of_partial
import Theorems.Thm_FiniteEnergyPlane_norm_iteratedFDeriv_intervalIntegral_le
import Theorems.Thm_FiniteEnergyPlane_exists_clm_boundedContinuous_rep
import Theorems.Thm_FiniteEnergyPlane_cylJ_iteratedFDeriv_bdd
import Theorems.Thm_FiniteEnergyPlane_memLp_four_of_exp_bound
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv

open Metric Set Filter Topology BoundedContinuousFunction
open Metric Set Filter Topology MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open MeasureTheory Metric Set Filter Topology BoundedContinuousFunction
open scoped ENNReal ContDiff
open Metric Set Filter Topology
open scoped ContDiff



/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-! ### Slope weights are affine near the ends -/

theorem IsSlopeWeight.eq_right {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : 1 ≤ s) : χ s = χ 1 + b * (s - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have hb : deriv χ c = b := h.2.2 c hc.1.le
  rw [hb, eq_div_iff (by linarith)] at hc'
  linarith

theorem IsSlopeWeight.eq_left {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : s ≤ -1) : χ s = χ (-1) + a * (s + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have ha : deriv χ c = a := h.2.1 c hc.2.le
  rw [ha, eq_div_iff (by linarith)] at hc'
  linarith


end FiniteEnergyPlane

/-!
# Nemytskii operators on bounded continuous functions: base layer (spike (e))

`nem Φ u = (x ↦ Φ x (u x))` on `X →ᵇ E`, its continuity, and the pointwise-application
operator `pmul : (X →ᵇ (E →L F)) →L (X →ᵇ E) →L (X →ᵇ F)`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X]
  {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Base hypotheses on `Φ : X → E → F`: joint continuity, boundedness on `X × closedBall 0 R`,
and uniform equicontinuity of `Φ x` on `closedBall 0 R`, uniformly in `x`. -/
structure IsBaseNem (Φ : X → E → F) : Prop where
  cont : Continuous (fun p : X × E => Φ p.1 p.2)
  bdd : ∀ R : ℝ, ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R, ‖Φ x a‖ ≤ C
  ueq : ∀ R : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x, ∀ a ∈ closedBall (0 : E) R,
    ∀ b ∈ closedBall (0 : E) R, ‖a - b‖ < δ → ‖Φ x a - Φ x b‖ < ε

lemma mem_closedBall_norm (u : X →ᵇ E) (x : X) : u x ∈ closedBall (0 : E) ‖u‖ :=
  mem_closedBall_zero_iff.2 (u.norm_coe_le_norm x)

/-- The Nemytskii (superposition) operator. -/
def nem (Φ : X → E → F) (hΦ : IsBaseNem Φ) (u : X →ᵇ E) : X →ᵇ F :=
  ofNormedAddCommGroup (fun x => Φ x (u x))
    (hΦ.cont.comp (continuous_id.prodMk u.continuous)) (hΦ.bdd ‖u‖).choose
    (fun x => (hΦ.bdd ‖u‖).choose_spec x (u x) (mem_closedBall_norm u x))

@[simp] lemma nem_apply (Φ : X → E → F) (hΦ : IsBaseNem Φ) (u : X →ᵇ E) (x : X) :
    nem Φ hΦ u x = Φ x (u x) := rfl

lemma closedBall_succ {u v : X →ᵇ E} (h : dist v u < 1) (x : X) :
    v x ∈ closedBall (0 : E) (‖u‖ + 1) := by
  rw [mem_closedBall_zero_iff]
  have h1 : ‖v x - u x‖ ≤ ‖v - u‖ := by
    simpa using (v - u).norm_coe_le_norm x
  have h2 : ‖v x‖ ≤ ‖u x‖ + ‖v x - u x‖ := by
    simpa using norm_le_insert' (v x) (u x)
  have h3 := u.norm_coe_le_norm x
  rw [dist_eq_norm] at h
  linarith

lemma closedBall_le_succ (u : X →ᵇ E) (x : X) : u x ∈ closedBall (0 : E) (‖u‖ + 1) :=
  closedBall_subset_closedBall (by linarith) (mem_closedBall_norm u x)

/-- Milestone 0: the Nemytskii operator is continuous. -/
theorem continuous_nem (Φ : X → E → F) (hΦ : IsBaseNem Φ) : Continuous (nem Φ hΦ) := by
  refine continuous_iff_continuousAt.2 fun u => Metric.continuousAt_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := hΦ.ueq (‖u‖ + 1) (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ one_pos, fun v hv => ?_⟩
  have hv1 : dist v u < 1 := lt_of_lt_of_le hv (min_le_right _ _)
  have hvδ : dist v u < δ := lt_of_lt_of_le hv (min_le_left _ _)
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun x => ?_)
    (half_lt_self hε)
  rw [nem_apply, nem_apply, dist_eq_norm]
  refine (hδ' x _ (closedBall_succ hv1 x) _ (closedBall_le_succ u x) ?_).le
  exact lt_of_le_of_lt (by simpa [dist_eq_norm] using dist_coe_le_dist (f := v) (g := u) x) hvδ

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pointwise application `(f, g) ↦ (x ↦ B (f x) (g x))` of a continuous bilinear `B`.
(Generic in `G`: elaborating `X →ᵇ (E →L F)` directly picks a non-matching `AddCommMonoid`.) -/
def pmulAux (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : X →ᵇ E) : X →ᵇ F :=
  ofNormedAddCommGroup (fun x => B (f x) (g x))
    ((B.continuous.comp f.continuous).clm_apply g.continuous) (‖B‖ * ‖f‖ * ‖g‖)
    (fun x => (B.le_opNorm₂ (f x) (g x)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg B))
        (g.norm_coe_le_norm x) (norm_nonneg (g x)) (by positivity)))

@[simp] lemma pmulAux_apply (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : X →ᵇ E) (x : X) :
    pmulAux B f g x = B (f x) (g x) := rfl

def pmulL (B : G →L[ℝ] E →L[ℝ] F) : (X →ᵇ G) →ₗ[ℝ] (X →ᵇ E) →ₗ[ℝ] (X →ᵇ F) :=
  LinearMap.mk₂ ℝ (pmulAux B)
    (fun f₁ f₂ g => BoundedContinuousFunction.ext fun x => by simp)
    (fun c f g => BoundedContinuousFunction.ext fun x => by simp)
    (fun f g₁ g₂ => BoundedContinuousFunction.ext fun x => by simp)
    (fun c f g => BoundedContinuousFunction.ext fun x => by simp)

/-- The pointwise-application operator, a continuous bilinear map of norm `≤ ‖B‖`. -/
def pmul (B : G →L[ℝ] E →L[ℝ] F) : (X →ᵇ G) →L[ℝ] (X →ᵇ E) →L[ℝ] (X →ᵇ F) :=
  (pmulL B).mkContinuous₂ ‖B‖ (fun f g => by
      show ‖pmulAux B f g‖ ≤ _
      exact norm_ofNormedAddCommGroup_le _ (by positivity) _)

@[simp] lemma pmul_apply (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : X →ᵇ E) (x : X) :
    pmul B f g x = B (f x) (g x) := rfl

end NEM

/-!
# Q-N sketch: the Nemytskii interface over the published children

The class `UC` is the derivative-bound hypothesis of `Nemytskii.exists_contDiff_superposition`
(the index `n` is kept so the later layers read unchanged). Smoothness of the Nemytskii operator,
and the two ways of producing such integrands, come from the published children
`Nemytskii.exists_contDiff_superposition`, `Nemytskii.iteratedFDeriv_bounds_of_comp_compact` and
`Nemytskii.iteratedFDeriv_bounds_of_partial`. The value map `QN19.U` is the published
`exists_clm_boundedContinuous_rep`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Base hypotheses from bounds on the value and the first value-derivative. -/
theorem isBaseNem_of_bounds {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : X → E → F) (hd : ∀ x, Differentiable ℝ (Φ x))
    (hc : Continuous (fun p : X × E => Φ p.1 p.2))
    (h0 : ∀ R : ℝ, ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R, ‖Φ x a‖ ≤ C)
    (h1 : ∀ R : ℝ, ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R, ‖fderiv ℝ (Φ x) a‖ ≤ C) :
    IsBaseNem Φ := by
  refine ⟨hc, h0, fun R ε hε => ?_⟩
  obtain ⟨C, hC⟩ := h1 R
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨ε / (max C 0 + 1), by positivity, fun x a ha b hb hab => ?_⟩
  have key := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
    (f := Φ x) (fun y _ => (hd x).differentiableAt)
    (fun y hy => (hC x y hy).trans (le_max_left C 0)) hb ha
  calc ‖Φ x a - Φ x b‖ ≤ max C 0 * ‖a - b‖ := key
    _ ≤ (max C 0 + 1) * ‖a - b‖ := by nlinarith [norm_nonneg (a - b)]
    _ < (max C 0 + 1) * (ε / (max C 0 + 1)) := by
        exact mul_lt_mul_of_pos_left hab (by positivity)
    _ = ε := by field_simp

/-- The derivative-bound class: each `Φ x` is `C^∞`, and every value-derivative is jointly
continuous and bounded on `X × closedBall 0 R`. -/
def UC (_n : ℕ) (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : X → E → F) : Prop :=
  (∀ x, ContDiff ℝ ∞ (Φ x)) ∧
    (∀ k : ℕ, Continuous (fun p : X × E => iteratedFDeriv ℝ k (Φ p.1) p.2)) ∧
    ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k (Φ x) a‖ ≤ C

theorem UC.base {n : ℕ} {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : X → E → F}
    (h : UC n F Φ) : IsBaseNem Φ := by
  obtain ⟨hs, hc, hb⟩ := h
  refine isBaseNem_of_bounds Φ (fun x => (hs x).differentiable (by simp)) ?_ ?_ ?_
  · have := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp (hc 0)
    refine this.congr fun p => ?_
    simp [Function.comp]
  · intro R
    obtain ⟨C, hC⟩ := hb 0 R
    exact ⟨C, fun x a ha => by simpa [norm_iteratedFDeriv_zero] using hC x a ha⟩
  · intro R
    obtain ⟨C, hC⟩ := hb 1 R
    refine ⟨C, fun x a ha => ?_⟩
    have h := hC x a ha
    rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h
    exact h

/-- The Nemytskii operator of a `UC` integrand is `C^∞` (published child). -/
theorem contDiff_infty_nem {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : X → E → F) (h : ∀ n, UC n F Φ) (hb : IsBaseNem Φ) :
    ContDiff ℝ ∞ (nem Φ hb) := by
  obtain ⟨hs, hc, hbd⟩ := h 0
  obtain ⟨N, hN, hNe⟩ := Nemytskii.exists_contDiff_superposition Φ hs hc hbd
  have : nem Φ hb = N := funext fun u => by
    ext x
    rw [nem_apply, hNe]
  rw [this]
  exact hN

/-- `UC` through a compact parameter (published child). -/
theorem uc_of_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [ProperSpace E] (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p) (K : Set P)
    (hK : IsCompact K) (hpK : ∀ x, p x ∈ K) (n : ℕ) :
    UC n F (fun x a => Ψ (p x, a)) :=
  Nemytskii.iteratedFDeriv_bounds_of_comp_compact Ψ hΨ p hp K hK hpK

/-- `UC` from bounds along a continuous parameter (published child). -/
theorem uc_of_comp_bdd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p : X → P) (hp : Continuous p)
    (hbd : ∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x, ∀ a ∈ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ k Ψ (p x, a)‖ ≤ C) (n : ℕ) :
    UC n F (fun x a => Ψ (p x, a)) :=
  Nemytskii.iteratedFDeriv_bounds_of_partial Ψ hΨ p hp hbd

end NEM

namespace FiniteEnergyPlane

open CauchyRiemannIndex

namespace QN19

/-- The value map (published child `exists_clm_boundedContinuous_rep`). -/
def U : QDom →L[ℝ] (ℝ × ℝ →ᵇ ℂ × ℂ × ℂ) := Classical.choose exists_clm_boundedContinuous_rep

lemma U_ae (x : QDom) : ∀ᵐ q ∂cylMeasure,
    (U x q).1 = vecToC ((x.1 : Triple 1 4).1 q) ∧ (U x q).2.1 = vecToC ((x.2.2 : Triple 1 4).1 q) ∧
      (U x q).2.2 = x.2.1 :=
  (Classical.choose_spec exists_clm_boundedContinuous_rep x).mono fun q h => by
    have h' : U x q = _ := h
    rw [h']; exact ⟨rfl, rfl, rfl⟩

def UK : ℝ := ‖U‖ + 1

lemma UK_pos : 0 < UK := by unfold UK; positivity

lemma norm_U_apply_le (x : QDom) (q : ℝ × ℝ) : ‖U x q‖ ≤ UK * ‖x‖ :=
  ((U x).norm_coe_le_norm q).trans ((U.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (by unfold UK; linarith) (norm_nonneg x)))

end QN19

end FiniteEnergyPlane

/-!
# Spike (e), milestone 3 piece: multiplication `C_b × Lᵖ → Lᵖ`

For a continuous bilinear `B : G →L E →L F`, `(f, g) ↦ (x ↦ B (f x) (g x))` is a continuous
bilinear map `(X →ᵇ G) →L (Lp E p μ →L Lp F p μ)`. Composed with `NEM.nem`, this gives the
smoothness of `u ↦ Φ(·, u) · g` into `Lᵖ`, which is the shape of the `Jbar(G) ∂ₜG` term of `qMap`.
-/


noncomputable section

namespace NEM

universe u v

variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [SecondCountableTopology X] {μ : Measure X}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E F G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma memLp_mul (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : Lp E p μ) :
    MemLp (fun x => B (f x) (g x)) p μ :=
  (Lp.memLp g).of_le_mul (c := ‖B‖ * ‖f‖)
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((B.continuous.comp f.continuous).aestronglyMeasurable).prodMk (Lp.aestronglyMeasurable g)))
    (ae_of_all _ fun x => (B.le_opNorm₂ (f x) (g x)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg B)) (norm_nonneg _)))

/-- The product as an `Lᵖ` class. -/
def mulLpAux (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : Lp E p μ) : Lp F p μ :=
  (memLp_mul B f g).toLp _

lemma coeFn_mulLpAux (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : Lp E p μ) :
    mulLpAux B f g =ᵐ[μ] fun x => B (f x) (g x) :=
  MemLp.coeFn_toLp _

def mulLpL (B : G →L[ℝ] E →L[ℝ] F) : (X →ᵇ G) →ₗ[ℝ] Lp E p μ →ₗ[ℝ] Lp F p μ :=
  LinearMap.mk₂ ℝ (mulLpAux (μ := μ) B)
    (fun f₁ f₂ g => by
      apply Lp.ext
      filter_upwards [coeFn_mulLpAux B (f₁ + f₂) g, coeFn_mulLpAux B f₁ g, coeFn_mulLpAux B f₂ g,
        Lp.coeFn_add (mulLpAux B f₁ g) (mulLpAux B f₂ g)] with x h h₁ h₂ h₃
      rw [h, h₃, Pi.add_apply, h₁, h₂]; simp)
    (fun c f g => by
      apply Lp.ext
      filter_upwards [coeFn_mulLpAux B (c • f) g, coeFn_mulLpAux B f g,
        Lp.coeFn_smul c (mulLpAux B f g)] with x h h₁ h₂
      rw [h, h₂, Pi.smul_apply, h₁]; simp)
    (fun f g₁ g₂ => by
      apply Lp.ext
      filter_upwards [coeFn_mulLpAux B f (g₁ + g₂), coeFn_mulLpAux B f g₁, coeFn_mulLpAux B f g₂,
        Lp.coeFn_add (mulLpAux B f g₁) (mulLpAux B f g₂), Lp.coeFn_add g₁ g₂]
        with x h h₁ h₂ h₃ h₄
      rw [h, h₃, Pi.add_apply, h₁, h₂, h₄, Pi.add_apply, map_add])
    (fun c f g => by
      apply Lp.ext
      filter_upwards [coeFn_mulLpAux B f (c • g), coeFn_mulLpAux B f g,
        Lp.coeFn_smul c (mulLpAux B f g), Lp.coeFn_smul c g] with x h h₁ h₂ h₃
      rw [h, h₂, Pi.smul_apply, h₁, h₃, Pi.smul_apply, map_smul])

/-- The multiplication operator `C_b × Lᵖ → Lᵖ`, of norm `≤ ‖B‖`. -/
def mulLp (B : G →L[ℝ] E →L[ℝ] F) : (X →ᵇ G) →L[ℝ] Lp E p μ →L[ℝ] Lp F p μ :=
  (mulLpL B).mkContinuous₂ ‖B‖ (fun f g => by
    show ‖mulLpAux B f g‖ ≤ _
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_mulLpAux B f g] with x h
    rw [h]
    exact (B.le_opNorm₂ (f x) (g x)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg B)) (norm_nonneg _)))

lemma coeFn_mulLp (B : G →L[ℝ] E →L[ℝ] F) (f : X →ᵇ G) (g : Lp E p μ) :
    mulLp (μ := μ) B f g =ᵐ[μ] fun x => B (f x) (g x) :=
  coeFn_mulLpAux B f g

/-- Smoothness of the `Φ(·, u) · g` term: `(u, g) ↦ B(Φ(·, u(·)), g)` is `C^∞` from
`C_b × Lᵖ` to `Lᵖ` when `Φ` is in every `UC n`. -/
theorem contDiff_mulLp_nem {E' : Type v} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (B : G →L[ℝ] E →L[ℝ] F) (Φ : X → E' → G) (h : ∀ n, UC n G Φ) (hb : IsBaseNem Φ) :
    ContDiff ℝ ∞ (fun ug : (X →ᵇ E') × Lp E p μ => mulLp (μ := μ) B (nem Φ hb ug.1) ug.2) :=
  ((mulLp (μ := μ) B).contDiff.comp ((contDiff_infty_nem Φ h hb).comp contDiff_fst)).clm_apply
    contDiff_snd

end NEM

/-!
# Q-N, layer 9 (local, NOT published): Nemytskii integrands from derivative bounds

* `NEM.partial_of_bdd`: for `Ψ` jointly `C^∞` on `P × E` with derivative bounds on
  `range p × closedBall 0 R`, the partial maps `a ↦ Ψ (p x, a)` satisfy the hypotheses of
  `uc_of_iteratedFDeriv` / `uc_of_comp_clm` (no compactness).
* `BddDerivOn`, `BddDeriv1On`: smooth maps with bounded derivatives (of order `≥ 1`) on a set;
  closed under bilinear products, composition, sums; CLMs and constants.
-/


noncomputable section



namespace QN9

variable {Y Z W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Smooth with every derivative bounded on `U`. -/
def BddDerivOn (f : Y → Z) (U : Set Y) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C

/-- Smooth with every derivative of order `≥ 1` bounded on `U`. -/
def BddDeriv1On (f : Y → Z) (U : Set Y) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C

lemma BddDerivOn.one {f : Y → Z} {U : Set Y} (h : BddDerivOn f U) : BddDeriv1On f U :=
  ⟨h.1, fun k _ => h.2 k⟩

lemma BddDerivOn.mono {f : Y → Z} {U V : Set Y} (h : BddDerivOn f V) (hUV : U ⊆ V) :
    BddDerivOn f U := ⟨h.1, fun k => (h.2 k).imp fun C hC y hy => hC y (hUV hy)⟩

lemma BddDeriv1On.mono {f : Y → Z} {U V : Set Y} (h : BddDeriv1On f V) (hUV : U ⊆ V) :
    BddDeriv1On f U := ⟨h.1, fun k hk => (h.2 k hk).imp fun C hC y hy => hC y (hUV hy)⟩

/-- A family of bounds, nonnegative. -/
lemma choose_bounds {f : Y → Z} {U : Set Y} (h : ∀ k : ℕ, ∃ C : ℝ, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ k, ∀ y ∈ U, ‖iteratedFDeriv ℝ k f y‖ ≤ C k := by
  choose C hC using h
  exact ⟨fun k => max (C k) 0, fun k => le_max_right _ _,
    fun k y hy => (hC k y hy).trans (le_max_left _ _)⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma BddDerivOn.bilin (B : Z →L[ℝ] W →L[ℝ] V) {f : Y → Z} {g : Y → W} {U : Set Y}
    (hf : BddDerivOn f U) (hg : BddDerivOn g U) :
    BddDerivOn (fun y => B (f y) (g y)) U := by
  refine ⟨B.isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1), fun n => ?_⟩
  obtain ⟨Cf, hCf0, hCf⟩ := choose_bounds hf.2
  obtain ⟨Cg, hCg0, hCg⟩ := choose_bounds hg.2
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Cg (n - i), fun y hy => ?_⟩
  refine (B.norm_iteratedFDeriv_le_of_bilinear hf.1 hg.1 y (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (norm_nonneg B)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hCf i y hy) (Nat.cast_nonneg _)) (hCg (n - i) y hy)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

lemma BddDerivOn.add {f g : Y → Z} {U : Set Y} (hf : BddDerivOn f U) (hg : BddDerivOn g U) :
    BddDerivOn (fun y => f y + g y) U := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨C1, hC1⟩ := hf.2 n
  obtain ⟨C2, hC2⟩ := hg.2 n
  refine ⟨C1 + C2, fun y hy => ?_⟩
  rw [iteratedFDeriv_add_apply' (hf.1.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.1.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hC1 y hy) (hC2 y hy))

lemma BddDeriv1On.add {f g : Y → Z} {U : Set Y} (hf : BddDeriv1On f U) (hg : BddDeriv1On g U) :
    BddDeriv1On (fun y => f y + g y) U := by
  refine ⟨hf.1.add hg.1, fun n hn => ?_⟩
  obtain ⟨C1, hC1⟩ := hf.2 n hn
  obtain ⟨C2, hC2⟩ := hg.2 n hn
  refine ⟨C1 + C2, fun y hy => ?_⟩
  rw [iteratedFDeriv_add_apply' (hf.1.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.1.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hC1 y hy) (hC2 y hy))

lemma bddDerivOn_const (c : Z) (U : Set Y) : BddDerivOn (fun _ : Y => c) U := by
  refine ⟨contDiff_const, fun k => ⟨‖c‖, fun y _ => ?_⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hk.ne' c]; simp

lemma bddDeriv1On_clm (L : Y →L[ℝ] Z) (U : Set Y) : BddDeriv1On L U := by
  refine ⟨L.contDiff, fun k hk => ⟨‖L‖, fun y _ => ?_⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hL : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
  rw [← norm_iteratedFDeriv_fderiv, hL]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hm.ne' L]; simp

/-- **Composition** (Faà di Bruno). -/
lemma BddDerivOn.comp {g : Z → W} {f : Y → Z} {U : Set Y} {V : Set Z} (hg : BddDerivOn g V)
    (hf : BddDeriv1On f U) (hfUV : MapsTo f U V) : BddDerivOn (g ∘ f) U := by
  refine ⟨hg.1.comp hf.1, fun n => ?_⟩
  obtain ⟨Cg, hCg0, hCg⟩ := choose_bounds hg.2
  choose Cf hCf using hf.2
  set C := ∑ i ∈ Finset.range (n + 1), Cg i
  set D := 1 + ∑ i ∈ Finset.range (n + 1), if h : 1 ≤ i then max (Cf i h) 0 else 0
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ i ∈ Finset.range (n + 1), if h : 1 ≤ i then max (Cf i h) 0 else 0 :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> simp
    linarith
  refine ⟨n.factorial * C * D ^ n, fun y hy => ?_⟩
  refine norm_iteratedFDeriv_comp_le hg.1 hf.1 (by exact_mod_cast le_top) y (fun i hi => ?_)
    (fun i hi1 hin => ?_)
  · exact (hCg i (f y) (hfUV hy)).trans (Finset.single_le_sum (fun j _ => hCg0 j)
      (Finset.mem_range.2 (by omega)))
  · have h1 : ‖iteratedFDeriv ℝ i f y‖ ≤ max (Cf i hi1) 0 := (hCf i hi1 y hy).trans (le_max_left _ _)
    have h2 : max (Cf i hi1) 0 ≤ D := by
      have := Finset.single_le_sum (f := fun i => if h : 1 ≤ i then max (Cf i h) 0 else 0)
        (fun j _ => by split_ifs <;> simp) (Finset.mem_range.2 (show i < n + 1 by omega))
      simp only [dif_pos hi1] at this
      linarith
    calc ‖iteratedFDeriv ℝ i f y‖ ≤ D := h1.trans h2
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1

end QN9

/-!
# Q-N, layer 2: the worked `-∞` instance of the `c`-term shortcut (local, NOT published)

The zero-order term `e^{-χ}(Jbar(ψ, v) - jStd)(2πi z, 0)` near `s = -∞`, cut off to `s ≤ 1`, equals
`B(Ψ(p(x), u(x)), m(x))` with
* `m = κ₀(s) e^{-χ(s)} z`, a FIXED function in `L⁴` (independent of `x`'s values and of `c`),
* `Ψ` jointly `C^∞` and `p` continuous with bounded range, so `Ψ(p(·), ·)` lies in every `UC n`,
* `B(G, m) = G(2πi m, 0)` continuous bilinear.
The constant `c` rides in the value variable on the `C_b` side. Hence `u ↦ mulLp B (nem Φ u) m` is
`C^∞` (no weighted Nemytskii operator needed).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex BoundedContinuousFunction
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Cut-offs and the value retraction -/

/-- `lcut j s = 1` for `s ≤ j`, `0` for `s ≥ j + 1`. -/
def lcut (j s : ℝ) : ℝ := 1 - Real.smoothTransition (s - j)

lemma lcut_contDiff (j : ℝ) : ContDiff ℝ ∞ (lcut j) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

lemma lcut_eq_one {j s : ℝ} (h : s ≤ j) : lcut j s = 1 := by
  simp [lcut, Real.smoothTransition.zero_of_nonpos (show s - j ≤ 0 by linarith)]

lemma lcut_eq_zero {j s : ℝ} (h : j + 1 ≤ s) : lcut j s = 0 := by
  simp [lcut, Real.smoothTransition.one_of_one_le (show 1 ≤ s - j by linarith)]

lemma lcut_nonneg (j s : ℝ) : 0 ≤ lcut j s := by
  simp [lcut, Real.smoothTransition.le_one]

lemma lcut_le_one (j s : ℝ) : lcut j s ≤ 1 := by
  simp [lcut, Real.smoothTransition.nonneg]

/-- A smooth map `ℂ → ℂ`, the identity on `ball 0 (ρ/4)`, with values in `ball 0 ρ`. -/
def rtr (ρ : ℝ) (v : ℂ) : ℂ :=
  ((1 - Real.smoothTransition (Complex.normSq v / (ρ / 4) ^ 2 - 1) : ℝ) : ℂ) * v

lemma rtr_contDiff (ρ : ℝ) : ContDiff ℝ ∞ (rtr ρ) := by
  have hn : ContDiff ℝ ∞ (fun v : ℂ => Complex.normSq v) := by
    have : (fun v : ℂ => Complex.normSq v) = fun v => v.re * v.re + v.im * v.im := by
      funext v; rw [Complex.normSq_apply]
    rw [this]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hs : ContDiff ℝ ∞ (fun v : ℂ =>
      1 - Real.smoothTransition (Complex.normSq v / (ρ / 4) ^ 2 - 1)) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((hn.div_const _).sub contDiff_const))
  exact (Complex.ofRealCLM.contDiff.comp hs).mul contDiff_id

lemma rtr_eq {ρ : ℝ} (hρ : 0 < ρ) {v : ℂ} (hv : ‖v‖ < ρ / 4) : rtr ρ v = v := by
  have h1 : Complex.normSq v < (ρ / 4) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_lt_pow_left₀ hv (norm_nonneg _) two_ne_zero
  have h2 : Complex.normSq v / (ρ / 4) ^ 2 - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one (by positivity)]; exact h1.le
  simp [rtr, Real.smoothTransition.zero_of_nonpos h2]

lemma norm_rtr_lt {ρ : ℝ} (hρ : 0 < ρ) (v : ℂ) : ‖rtr ρ v‖ < ρ := by
  set σ := 1 - Real.smoothTransition (Complex.normSq v / (ρ / 4) ^ 2 - 1)
  have hσ0 : 0 ≤ σ := by simp [σ, Real.smoothTransition.le_one]
  have hσ1 : σ ≤ 1 := by simp [σ, Real.smoothTransition.nonneg]
  have hnorm : ‖rtr ρ v‖ = σ * ‖v‖ := by
    simp only [rtr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0, σ]
  rw [hnorm]
  by_cases hv : Complex.normSq v / (ρ / 4) ^ 2 - 1 < 1
  · have h2 : ‖v‖ ^ 2 < ρ ^ 2 := by
      have h3 : Complex.normSq v < 2 * (ρ / 4) ^ 2 := by
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < (ρ / 4) ^ 2)).1 (by linarith : _ < (2 : ℝ))
        linarith
      rw [← Complex.normSq_eq_norm_sq]; nlinarith
    have h4 : ‖v‖ < ρ := lt_of_pow_lt_pow_left₀ 2 hρ.le h2
    calc σ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hσ1 (norm_nonneg _)
      _ < ρ := by linarith
  · have : σ = 0 := by
      simp [σ, Real.smoothTransition.one_of_one_le (not_lt.1 hv)]
    rw [this, zero_mul]; exact hρ

/-! ### Bounds for functions of `s` -/

/-- A continuous `g`, bounded on `(-∞, -1]` and zero on `[A, ∞)`, is bounded. -/
lemma bdd_of_left_bdd (g : ℝ → ℝ) (hg : Continuous g) (A D : ℝ) (hA : ∀ s ≥ A, g s = 0)
    (hD : ∀ s ≤ -1, |g s| ≤ D) : ∃ M, 0 ≤ M ∧ ∀ s, |g s| ≤ M := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := A)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (max B D) 0, le_max_right _ _, fun s => ?_⟩
  rcases le_or_gt s (-1) with h | h
  · exact (hD s h).trans ((le_max_right _ _).trans (le_max_left _ _))
  rcases le_or_gt A s with h' | h'
  · rw [hA s h', abs_zero]; exact le_max_right _ _
  · exact (hB s ⟨h.le, h'.le⟩).trans ((le_max_left _ _).trans (le_max_left _ _))

/-- A continuous `g` with `|g s| ≤ D e^{κ s}` on `(-∞, -1]` and `g = 0` on `[A, ∞)` satisfies
`|g s| ≤ C e^{-κ|s|}`. -/
lemma exp_bound_of_left (g : ℝ → ℝ) (hg : Continuous g) (κ : ℝ) (hκ : 0 < κ) (A D : ℝ)
    (hA : ∀ s ≥ A, g s = 0) (hD : ∀ s ≤ -1, |g s| ≤ D * Real.exp (κ * s)) :
    ∃ C, ∀ s, |g s| ≤ C * Real.exp (-(κ * |s|)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := A)).exists_bound_of_continuousOn
    hg.continuousOn
  set L := max 1 |A|
  refine ⟨max D (max B 0 * Real.exp (κ * L)), fun s => ?_⟩
  rcases le_or_gt s (-1) with h | h
  · have hs : |s| = -s := abs_of_neg (by linarith)
    rw [hs, mul_neg, neg_neg]
    refine (hD s h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  rcases le_or_gt A s with h' | h'
  · rw [hA s h', abs_zero]
    have hD0 : 0 ≤ max D (max B 0 * Real.exp (κ * L)) :=
      le_trans (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le) (le_max_right _ _)
    exact mul_nonneg hD0 (Real.exp_pos _).le
  · have hsL : |s| ≤ L := by
      rw [abs_le]; constructor
      · have := le_max_left 1 |A|; linarith
      · have := le_abs_self A; have := le_max_right 1 |A|; linarith
    have hgs : |g s| ≤ max B 0 := (hB s ⟨h.le, h'.le⟩).trans (le_max_left _ _)
    have he : 1 ≤ Real.exp (κ * L) * Real.exp (-(κ * |s|)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    calc |g s| ≤ max B 0 * 1 := by simpa using hgs
      _ ≤ max B 0 * (Real.exp (κ * L) * Real.exp (-(κ * |s|))) :=
          mul_le_mul_of_nonneg_left he (le_max_right _ _)
      _ = (max B 0 * Real.exp (κ * L)) * Real.exp (-(κ * |s|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

lemma n2_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma continuous_cylInf : Continuous (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  unfold cylInf ccwLoop
  fun_prop

/-- `e^{χ}` is bounded on `(-∞, -1]` for a weight with slope `π` there. -/
lemma exp_le_left {χ : ℝ → ℝ} {b : ℝ} (h : IsSlopeWeight χ π b) {s : ℝ} (hs : s ≤ -1) :
    Real.exp (χ s) ≤ Real.exp (χ (-1)) := by
  rw [h.eq_left hs]; exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-! ### The worked instance -/

/-- The bilinear map `B(G, m) = G(2πi m, 0)`. -/
def bZero : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] ℂ →L[ℝ] ℂ × ℂ :=
  (ContinuousLinearMap.compL ℝ ℂ (ℂ × ℂ) (ℂ × ℂ)).flip
    ((ContinuousLinearMap.inl ℝ ℂ ℂ).comp
      ((((2 * π : ℝ) : ℂ) * Complex.I) • ContinuousLinearMap.id ℝ ℂ))

lemma bZero_apply (G : ℂ × ℂ →L[ℝ] ℂ × ℂ) (m : ℂ) :
    bZero G m = G (((2 * π : ℝ) : ℂ) * Complex.I * m, 0) := by
  simp [bZero]

/-- The compact parameter: `(κ₁, κ₂ z, κ₂ e^{χT}, β, κ₂ e^{χ})`. -/
def pLeft (χT χ β : ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℂ × ℝ × ℝ × ℝ :=
  (lcut 1 q.1, (lcut 2 q.1 : ℂ) * cylInf q.1 q.2, lcut 2 q.1 * Real.exp (χT q.1), β q.1,
    lcut 2 q.1 * Real.exp (χ q.1))

/-- The jointly smooth integrand, in the value `(uT, uN, c)`. -/
def psiLeft (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (y : (ℝ × ℂ × ℝ × ℝ × ℝ) × (ℂ × ℂ × ℂ)) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  y.1.1 • (Jbar (y.1.2.1 + (y.1.2.2.1 : ℂ) * y.2.1,
    rtr ρ ((y.1.2.2.2.1 : ℂ) * y.2.2.2 + (y.1.2.2.2.2 : ℂ) * y.2.2.1)) - jStd)

lemma psiLeft_contDiff (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) : ContDiff ℝ ∞ (psiLeft ρ Jbar) := by
  have hR : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hin : ContDiff ℝ ∞ (fun y : (ℝ × ℂ × ℝ × ℝ × ℝ) × (ℂ × ℂ × ℂ) =>
      (y.1.2.1 + (y.1.2.2.1 : ℂ) * y.2.1,
        rtr ρ ((y.1.2.2.2.1 : ℂ) * y.2.2.2 + (y.1.2.2.2.2 : ℂ) * y.2.2.1))) := by
    refine ContDiff.prodMk ?_ ((rtr_contDiff ρ).comp ?_)
    · exact (contDiff_fst.comp (contDiff_snd.comp contDiff_fst)).add
        ((hR.comp (contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_fst)))).mul
          (contDiff_fst.comp contDiff_snd))
    · exact ((hR.comp (contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp
          (contDiff_snd.comp contDiff_fst))))).mul
          (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))).add
        ((hR.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp
          (contDiff_snd.comp contDiff_fst))))).mul
          (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)))
  have hmaps : ∀ y : (ℝ × ℂ × ℝ × ℝ × ℝ) × (ℂ × ℂ × ℂ),
      (y.1.2.1 + (y.1.2.2.1 : ℂ) * y.2.1,
        rtr ρ ((y.1.2.2.2.1 : ℂ) * y.2.2.2 + (y.1.2.2.2.2 : ℂ) * y.2.2.1)) ∈
        Set.univ ×ˢ ball (0 : ℂ) ρ :=
    fun y => ⟨mem_univ _, mem_ball_zero_iff.2 (norm_rtr_lt hρ _)⟩
  exact (contDiff_fst.comp contDiff_fst).smul ((hJ.comp_contDiff hin hmaps).sub contDiff_const)

lemma pLeft_continuous {χT χ β : ℝ → ℝ} (hχT : Continuous χT) (hχ : Continuous χ)
    (hβ : Continuous β) : Continuous (pLeft χT χ β) := by
  have h1 := (lcut_contDiff 1).continuous
  have h2 := (lcut_contDiff 2).continuous
  unfold pLeft
  refine (h1.comp continuous_fst).prodMk ?_
  refine ((Complex.continuous_ofReal.comp (h2.comp continuous_fst)).mul continuous_cylInf).prodMk ?_
  refine ((h2.comp continuous_fst).mul (Real.continuous_exp.comp (hχT.comp continuous_fst))).prodMk ?_
  exact (hβ.comp continuous_fst).prodMk
    ((h2.comp continuous_fst).mul (Real.continuous_exp.comp (hχ.comp continuous_fst)))

lemma pLeft_bdd {χT χ β : ℝ → ℝ} {bT b : ℝ} (hχT : IsSlopeWeight χT π bT)
    (hχ : IsSlopeWeight χ π b) (hβ : IsLeftCutoff β) :
    ∃ M, ∀ q, ‖pLeft χT χ β q‖ ≤ M := by
  have h2 := (lcut_contDiff 2).continuous
  have hcT : Continuous χT := hχT.1.continuous
  have hc : Continuous χ := hχ.1.continuous
  have hcβ : Continuous β := hβ.1.continuous
  have hl2 : ∀ s, |lcut 2 s| ≤ 1 := fun s => by
    rw [abs_of_nonneg (lcut_nonneg _ _)]; exact lcut_le_one _ _
  have hz3 : ∀ s ≥ (3 : ℝ), lcut 2 s = 0 := fun s hs => lcut_eq_zero (by linarith)
  obtain ⟨M2, -, hM2⟩ := bdd_of_left_bdd (fun s => lcut 2 s * Real.exp (2 * π * s))
    (h2.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))) 3 1
    (fun s hs => by simp [hz3 s hs]) (fun s hs => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |lcut 2 s| * Real.exp (2 * π * s) ≤ 1 * 1 :=
            mul_le_mul (hl2 s) (Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos]))
              (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1)
  obtain ⟨M3, -, hM3⟩ := bdd_of_left_bdd (fun s => lcut 2 s * Real.exp (χT s))
    (h2.mul (Real.continuous_exp.comp hcT)) 3 (Real.exp (χT (-1)))
    (fun s hs => by simp [hz3 s hs]) (fun s hs => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |lcut 2 s| * Real.exp (χT s) ≤ 1 * Real.exp (χT (-1)) :=
            mul_le_mul (hl2 s) (exp_le_left hχT hs) (Real.exp_pos _).le zero_le_one
        _ = _ := one_mul _)
  obtain ⟨M4, -, hM4⟩ := bdd_of_left_bdd β hcβ 0 1 (fun s hs => hβ.2.2 s hs)
    (fun s hs => by rw [hβ.2.1 s hs]; simp)
  obtain ⟨M5, -, hM5⟩ := bdd_of_left_bdd (fun s => lcut 2 s * Real.exp (χ s))
    (h2.mul (Real.continuous_exp.comp hc)) 3 (Real.exp (χ (-1)))
    (fun s hs => by simp [hz3 s hs]) (fun s hs => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |lcut 2 s| * Real.exp (χ s) ≤ 1 * Real.exp (χ (-1)) :=
            mul_le_mul (hl2 s) (exp_le_left hχ hs) (Real.exp_pos _).le zero_le_one
        _ = _ := one_mul _)
  set M := max (max 1 M2) (max M3 (max M4 M5))
  refine ⟨M, fun q => ?_⟩
  simp only [pLeft, norm_prod_le_iff, Real.norm_eq_abs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (lcut_nonneg _ _)]
    exact (lcut_le_one _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, n2_norm_cylInf]
    have := hM2 q.1
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hM3 q.1).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hM4 q.1).trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  · exact (hM5 q.1).trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))

/-- The fixed `L⁴` factor `m = κ₀(s) e^{-χ(s)} z`. -/
def mLeft (χ : ℝ → ℝ) (q : ℝ × ℝ) : ℂ :=
  ((lcut 0 q.1 * Real.exp (-χ q.1) : ℝ) : ℂ) * cylInf q.1 q.2

lemma mLeft_memLp {χ : ℝ → ℝ} {b : ℝ} (hχ : IsSlopeWeight χ π b) :
    MemLp (mLeft χ) 4 cylMeasure := by
  have hc : Continuous χ := hχ.1.continuous
  have h0 := (lcut_contDiff 0).continuous
  have hcont : Continuous (mLeft χ) := by
    unfold mLeft
    exact (Complex.continuous_ofReal.comp ((h0.comp continuous_fst).mul
      (Real.continuous_exp.comp (hc.comp continuous_fst).neg))).mul continuous_cylInf
  obtain ⟨C, hC⟩ := exp_bound_of_left
    (fun s => lcut 0 s * Real.exp (-χ s) * Real.exp (2 * π * s))
    ((h0.mul (Real.continuous_exp.comp hc.neg)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    π Real.pi_pos 1 (Real.exp (-χ (-1) - π))
    (fun s hs => by simp [lcut_eq_zero (show (0 : ℝ) + 1 ≤ s by linarith)])
    (fun s hs => by
      have hl : |lcut 0 s| ≤ 1 := by
        rw [abs_of_nonneg (lcut_nonneg _ _)]; exact lcut_le_one _ _
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
        mul_assoc, ← Real.exp_add, hχ.eq_left hs]
      have he : Real.exp (-(χ (-1) + π * (s + 1)) + 2 * π * s) =
          Real.exp (-χ (-1) - π) * Real.exp (π * s) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he]
      calc |lcut 0 s| * (Real.exp (-χ (-1) - π) * Real.exp (π * s))
          ≤ 1 * (Real.exp (-χ (-1) - π) * Real.exp (π * s)) :=
            mul_le_mul_of_nonneg_right hl (by positivity)
        _ = _ := one_mul _)
  refine memLp_four_of_exp_bound (mLeft χ) hcont.aestronglyMeasurable C π Real.pi_pos
    (fun s t => ?_)
  have := hC s
  simp only [mLeft, norm_mul, Complex.norm_real, Real.norm_eq_abs, n2_norm_cylInf]
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (2 * π * s))] at this
  simpa [abs_mul, mul_assoc] using this

lemma clm_apply_real_mul (X : ℂ × ℂ →L[ℝ] ℂ × ℂ) (r : ℝ) (z : ℂ) :
    X (((2 * π : ℝ) : ℂ) * Complex.I * ((r : ℂ) * z), 0) =
      r • X (((2 * π : ℝ) : ℂ) * Complex.I * z, 0) := by
  rw [← X.map_smul]
  congr 1
  ext <;> simp [Complex.real_smul] <;> ring

/-- The Nemytskii integrand `Φ(q, a) = Ψ(p(q), a)`. -/
def phiLeft (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χ β : ℝ → ℝ) (q : ℝ × ℝ)
    (a : ℂ × ℂ × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  psiLeft ρ Jbar (pLeft χT χ β q, a)

/-- **The `c`-term shortcut, worked instance at `-∞`.** The cut-off zero-order term
`κ₀ e^{-χ}(Jbar(ψ, v) - jStd)(2πi z, 0)`, with `ψ = z + e^{χT} uT` and `v = β c + e^{χ} uN`, is
`B(Φ(·, u), m)` for a FIXED `m ∈ L⁴` and a Nemytskii integrand `Φ` in every `UC n`; hence it is a
`C^∞` function of `u = (uT, uN, c) ∈ C_b` with values in `L⁴`. -/
theorem cTerm_left_shortcut (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) (χT χ β : ℝ → ℝ) (bT b : ℝ)
    (hχT : IsSlopeWeight χT π bT) (hχ : IsSlopeWeight χ π b) (hβ : IsLeftCutoff β) :
    ∃ (Φ : ℝ × ℝ → ℂ × ℂ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ)) (hΦ : NEM.IsBaseNem Φ)
      (mL : MeasureTheory.Lp ℂ 4 cylMeasure),
      (∀ n, NEM.UC n _ Φ) ∧
      ContDiff ℝ ∞ (fun u : ℝ × ℝ →ᵇ ℂ × ℂ × ℂ =>
        NEM.mulLp (μ := cylMeasure) bZero (NEM.nem Φ hΦ u) mL) ∧
      ∀ u : ℝ × ℝ →ᵇ ℂ × ℂ × ℂ,
        (∀ q, ‖(β q.1 : ℂ) * (u q).2.2 + (Real.exp (χ q.1) : ℂ) * (u q).2.1‖ < ρ / 4) →
        (NEM.mulLp (μ := cylMeasure) bZero (NEM.nem Φ hΦ u) mL : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure]
          fun q => (lcut 0 q.1 * Real.exp (-χ q.1)) •
            (Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * (u q).1,
                (β q.1 : ℂ) * (u q).2.2 + (Real.exp (χ q.1) : ℂ) * (u q).2.1) - jStd)
              (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0) := by
  obtain ⟨M, hM⟩ := pLeft_bdd hχT hχ hβ
  have hUC : ∀ n, NEM.UC n _ (phiLeft ρ Jbar χT χ β) := fun n =>
    NEM.uc_of_comp (ℂ × ℂ →L[ℝ] ℂ × ℂ) (psiLeft ρ Jbar) (psiLeft_contDiff ρ hρ Jbar hJ)
      (pLeft χT χ β) (pLeft_continuous hχT.1.continuous hχ.1.continuous hβ.1.continuous)
      (closedBall 0 M) (isCompact_closedBall 0 M) (fun q => mem_closedBall_zero_iff.2 (hM q)) n
  have hb : NEM.IsBaseNem (phiLeft ρ Jbar χT χ β) := (hUC 0).base
  have hm := mLeft_memLp hχ
  refine ⟨phiLeft ρ Jbar χT χ β, hb, hm.toLp _, hUC, ?_, fun u hu => ?_⟩
  · have hcd := NEM.contDiff_mulLp_nem (μ := cylMeasure) (p := 4) (E' := ℂ × ℂ × ℂ) bZero
      (phiLeft ρ Jbar χT χ β) hUC hb
    have hpair : ContDiff ℝ ∞ (fun u : ℝ × ℝ →ᵇ ℂ × ℂ × ℂ => (u, hm.toLp (mLeft χ))) :=
      contDiff_id.prodMk contDiff_const
    have := hcd.comp hpair
    unfold Function.comp at this
    exact this
  · filter_upwards [NEM.coeFn_mulLp (μ := cylMeasure) bZero (NEM.nem _ hb u) (hm.toLp _),
      hm.coeFn_toLp] with q h1 h2
    rw [h1, h2, NEM.nem_apply, bZero_apply]
    simp only [phiLeft, psiLeft, pLeft, mLeft]
    rcases lt_or_ge q.1 1 with hs | hs
    · rw [lcut_eq_one (show q.1 ≤ 1 from hs.le), lcut_eq_one (show q.1 ≤ 2 by linarith)]
      simp only [Complex.ofReal_one, one_mul, one_smul]
      rw [rtr_eq hρ (hu q)]
      exact clm_apply_real_mul _ _ _
    · rw [lcut_eq_zero (show (0 : ℝ) + 1 ≤ q.1 by linarith)]
      simp only [zero_mul, Complex.ofReal_zero, mul_zero, zero_smul]
      exact map_zero _

end

end FiniteEnergyPlane

/-!
# Q-N, layer 10 (local, NOT published): bounded-derivative toolkit, part 1

* `bddDerivOn_of_outside`: smooth, derivatives bounded outside a compact set ⇒ bounded everywhere.
* `BddDerivOn.comp_contDiffOn`: composition with an outer map smooth only on an open set.
* `BddDeriv1On.comp_clm`, `BddDeriv1On.clm_comp`, `BddDerivOn.clm_comp`.
* `rtr ρ` has bounded derivatives; the smooth floor `sfl a` (`≥ a`, `= id` on `[a + 1, ∞)`).
-/

namespace FiniteEnergyPlane

open Metric Set Filter Topology
open scoped ContDiff

noncomputable section

namespace QN10

open QN9

variable {Y Z W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Bounds outside a compact set suffice (`k ≥ k₀`). -/
lemma bdd_of_outside [FiniteDimensional ℝ Y] {f : Y → Z} (hf : ContDiff ℝ ∞ f) {K : Set Y}
    (hK : IsCompact K) (k : ℕ) {C : ℝ} (hC : ∀ y ∉ K, ‖iteratedFDeriv ℝ k f y‖ ≤ C) :
    ∃ C', ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ C' := by
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).continuousOn
  refine ⟨max C C₁, fun y => ?_⟩
  by_cases hy : y ∈ K
  · exact (hC₁ y hy).trans (le_max_right _ _)
  · exact (hC y hy).trans (le_max_left _ _)

/-- Composition with an outer map smooth on an open set `t`, bounded on `V ⊆ t`. -/
lemma comp_contDiffOn {g : Z → W} {f : Y → Z} {t V : Set Z} (ht : IsOpen t)
    (hg : ContDiffOn ℝ ∞ g t) (hgV : ∀ k : ℕ, ∃ C, ∀ z ∈ V, ‖iteratedFDeriv ℝ k g z‖ ≤ C)
    (hVt : V ⊆ t) (hf : BddDeriv1On f univ) (hfV : ∀ y, f y ∈ V) :
    BddDerivOn (g ∘ f) univ := by
  have hft : MapsTo f univ t := fun y _ => hVt (hfV y)
  have hgf : ContDiff ℝ ∞ (g ∘ f) :=
    contDiffOn_univ.1 (hg.comp hf.1.contDiffOn hft)
  refine ⟨hgf, fun n => ?_⟩
  obtain ⟨Cg, hCg0, hCg⟩ := choose_bounds hgV
  choose Cf hCf using hf.2
  set C := ∑ i ∈ Finset.range (n + 1), Cg i
  set D := 1 + ∑ i ∈ Finset.range (n + 1), if h : 1 ≤ i then max (Cf i h) 0 else 0
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ i ∈ Finset.range (n + 1), if h : 1 ≤ i then max (Cf i h) 0 else 0 :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> simp
    linarith
  refine ⟨n.factorial * C * D ^ n, fun y _ => ?_⟩
  have key := norm_iteratedFDerivWithin_comp_le (n := n) (N := ∞) hg hf.1.contDiffOn
    (by exact_mod_cast le_top) ht.uniqueDiffOn uniqueDiffOn_univ hft (mem_univ y)
    (C := C) (D := D) (fun i hi => ?_) (fun i hi1 hin => ?_)
  · rwa [iteratedFDerivWithin_univ] at key
  · rw [iteratedFDerivWithin_of_isOpen i ht (hVt (hfV y))]
    exact (hCg i (f y) (hfV y)).trans (Finset.single_le_sum (fun j _ => hCg0 j)
      (Finset.mem_range.2 (by omega)))
  · rw [iteratedFDerivWithin_univ]
    have h1 : ‖iteratedFDeriv ℝ i f y‖ ≤ max (Cf i hi1) 0 :=
      (hCf i hi1 y (mem_univ y)).trans (le_max_left _ _)
    have h2 : max (Cf i hi1) 0 ≤ D := by
      have := Finset.single_le_sum (f := fun i => if h : 1 ≤ i then max (Cf i h) 0 else 0)
        (fun j _ => by split_ifs <;> simp) (Finset.mem_range.2 (show i < n + 1 by omega))
      simp only [dif_pos hi1] at this
      linarith
    calc ‖iteratedFDeriv ℝ i f y‖ ≤ D := h1.trans h2
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1

lemma BddDeriv1On.comp_clm {f : Z → W} (hf : BddDeriv1On f univ) (L : Y →L[ℝ] Z) :
    BddDeriv1On (f ∘ L) univ := by
  refine ⟨hf.1.comp L.contDiff, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 k hk
  refine ⟨C * ‖L‖ ^ k, fun y _ => ?_⟩
  rw [L.iteratedFDeriv_comp_right hf.1 y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hC _ (mem_univ _)) (by positivity)

lemma BddDerivOn.comp_clm {f : Z → W} (hf : BddDerivOn f univ) (L : Y →L[ℝ] Z) :
    BddDerivOn (f ∘ L) univ := by
  refine ⟨hf.1.comp L.contDiff, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 k
  refine ⟨C * ‖L‖ ^ k, fun y _ => ?_⟩
  rw [L.iteratedFDeriv_comp_right hf.1 y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hC _ (mem_univ _)) (by positivity)

lemma BddDeriv1On.clm_comp {f : Y → Z} {U : Set Y} (hf : BddDeriv1On f U) (L : Z →L[ℝ] W) :
    BddDeriv1On (L ∘ f) U := by
  refine ⟨L.contDiff.comp hf.1, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 k hk
  refine ⟨‖L‖ * C, fun y hy => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left hf.1.contDiffAt (by exact_mod_cast le_top)).trans
    (mul_le_mul_of_nonneg_left (hC y hy) (norm_nonneg _))

lemma BddDerivOn.clm_comp {f : Y → Z} {U : Set Y} (hf : BddDerivOn f U) (L : Z →L[ℝ] W) :
    BddDerivOn (L ∘ f) U := by
  refine ⟨L.contDiff.comp hf.1, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 k
  refine ⟨‖L‖ * C, fun y hy => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left hf.1.contDiffAt (by exact_mod_cast le_top)).trans
    (mul_le_mul_of_nonneg_left (hC y hy) (norm_nonneg _))

/-! ### The retraction and the smooth floor -/

lemma rtr_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {v : ℂ} (hv : ρ / 2 < ‖v‖) : rtr ρ v = 0 := by
  have h1 : 1 ≤ Complex.normSq v / (ρ / 4) ^ 2 - 1 := by
    rw [Complex.normSq_eq_norm_sq, le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    nlinarith
  simp [rtr, Real.smoothTransition.one_of_one_le h1]

lemma bddDerivOn_rtr {ρ : ℝ} (hρ : 0 < ρ) : BddDerivOn (rtr ρ) univ := by
  refine ⟨rtr_contDiff ρ, fun k => ?_⟩
  refine (bdd_of_outside (rtr_contDiff ρ) (isCompact_closedBall (0 : ℂ) (ρ / 2)) k
    (C := 0) fun y hy => ?_).imp fun C' h y _ => h y
  rw [mem_closedBall_zero_iff, not_le] at hy
  have hev : rtr ρ =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with v hv
    exact rtr_eq_zero hρ hv
  rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [iteratedFDeriv_const_of_ne hk.ne']; simp

/-- The smooth floor: `≥ a`, equal to `s` for `s ≥ a + 1`, to `a + 1` for `s ≤ a`. -/
def sfl (a s : ℝ) : ℝ := a + 1 + (s - a - 1) * Real.smoothTransition (s - a)

lemma sfl_contDiff (a : ℝ) : ContDiff ℝ ∞ (sfl a) :=
  contDiff_const.add (((contDiff_id.sub contDiff_const).sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))

lemma sfl_eq {a s : ℝ} (hs : a + 1 ≤ s) : sfl a s = s := by
  simp [sfl, Real.smoothTransition.one_of_one_le (show 1 ≤ s - a by linarith)]

lemma sfl_eq_left {a s : ℝ} (hs : s ≤ a) : sfl a s = a + 1 := by
  simp [sfl, Real.smoothTransition.zero_of_nonpos (show s - a ≤ 0 by linarith)]

lemma le_sfl (a s : ℝ) : a ≤ sfl a s := by
  unfold sfl
  have h0 := Real.smoothTransition.nonneg (s - a)
  have h1 := Real.smoothTransition.le_one (s - a)
  rcases le_or_gt (a + 1) s with h | h
  · nlinarith
  · rcases le_or_gt s a with h' | h'
    · rw [Real.smoothTransition.zero_of_nonpos (show s - a ≤ 0 by linarith)]; linarith
    · nlinarith

lemma bddDeriv1On_sfl (a : ℝ) : BddDeriv1On (sfl a) univ := by
  refine ⟨sfl_contDiff a, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := (bddDeriv1On_clm (ContinuousLinearMap.id ℝ ℝ) univ).2 k hk
  refine (bdd_of_outside (sfl_contDiff a) (isCompact_Icc (a := a - 1) (b := a + 2)) k
    (C := max C 0) fun y hy => ?_).imp fun C' h y _ => h y
  simp only [mem_Icc, not_and_or, not_le] at hy
  rcases hy with hy | hy
  · have hev : sfl a =ᶠ[𝓝 y] fun _ => a + 1 := by
      filter_upwards [Iio_mem_nhds (show y < a by linarith)] with v hv
      exact sfl_eq_left (le_of_lt hv)
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
    simp
  · have hev : sfl a =ᶠ[𝓝 y] (ContinuousLinearMap.id ℝ ℝ) := by
      filter_upwards [Ioi_mem_nhds (show a + 1 < y by linarith)] with v hv
      exact sfl_eq (le_of_lt hv)
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
    exact (hC y (mem_univ y)).trans (le_max_left _ _)

end QN10

end

end FiniteEnergyPlane

/-!
# Q-N, layer 3: the `+∞` Lipschitz bound `‖cylJ(s, t, w) - jStd‖ ≤ C ‖w‖` (local, NOT published)
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  unfold cylInf ccwLoop
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne') (Complex.exp_ne_zero _)

/-- `cylJ` is `jStd` along `w = 0`. -/
lemma cylJ_zero (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (s t : ℝ) : cylJ Jbar s t 0 = jStd := by
  have hz : (((2 * π : ℝ) : ℂ) * cylInf s t) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (cylInf_ne_zero s t)
  ext x <;> simp [cylJ, cylScale, cylScaleInv, jStd, h0] <;> field_simp [cylInf_ne_zero s t]

/-- `(s, t, w) ↦ cylJ Jbar s t w` is smooth near every point with large `s` and `w ∈ ball 0 ρ`. -/
lemma cylJ_contDiffAt (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → Mat 1)
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    ∃ s₀ : ℝ, ∀ s > s₀, ∀ t : ℝ, ∀ w ∈ ball (0 : ℂ) ρ,
      ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2) (s, t, w) := by
  obtain ⟨-, -, -, hJ, -, ⟨⟨s₀, hD⟩, -⟩, -, -⟩ := hstd
  refine ⟨s₀, fun s hs t w hw => ?_⟩
  set π₂ : ℝ × ℝ × ℂ →L[ℝ] ℝ × ℂ := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)
  have hsplit : (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2) =
      (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)) + Jinf ∘ π₂ := by
    funext q; simp [π₂]
  have hVf : IsOpen (Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    (isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ)))
  have hm1 : ((s, t, w) : ℝ × ℝ × ℂ) ∈ Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ :=
    ⟨hs, mem_univ _, hw⟩
  rw [hsplit]
  exact (hD.contDiffAt (hVf.mem_nhds hm1)).add
    ((hJ.contDiffAt (hU.mem_nhds ⟨mem_univ _, hw⟩)).comp _ π₂.contDiff.contDiffAt)

/-- **`+∞` Lipschitz bound.** `‖cylJ(s, t, w) - jStd‖ ≤ C ‖w‖` on `[s₁, ∞) × ℝ × closedBall 0 (ρ/2)`. -/
theorem cylJ_sub_jStd_le (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ w ∈ closedBall (0 : ℂ) (ρ / 2),
      ‖cylJ Jbar s t w - jStd‖ ≤ C * ‖w‖ := by
  obtain ⟨C, s₁, hC⟩ := cylJ_iteratedFDeriv_bdd ρ b hρ hb Jbar Jinf Sinf hstd 1
  obtain ⟨s₀, hs₀⟩ := cylJ_contDiffAt ρ b Jbar Jinf Sinf hstd
  have h0 := hstd.2.2.1
  refine ⟨C, max s₁ (s₀ + 1), fun s hs t w hw => ?_⟩
  have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs0 : s₀ < s := by have := le_trans (le_max_right _ _) hs; linarith
  set F : ℝ × ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ := fun q => cylJ Jbar q.1 q.2.1 q.2.2 with hF
  set L : ℂ →L[ℝ] ℝ × ℝ × ℂ :=
    (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℂ)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) with hL
  have hL1 : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_one₀ (ContinuousLinearMap.norm_inr_le_one ℝ ℝ (ℝ × ℂ)) (norm_nonneg _)
      (ContinuousLinearMap.norm_inr_le_one ℝ ℝ ℂ)
  have hpath : ∀ v : ℂ, ((s, t, 0) : ℝ × ℝ × ℂ) + L v = (s, t, v) := by
    intro v; simp [hL]
  have hder : ∀ v ∈ closedBall (0 : ℂ) (ρ / 2),
      HasFDerivWithinAt (fun v => cylJ Jbar s t v) ((fderiv ℝ F (s, t, v)).comp L)
        (closedBall (0 : ℂ) (ρ / 2)) v := by
    intro v hv
    have hvρ : v ∈ ball (0 : ℂ) ρ := closedBall_subset_ball (by linarith) hv
    have hFd : HasFDerivAt F (fderiv ℝ F (s, t, v)) ((s, t, 0) + L v) := by
      rw [hpath]
      exact ((hs₀ s hs0 t v hvρ).differentiableAt (by simp)).hasFDerivAt
    have hg : HasFDerivAt (fun v : ℂ => ((s, t, 0) : ℝ × ℝ × ℂ) + L v) L v :=
      L.hasFDerivAt.const_add _
    have := hFd.comp v hg
    refine (this.congr_of_eventuallyEq ?_).hasFDerivWithinAt
    exact Eventually.of_forall fun v' => by simp [hF, hpath]
  have hbound : ∀ v ∈ closedBall (0 : ℂ) (ρ / 2), ‖(fderiv ℝ F (s, t, v)).comp L‖ ≤ C := by
    intro v hv
    have h1 := hC s hs1 t v hv
    rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h1
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ F (s, t, v)‖ * ‖L‖ ≤ ‖fderiv ℝ F (s, t, v)‖ * 1 :=
          mul_le_mul_of_nonneg_left hL1 (ContinuousLinearMap.opNorm_nonneg _)
      _ ≤ C := by simpa using h1
  have key := (convex_closedBall (0 : ℂ) (ρ / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hder hbound (mem_closedBall_self (by linarith)) hw
  rw [cylJ_zero Jbar h0, sub_zero] at key
  exact key

end

end FiniteEnergyPlane

/-!
# Q-S, part 1: matrices of real-linear maps `ℂ → ℂ`, the normal coefficient as such a matrix,
smoothness, periodicity, and the plane form (from `Jbar² = -1`).
-/

namespace FiniteEnergyPlane.QS

open Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- Real and imaginary part, indexed by `Fin 1 ⊕ Fin 1`. -/
def reIm : Fin 1 ⊕ Fin 1 → ℂ → ℝ := Sum.elim (fun _ (y : ℂ) => y.re) (fun _ (y : ℂ) => y.im)

/-- The real basis `1, i` of `ℂ`, indexed by `Fin 1 ⊕ Fin 1`. -/
def basisC : Fin 1 ⊕ Fin 1 → ℂ := Sum.elim (fun _ => (1 : ℂ)) (fun _ => Complex.I)

/-- `reIm i` as a continuous real-linear map. -/
def reImCLM : Fin 1 ⊕ Fin 1 → ℂ →L[ℝ] ℝ := Sum.elim (fun _ => Complex.reCLM) (fun _ => Complex.imCLM)

theorem reImCLM_apply (i : Fin 1 ⊕ Fin 1) (y : ℂ) : reImCLM i y = reIm i y := by
  rcases i with i | i <;> rfl

/-- The real `2 × 2` matrix of a real-linear map `ℂ → ℂ`. -/
def cMat (T : ℂ →L[ℝ] ℂ) : Mat 1 := Matrix.of fun i j => reIm i (T (basisC j))

theorem vecToC_eq (a : Vec 1) :
    vecToC a = (a (Sum.inl 0)) • (1 : ℂ) + (a (Sum.inr 0)) • Complex.I := by
  apply Complex.ext <;> simp [vecToC]

theorem vecToC_cMat (T : ℂ →L[ℝ] ℂ) (a : Vec 1) :
    vecToC (Matrix.toEuclideanLin (cMat T) a) = T (vecToC a) := by
  rw [vecToC_eq a, map_add, map_smul, map_smul]
  apply Complex.ext <;>
  simp [vecToC, cMat, reIm, basisC, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type] <;> ring

theorem vecToC_injective : Function.Injective vecToC := by
  intro a b h
  ext i
  rcases i with i | i <;> obtain rfl : i = 0 := Subsingleton.elim _ _
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

theorem eq_cMat {M : Mat 1} {T : ℂ →L[ℝ] ℂ}
    (h : ∀ a, vecToC (Matrix.toEuclideanLin M a) = T (vecToC a)) : M = cMat T := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro a
  apply vecToC_injective
  rw [h, vecToC_cMat]

theorem cMat_sub (T T' : ℂ →L[ℝ] ℂ) : cMat (T - T') = cMat T - cMat T' := by
  ext i j
  rcases i with i | i <;> simp [cMat, reIm]

theorem cMat_apply (T : ℂ →L[ℝ] ℂ) (i j : Fin 1 ⊕ Fin 1) :
    cMat T i j = reIm i (T (basisC j)) := rfl

/-- The `w`-derivative of `Jbar` along `w = 0`. -/
def dW (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (z : ℂ) : ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  fderiv ℝ (fun w : ℂ => Jbar (z, w)) 0

/-- Evaluate at `v`, then take the second component. -/
def evSnd (v : ℂ × ℂ) : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.apply ℝ (ℂ × ℂ) v)

theorem evSnd_apply (v : ℂ × ℂ) (L : ℂ × ℂ →L[ℝ] ℂ × ℂ) : evSnd v L = (L v).2 := rfl

/-- `a ↦ [(∂_w Jbar(z, 0) a)(2πi z, 0)]₂`. -/
def tN (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (evSnd ((((2 * π : ℝ) : ℂ) * Complex.I * z), 0)).comp (dW Jbar z)

theorem normalCoeff_eq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (x : ℝ × ℝ) :
    normalCoeff Jbar x = cMat (tN Jbar (cylInf x.1 x.2)) := rfl

/-- `a ↦ [(∂_w Jinf(t, 0) a)(i, 0)]₂`. -/
def tInf (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  (evSnd (Complex.I, 0)).comp (fderiv ℝ (fun w : ℂ => Jinf (t, w)) 0)

theorem sinf_eq (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → Mat 1)
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) (t : ℝ) : Sinf t = cMat (tInf Jinf t) :=
  eq_cMat fun a => hstd.2.2.2.2.2.2.2 t a

/-! ### smoothness of partial `w`-derivatives -/

theorem contDiff_fderiv_w {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : X × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : ContDiffOn ℝ ∞ K (Set.univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiff ℝ ∞ (fun x : X => fderiv ℝ (fun w : ℂ => K (x, w)) 0) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (X × ℂ)) := isOpen_univ.prod isOpen_ball
  have hx : ((x, 0) : X × ℂ) ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (X × ℂ)) :=
    ⟨Set.mem_univ _, mem_ball_self hρ⟩
  have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (x : X) (w : ℂ) => K (x, w)) (x, (fun _ => (0 : ℂ)) x) :=
    hK.contDiffAt (hU.mem_nhds hx)
  exact ContDiffAt.fderiv h1 contDiffAt_const (by simp)

theorem hasFDerivAt_w {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : X × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (ρ : ℝ)
    (hK : ContDiffOn ℝ ∞ K (Set.univ ×ˢ ball (0 : ℂ) ρ)) (x : X) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    HasFDerivAt (fun w : ℂ => K (x, w)) (fderiv ℝ (fun w : ℂ => K (x, w)) w) w := by
  have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (X × ℂ)) := isOpen_univ.prod isOpen_ball
  have hd : DifferentiableAt ℝ K (x, w) :=
    (hK.contDiffAt (hU.mem_nhds ⟨Set.mem_univ _, hw⟩)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun w : ℂ => ((x, w) : X × ℂ))
      ((0 : ℂ →L[ℝ] X).prod (ContinuousLinearMap.id ℝ ℂ)) w :=
    (hasFDerivAt_const x w).prodMk (hasFDerivAt_id w)
  exact (hd.hasFDerivAt.comp w hc).differentiableAt.hasFDerivAt

theorem contDiff_cyl : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  unfold cylInf ccwLoop
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((Real.exp (2 * π * q.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((2 * π * q.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)
  exact h1.mul (Complex.contDiff_exp.comp (h2.mul contDiff_const))

theorem cyl_per (s t : ℝ) : cylInf s (t + 1) = cylInf s t := by
  unfold cylInf ccwLoop
  congr 1
  have : (((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I) =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem cyl_ne (s t : ℝ) : cylInf s t ≠ 0 := by
  unfold cylInf ccwLoop
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact_mod_cast (Real.exp_pos _).ne'

/-! ### antilinearity of `∂_w Jbar(z, 0)` in the tangential slot -/

theorem dW_antilinear (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) (z a Δ : ℂ) :
    (dW Jbar z a (Complex.I * Δ, 0)).2 = -(Complex.I * (dW Jbar z a (Δ, 0)).2) := by
  have hd : HasFDerivAt (fun w : ℂ => Jbar (z, w)) (dW Jbar z) 0 :=
    hasFDerivAt_w Jbar ρ hJ z (mem_ball_self hρ)
  have hsqd := hd.clm_comp hd
  have hconst : HasFDerivAt (fun w : ℂ => (Jbar (z, w)).comp (Jbar (z, w)))
      (0 : ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ)) 0 := by
    have hev : (fun w : ℂ => (Jbar (z, w)).comp (Jbar (z, w))) =ᶠ[𝓝 0]
        fun _ => -ContinuousLinearMap.id ℝ (ℂ × ℂ) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with w hw
      exact hsq (z, w) ⟨Set.mem_univ _, hw⟩
    exact (hasFDerivAt_const _ _).congr_of_eventuallyEq hev
  have huniq := hsqd.unique hconst
  have ha := congrArg (fun L => L a (Δ, 0)) huniq
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, h0,
    ContinuousLinearMap.zero_apply] at ha
  have hj : ∀ p : ℂ × ℂ, jStd p = (Complex.I * p.1, Complex.I * p.2) := by
    intro p
    show ((Complex.I • ContinuousLinearMap.id ℝ ℂ) p.1, (Complex.I • ContinuousLinearMap.id ℝ ℂ) p.2) = _
    simp
  have ha2 := congrArg Prod.snd ha
  simp only [hj, Prod.snd_add, Prod.snd_zero, mul_zero] at ha2
  change (dW Jbar z a (Complex.I * Δ, 0)).2 = _
  linear_combination ha2

/-! ### plane form -/

theorem isPlaneCoeff_normalCoeff (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) : IsPlaneCoeff (normalCoeff Jbar) := by
  let c : ℂ := -(Complex.I / 2)
  let A : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    ((c • ContinuousLinearMap.id ℝ ℂ).comp (evSnd ((1 : ℂ), (0 : ℂ)))).comp (dW Jbar z)
  refine ⟨A, ?_, ?_⟩
  · exact contDiff_const.clm_comp (contDiff_fderiv_w Jbar ρ hρ hJ)
  · intro s t a
    rw [normalCoeff_eq, vecToC_cMat]
    set z := cylInf s t
    set α := vecToC a
    set X := (dW Jbar z α ((1 : ℂ), (0 : ℂ))).2 with hX
    have hanti := dW_antilinear ρ hρ Jbar hJ hsq h0 z α 1
    rw [mul_one] at hanti
    set μ : ℂ := ((2 * π : ℝ) : ℂ) * Complex.I * z
    have hsplit : ((μ, 0) : ℂ × ℂ) = μ.re • ((1 : ℂ), (0 : ℂ)) + μ.im • (Complex.I, (0 : ℂ)) := by
      refine Prod.ext ?_ ?_
      · apply Complex.ext <;> simp
      · simp
    have hlhs : tN Jbar z α = μ.re * X + μ.im * (-(Complex.I * X)) := by
      show (dW Jbar z α (μ, 0)).2 = _
      rw [hsplit, map_add, map_smul, map_smul, Prod.snd_add, Prod.smul_snd, Prod.smul_snd, hanti,
        Complex.real_smul, Complex.real_smul]
    have hrhs : A z α = c * X := rfl
    rw [hlhs, hrhs]
    simp only [μ, c]
    apply Complex.ext <;> simp <;> ring

/-! ### smoothness and periodicity of the entries -/

theorem contDiff_normalCoeff (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) (i j : Fin 1 ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => normalCoeff Jbar x i j) := by
  have hd := (contDiff_fderiv_w Jbar ρ hρ hJ).comp contDiff_cyl
  have hv : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      ((((2 * π : ℝ) : ℂ) * Complex.I * cylInf x.1 x.2), (0 : ℂ))) :=
    (contDiff_const.mul contDiff_cyl).prodMk contDiff_const
  have : (fun x : ℝ × ℝ => normalCoeff Jbar x i j) =
      fun x => reImCLM i ((dW Jbar (cylInf x.1 x.2) (basisC j)
        ((((2 * π : ℝ) : ℂ) * Complex.I * cylInf x.1 x.2), (0 : ℂ))).2) := by
    funext x; rw [normalCoeff_eq, cMat_apply, reImCLM_apply]; rfl
  rw [this]
  exact (reImCLM i).contDiff.comp (contDiff_snd.comp ((hd.clm_apply contDiff_const).clm_apply hv))

theorem contDiff_sinf (ρ b : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → Mat 1)
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) (i j : Fin 1 ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun t => Sinf t i j) := by
  have : (fun t => Sinf t i j) = fun t => reImCLM i ((tInf Jinf t) (basisC j)) := by
    funext t; rw [sinf_eq ρ b Jbar Jinf Sinf hstd t, cMat_apply, reImCLM_apply]
  rw [this]
  have hT : ContDiff ℝ ∞ (fun t => tInf Jinf t) :=
    contDiff_const.clm_comp (contDiff_fderiv_w Jinf ρ hρ hstd.2.2.2.1)
  exact (reImCLM i).contDiff.comp (hT.clm_apply contDiff_const)

theorem normalCoeff_per (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (s t : ℝ) :
    normalCoeff Jbar (s, t + 1) = normalCoeff Jbar (s, t) := by
  rw [normalCoeff_eq, normalCoeff_eq]
  simp only [cyl_per]

end

end FiniteEnergyPlane.QS

/-!
# Q-N, layer 11 (local, NOT published): `K̃` and its Hadamard quotient have bounded derivatives

* `cylJ_bdd_right`: for `a > s₀`, every derivative of `(s, t, w) ↦ cylJ Jbar s t w` is bounded on
  `[a, ∞) × ℝ × closedBall 0 (ρ/2)` (N1 at large `s`, compactness + `t`-periodicity in between).
* `Kt a`: `K̃(p) = cylJ(sfl a s, t, rtr (ρ/2) w) − jStd` on `(ℝ × ℝ) × ℂ`; `bddDerivOn_Kt`.
* `Ht a`: its Hadamard quotient in `w`; `bddDerivOn_Ht`, `Kt_eq_Ht`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN11

open QN9 QN10

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

/-- `cylJ` as a function on `ℝ × ℝ × ℂ`. -/
def gJ (q : ℝ × ℝ × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ := cylJ Jbar q.1 q.2.1 q.2.2

lemma gJ_per (q : ℝ × ℝ × ℂ) : gJ Jbar (q + ((0 : ℝ), (1 : ℝ), (0 : ℂ))) = gJ Jbar q := by
  obtain ⟨s, t, w⟩ := q
  simp only [gJ, Prod.mk_add_mk, add_zero, cylJ, cylScale, cylScaleInv, QS.cyl_per]

/-- Bounded derivatives of `cylJ` on `[a, ∞) × ℝ × closedBall 0 (ρ/2)`. -/
theorem cylJ_bdd_right (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    ∃ s₀ : ℝ, ContDiffOn ℝ ∞ (gJ Jbar) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) ∧
      ∀ a > s₀, ∀ m : ℕ, ∃ C, ∀ q ∈ Ici a ×ˢ univ ×ˢ closedBall (0 : ℂ) (ρ / 2),
        ‖iteratedFDeriv ℝ m (gJ Jbar) q‖ ≤ C := by
  obtain ⟨s₀, hs₀⟩ := cylJ_contDiffAt ρ b Jbar Jinf Sinf hstd
  have hO : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hC : ContDiffOn ℝ ∞ (gJ Jbar) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) := fun q hq =>
    (hs₀ q.1 hq.1 q.2.1 q.2.2 hq.2.2).contDiffWithinAt
  refine ⟨s₀, hC, fun a ha m => ?_⟩
  obtain ⟨C₁, s₁, hC₁⟩ := cylJ_iteratedFDeriv_bdd ρ b hρ hb Jbar Jinf Sinf hstd m
  have hcont : ContinuousOn (iteratedFDeriv ℝ m (gJ Jbar)) (Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
    (hC.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top)
      hO.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen m hO hx).symm)
  have hsub : Icc a (max a s₁) ×ˢ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) (ρ / 2) ⊆
      Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ := fun q hq =>
    ⟨lt_of_lt_of_le ha hq.1.1, mem_univ _, closedBall_subset_ball (by linarith) hq.2.2⟩
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) (ρ / 2))))
    |>.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max C₁ C₂, fun q hq => ?_⟩
  obtain ⟨s, t, w⟩ := q
  obtain ⟨hs, -, hw⟩ := hq
  rcases le_or_gt s₁ s with h1 | h1
  · exact (hC₁ s h1 t w hw).trans (le_max_left _ _)
  · have hP : Function.Periodic (fun t : ℝ => ‖iteratedFDeriv ℝ m (gJ Jbar) (s, t, w)‖) 1 := by
      intro t
      have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := gJ Jbar) m ((0 : ℝ), (1 : ℝ), (0 : ℂ))
        (s, t, w)
      have hfun : (fun z => gJ Jbar (z + ((0 : ℝ), (1 : ℝ), (0 : ℂ)))) = gJ Jbar :=
        funext fun z => gJ_per Jbar z
      rw [hfun] at this
      simp only [Prod.mk_add_mk, add_zero] at this
      exact congrArg norm this.symm
    obtain ⟨y, hy, hy'⟩ := hP.exists_mem_Ico₀ one_pos t
    rw [hy']
    exact (hC₂ (s, y, w) ⟨⟨hs, le_max_of_le_right h1.le⟩, Ico_subset_Icc_self hy, hw⟩).trans
      (le_max_right _ _)

end QN11

end

end FiniteEnergyPlane

/-!
# Q-N, layer 12 (local, NOT published): `K̃` and its Hadamard quotient `Ĥ`

* `Kt a`: `K̃(p) = cylJ(sfl a s, t, rtr (ρ/2) w) − jStd` on `(ℝ × ℝ) × ℂ`; `bddDerivOn_Kt`.
* `Ht a`: its Hadamard quotient in `w`; `Kt_eq_Ht` (`K̃ = Ĥ(·)(w)`), `bddDerivOn_Ht`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN11

open QN9 QN10

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

/-! ### `K̃` -/

/-- `K̃(s, t, w) = cylJ(sfl a s, t, rtr (ρ/2) w) − jStd`. -/
def Kt (a : ℝ) (p : (ℝ × ℝ) × ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  gJ Jbar (sfl a p.1.1, p.1.2, rtr (ρ / 2) p.2) - jStd

/-- The inner map of `K̃`. -/
def innerK (a : ℝ) (p : (ℝ × ℝ) × ℂ) : ℝ × ℝ × ℂ := (sfl a p.1.1, p.1.2, rtr (ρ / 2) p.2)

lemma bddDeriv1On_innerK (hρ : 0 < ρ) (a : ℝ) : BddDeriv1On (innerK ρ a) univ := by
  set P1 : (ℝ × ℝ) × ℂ →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℂ)
  set L1 : ℝ →L[ℝ] ℝ × ℝ × ℂ := ContinuousLinearMap.inl ℝ ℝ (ℝ × ℂ)
  set L2 : (ℝ × ℝ) × ℂ →L[ℝ] ℝ × ℝ × ℂ := (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℂ)).comp
    ((ContinuousLinearMap.inl ℝ ℝ ℂ).comp ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℂ)))
  set P3 : (ℝ × ℝ) × ℂ →L[ℝ] ℂ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℂ
  set L3 : ℂ →L[ℝ] ℝ × ℝ × ℂ := (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℂ)).comp
    (ContinuousLinearMap.inr ℝ ℝ ℂ)
  have e : innerK ρ a = fun p => (L1 ∘ (sfl a ∘ P1)) p + L2 p + (L3 ∘ (rtr (ρ / 2) ∘ P3)) p := by
    funext p; ext <;> simp [innerK, P1, L1, L2, P3, L3]
  rw [e]
  refine BddDeriv1On.add (BddDeriv1On.add
    (QN10.BddDeriv1On.clm_comp (QN10.BddDeriv1On.comp_clm (bddDeriv1On_sfl a) P1) L1)
    (bddDeriv1On_clm L2 univ)) ?_
  exact BddDerivOn.one
    (QN10.BddDerivOn.clm_comp (QN10.BddDerivOn.comp_clm (bddDerivOn_rtr (half_pos hρ)) P3) L3)

theorem bddDerivOn_Kt (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    ∃ s₀ : ℝ, ∀ a > s₀, BddDerivOn (Kt ρ Jbar a) univ := by
  obtain ⟨s₀, hC, hB⟩ := cylJ_bdd_right ρ b Jbar Jinf Sinf hρ hb hstd
  refine ⟨s₀, fun a ha => ?_⟩
  have hO : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_Ioi.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hV : Ici a ×ˢ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) (ρ / 2) ⊆
      Ioi s₀ ×ˢ univ ×ˢ ball (0 : ℂ) ρ := fun q hq =>
    ⟨lt_of_lt_of_le ha hq.1, mem_univ _, closedBall_subset_ball (by linarith) hq.2.2⟩
  have hmaps : ∀ p, innerK ρ a p ∈ Ici a ×ˢ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) (ρ / 2) :=
    fun p => ⟨le_sfl a _, mem_univ _,
      mem_closedBall_zero_iff.2 (norm_rtr_lt (half_pos hρ) _).le⟩
  have h1 := comp_contDiffOn hO hC (hB a ha) hV (bddDeriv1On_innerK ρ hρ a) hmaps
  have e : Kt ρ Jbar a = fun p => (gJ Jbar ∘ innerK ρ a) p + (fun _ => -jStd) p := by
    funext p; simp [Kt, innerK, sub_eq_add_neg]
  rw [e]
  exact h1.add (bddDerivOn_const _ _)

lemma Kt_zero (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) (a : ℝ) (x : ℝ × ℝ) : Kt ρ Jbar a (x, 0) = 0 := by
  have hr : rtr (ρ / 2) 0 = 0 := by simp [rtr]
  simp only [Kt, gJ, hr]
  rw [cylJ_zero Jbar h0]
  simp

/-! ### The Hadamard quotient `Ĥ`

Written with the full derivative of `K̃` (a 2-level CLM type); the restriction to the `w`-slot is
`(0, ·)`. (Three-level nested CLM types such as `(P →L G) →L (ℂ →L G)` do not get a `Norm`
instance in this Mathlib.) -/

/-- `Ĥ(x, w) = ∫₀¹ DK̃(x, θ w) dθ`. -/
def Ht (a : ℝ) (p : (ℝ × ℝ) × ℂ) : ((ℝ × ℝ) × ℂ) →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (Kt ρ Jbar a) (p.1, θ • p.2)

/-- The splitting `p ↦ ((x, 0), (0, w))`. -/
def splitL : (ℝ × ℝ) × ℂ →L[ℝ] ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) :=
  ((ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℂ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℂ)).prod
    ((ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℂ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℂ))

lemma Ht_eq_split (a : ℝ) (hK : ContDiff ℝ ∞ (Kt ρ Jbar a)) (p : (ℝ × ℝ) × ℂ) :
    Ht ρ Jbar a p = (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
      ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun c => Kt ρ Jbar a (y.1 + c)) (θ • y.2)) (splitL p) := by
  simp only [Ht, splitL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [fderiv_comp_add_left]
  congr 1
  ext <;> simp

lemma contDiff_Ht (a : ℝ) (hK : ContDiff ℝ ∞ (Kt ρ Jbar a)) : ContDiff ℝ ∞ (Ht ρ Jbar a) := by
  have h := (hadamard_integral_fderiv (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
    Kt ρ Jbar a (y.1 + y.2)) (hK.comp (contDiff_fst.add contDiff_snd))).1
  have e : Ht ρ Jbar a = (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
      ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun c => Kt ρ Jbar a (y.1 + c)) (θ • y.2)) ∘ splitL :=
    funext fun p => Ht_eq_split ρ Jbar a hK p
  rw [e]
  exact h.comp splitL.contDiff

lemma Kt_eq_Ht (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) (a : ℝ) (hK : ContDiff ℝ ∞ (Kt ρ Jbar a))
    (p : (ℝ × ℝ) × ℂ) : Kt ρ Jbar a p = Ht ρ Jbar a p (0, p.2) := by
  have h := (hadamard_integral_fderiv (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
    Kt ρ Jbar a (y.1 + y.2)) (hK.comp (contDiff_fst.add contDiff_snd))).2 (splitL p)
  have e1 : (splitL p).1 + (splitL p).2 = p := by
    obtain ⟨x, w⟩ := p; simp [splitL]
  have e2 : (splitL p).1 + 0 = (p.1, 0) := by
    obtain ⟨x, w⟩ := p; simp [splitL]
  have e3 : (splitL p).2 = (0, p.2) := by
    obtain ⟨x, w⟩ := p; simp [splitL]
  calc Kt ρ Jbar a p = Kt ρ Jbar a ((splitL p).1 + (splitL p).2) := by rw [e1]
    _ = Kt ρ Jbar a ((splitL p).1 + 0) + (∫ θ in (0 : ℝ)..1,
          fderiv ℝ (fun c => Kt ρ Jbar a ((splitL p).1 + c)) (θ • (splitL p).2)) (splitL p).2 := h
    _ = Ht ρ Jbar a p (0, p.2) := by
        rw [e2, Kt_zero ρ Jbar h0, zero_add, Ht_eq_split ρ Jbar a hK p, ← e3]

theorem bddDerivOn_Ht (a : ℝ) (hK : BddDerivOn (Kt ρ Jbar a) univ) :
    BddDerivOn (Ht ρ Jbar a) univ := by
  set M : ℝ → (ℝ × ℝ) × ℂ →L[ℝ] (ℝ × ℝ) × ℂ := fun θ =>
    ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (θ • ContinuousLinearMap.id ℝ ℂ)
  have hMe : ∀ θ : ℝ, ∀ p : (ℝ × ℝ) × ℂ, M θ p = (p.1, θ • p.2) := fun θ p => rfl
  have hfK : ContDiff ℝ ∞ (fderiv ℝ (Kt ρ Jbar a)) := hK.1.fderiv_right (m := ∞) le_rfl
  have hF : ContDiff ℝ ∞ (Function.uncurry (fun (p : (ℝ × ℝ) × ℂ) (θ : ℝ) =>
      fderiv ℝ (Kt ρ Jbar a) (p.1, θ • p.2))) :=
    hfK.comp (contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd))
  have hM : ∀ θ ∈ Icc (0 : ℝ) 1, ‖M θ‖ ≤ 1 := by
    intro θ hθ
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
    rw [hMe, one_mul]
    refine norm_prod_le_iff.2 ⟨norm_fst_le p, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hθ.2).trans (norm_snd_le p)
  refine ⟨contDiff_Ht ρ Jbar a hK.1, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hK.2 (k + 1)
  refine ⟨C, fun p _ => ?_⟩
  refine norm_iteratedFDeriv_intervalIntegral_le hF k p _ fun θ hθ => ?_
  have hfun : (fun p : (ℝ × ℝ) × ℂ => fderiv ℝ (Kt ρ Jbar a) (p.1, θ • p.2)) =
      fderiv ℝ (Kt ρ Jbar a) ∘ M θ := funext fun p => by rw [Function.comp_apply, hMe]
  rw [hfun, (M θ).iteratedFDeriv_comp_right hfK p (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_iteratedFDeriv_fderiv]
  have h1 := hC (M θ p) (mem_univ _)
  have h2 : ‖M θ‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hM θ hθ)
  calc ‖iteratedFDeriv ℝ (k + 1) (Kt ρ Jbar a) (M θ p)‖ * ‖M θ‖ ^ k ≤ C * 1 :=
        mul_le_mul h1 h2 (by positivity) ((norm_nonneg _).trans h1)
    _ = C := mul_one C

end QN11

end

end FiniteEnergyPlane

/-!
# Q-N, layer 13 (local, NOT published): vector Hadamard quotients, global smoothness of `cylJ`

* `hq k`: for `k : (ℝ × ℝ) × ℂ → W`, `hq k p = ∫₀¹ Dk(x, θ w) dθ`; `eq_hq` (`k p = hq k p (0, w)` when
  `k (x, 0) = 0`), `bddDerivOn_hq`. Values of `hq k` have CLM depth 1 when `W` is a plain space.
* `gJ_contDiffOn`: `cylJ` is `C^∞` on `ℝ × ℝ × ball 0 ρ` (no `s₀`); `cylJ_bdd_right'`, `bddDerivOn_Kt'`
  for every `a`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN13

open QN9 QN10 QN11

section Hadamard

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  (k : (ℝ × ℝ) × ℂ → W)

/-- `hq k (x, w) = ∫₀¹ Dk(x, θ w) dθ`. -/
def hq (p : (ℝ × ℝ) × ℂ) : ((ℝ × ℝ) × ℂ) →L[ℝ] W :=
  ∫ θ in (0 : ℝ)..1, fderiv ℝ (k) (p.1, θ • p.2)

lemma hq_eq_split (hK : ContDiff ℝ ∞ (k)) (p : (ℝ × ℝ) × ℂ) :
    hq k p = (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
      ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun c => k (y.1 + c)) (θ • y.2)) (splitL p) := by
  simp only [hq, splitL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [fderiv_comp_add_left]
  congr 1
  ext <;> simp

lemma contDiff_hq (hK : ContDiff ℝ ∞ (k)) : ContDiff ℝ ∞ (hq k) := by
  have h := (hadamard_integral_fderiv (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
    k (y.1 + y.2)) (hK.comp (contDiff_fst.add contDiff_snd))).1
  have e : hq k = (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
      ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun c => k (y.1 + c)) (θ • y.2)) ∘ splitL :=
    funext fun p => hq_eq_split k hK p
  rw [e]
  exact h.comp splitL.contDiff

lemma eq_hq (h0 : ∀ x, k (x, 0) = 0) (hK : ContDiff ℝ ∞ (k))
    (p : (ℝ × ℝ) × ℂ) : k p = hq k p (0, p.2) := by
  have h := (hadamard_integral_fderiv (fun y : ((ℝ × ℝ) × ℂ) × ((ℝ × ℝ) × ℂ) =>
    k (y.1 + y.2)) (hK.comp (contDiff_fst.add contDiff_snd))).2 (splitL p)
  have e1 : (splitL p).1 + (splitL p).2 = p := by
    obtain ⟨x, w⟩ := p; simp [splitL]
  have e2 : (splitL p).1 + 0 = (p.1, 0) := by
    obtain ⟨x, w⟩ := p; simp [splitL]
  have e3 : (splitL p).2 = (0, p.2) := by
    obtain ⟨x, w⟩ := p; simp [splitL]
  calc k p = k ((splitL p).1 + (splitL p).2) := by rw [e1]
    _ = k ((splitL p).1 + 0) + (∫ θ in (0 : ℝ)..1,
          fderiv ℝ (fun c => k ((splitL p).1 + c)) (θ • (splitL p).2)) (splitL p).2 := h
    _ = hq k p (0, p.2) := by
        rw [e2, h0, zero_add, hq_eq_split k hK p, ← e3]

theorem bddDerivOn_hq (hK : BddDerivOn (k) univ) :
    BddDerivOn (hq k) univ := by
  set M : ℝ → (ℝ × ℝ) × ℂ →L[ℝ] (ℝ × ℝ) × ℂ := fun θ =>
    ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (θ • ContinuousLinearMap.id ℝ ℂ)
  have hMe : ∀ θ : ℝ, ∀ p : (ℝ × ℝ) × ℂ, M θ p = (p.1, θ • p.2) := fun θ p => rfl
  have hfK : ContDiff ℝ ∞ (fderiv ℝ (k)) := hK.1.fderiv_right (m := ∞) le_rfl
  have hF : ContDiff ℝ ∞ (Function.uncurry (fun (p : (ℝ × ℝ) × ℂ) (θ : ℝ) =>
      fderiv ℝ (k) (p.1, θ • p.2))) :=
    hfK.comp (contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd))
  have hM : ∀ θ ∈ Icc (0 : ℝ) 1, ‖M θ‖ ≤ 1 := by
    intro θ hθ
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
    rw [hMe, one_mul]
    refine norm_prod_le_iff.2 ⟨norm_fst_le p, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hθ.2).trans (norm_snd_le p)
  refine ⟨contDiff_hq k hK.1, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hK.2 (n + 1)
  refine ⟨C, fun p _ => ?_⟩
  refine norm_iteratedFDeriv_intervalIntegral_le hF n p _ fun θ hθ => ?_
  have hfun : (fun p : (ℝ × ℝ) × ℂ => fderiv ℝ (k) (p.1, θ • p.2)) =
      fderiv ℝ (k) ∘ M θ := funext fun p => by rw [Function.comp_apply, hMe]
  rw [hfun, (M θ).iteratedFDeriv_comp_right hfK p (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_iteratedFDeriv_fderiv]
  have h1 := hC (M θ p) (mem_univ _)
  have h2 : ‖M θ‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (hM θ hθ)
  calc ‖iteratedFDeriv ℝ (n + 1) (k) (M θ p)‖ * ‖M θ‖ ^ n ≤ C * 1 :=
        mul_le_mul h1 h2 (by positivity) ((norm_nonneg _).trans h1)
    _ = C := mul_one C

end Hadamard

/-! ### `cylJ` is smooth for every `s` -/

section Cyl

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

lemma contDiff_cylInf : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) := by
  unfold cylInf ccwLoop
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => ((Real.exp (2 * π * q.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => Complex.exp (((2 * π * q.2.1 : ℝ) : ℂ) * Complex.I)) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (contDiff_fst.comp contDiff_snd))).mul contDiff_const)
  exact h1.mul h2

lemma gJ_apply (q : ℝ × ℝ × ℂ) (y : ℂ × ℂ) :
    gJ Jbar q y = ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1)⁻¹ *
        (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).1,
      (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).2) := by
  simp only [gJ, cylJ, cylScale, cylScaleInv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]

/-- `cylJ` is `C^∞` on `ℝ × ℝ × ball 0 ρ`. -/
theorem gJ_contDiffOn (hJ : ContDiffOn ℝ ∞ Jbar (univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (gJ Jbar) (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) := by
  refine contDiffOn_clm_apply.2 fun y => ?_
  have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) :=
    contDiff_const.mul contDiff_cylInf
  have hc0 : ∀ q : ℝ × ℝ × ℂ, ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1 ≠ 0 := fun q =>
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (cylInf_ne_zero _ _)
  have hJq : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ => Jbar (cylInf q.1 q.2.1, q.2.2))
      (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
    hJ.comp (contDiff_cylInf.prodMk (contDiff_snd.comp contDiff_snd)).contDiffOn
      fun q hq => ⟨mem_univ _, hq.2.2⟩
  have hv : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ =>
      Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2))
      (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
    hJq.clm_apply ((hc.mul contDiff_const).prodMk contDiff_const).contDiffOn
  have e : (fun q => gJ Jbar q y) = fun q : ℝ × ℝ × ℂ =>
      ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1)⁻¹ *
        (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).1,
      (Jbar (cylInf q.1 q.2.1, q.2.2) ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) * y.1, y.2)).2) :=
    funext fun q => gJ_apply Jbar q y
  rw [e]
  exact ((hc.inv hc0).contDiffOn.mul (contDiff_fst.comp_contDiffOn hv)).prodMk
    (contDiff_snd.comp_contDiffOn hv)

/-- Bounded derivatives of `cylJ` on `[a, ∞) × ℝ × closedBall 0 (ρ/2)`, for every `a`. -/
theorem cylJ_bdd_right' (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (a : ℝ) (m : ℕ) : ∃ C, ∀ q ∈ Ici a ×ˢ univ ×ˢ closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDeriv ℝ m (gJ Jbar) q‖ ≤ C := by
  have hO : IsOpen ((univ : Set ℝ) ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_univ.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hC : ContDiffOn ℝ ∞ (gJ Jbar) (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
    gJ_contDiffOn ρ Jbar hstd.1
  obtain ⟨C₁, s₁, hC₁⟩ := cylJ_iteratedFDeriv_bdd ρ b hρ hb Jbar Jinf Sinf hstd m
  have hcont : ContinuousOn (iteratedFDeriv ℝ m (gJ Jbar)) (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ) :=
    (hC.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top)
      hO.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen m hO hx).symm)
  have hsub : Icc a (max a s₁) ×ˢ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) (ρ / 2) ⊆
      univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ := fun q hq =>
    ⟨mem_univ _, mem_univ _, closedBall_subset_ball (by linarith) hq.2.2⟩
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) (ρ / 2))))
    |>.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max C₁ C₂, fun q hq => ?_⟩
  obtain ⟨s, t, w⟩ := q
  obtain ⟨hs, -, hw⟩ := hq
  rcases le_or_gt s₁ s with h1 | h1
  · exact (hC₁ s h1 t w hw).trans (le_max_left _ _)
  · have hP : Function.Periodic (fun t : ℝ => ‖iteratedFDeriv ℝ m (gJ Jbar) (s, t, w)‖) 1 := by
      intro t
      have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := gJ Jbar) m ((0 : ℝ), (1 : ℝ), (0 : ℂ))
        (s, t, w)
      have hfun : (fun z => gJ Jbar (z + ((0 : ℝ), (1 : ℝ), (0 : ℂ)))) = gJ Jbar :=
        funext fun z => gJ_per Jbar z
      rw [hfun] at this
      simp only [Prod.mk_add_mk, add_zero] at this
      exact congrArg norm this.symm
    obtain ⟨y, hy, hy'⟩ := hP.exists_mem_Ico₀ one_pos t
    rw [hy']
    exact (hC₂ (s, y, w) ⟨⟨hs, le_max_of_le_right h1.le⟩, Ico_subset_Icc_self hy, hw⟩).trans
      (le_max_right _ _)

/-- `K̃` has bounded derivatives, for every `a`. -/
theorem bddDerivOn_Kt' (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (a : ℝ) : BddDerivOn (Kt ρ Jbar a) univ := by
  have hO : IsOpen ((univ : Set ℝ) ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ) :=
    isOpen_univ.prod ((isOpen_univ (X := ℝ)).prod (isOpen_ball (x := (0 : ℂ))))
  have hV : Ici a ×ˢ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) (ρ / 2) ⊆
      univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ := fun q hq =>
    ⟨mem_univ _, mem_univ _, closedBall_subset_ball (by linarith) hq.2.2⟩
  have hmaps : ∀ p, innerK ρ a p ∈ Ici a ×ˢ (univ : Set ℝ) ×ˢ closedBall (0 : ℂ) (ρ / 2) :=
    fun p => ⟨le_sfl a _, mem_univ _,
      mem_closedBall_zero_iff.2 (norm_rtr_lt (half_pos hρ) _).le⟩
  have h1 := comp_contDiffOn hO (gJ_contDiffOn ρ Jbar hstd.1)
    (cylJ_bdd_right' ρ b Jbar Jinf Sinf hρ hb hstd a) hV (bddDeriv1On_innerK ρ hρ a) hmaps
  have e : Kt ρ Jbar a = fun p => (gJ Jbar ∘ innerK ρ a) p + (fun _ => -jStd) p := by
    funext p; simp [Kt, innerK, sub_eq_add_neg]
  rw [e]
  exact h1.add (bddDerivOn_const _ _)

end Cyl

end QN13

end

end FiniteEnergyPlane

/-!
# Q-N, layer 5 (local, NOT published): log coordinates of `ψ` at `+∞`

`ψ = z (1 + ζ)` with `z = cylInf s t` and `‖ζ‖ < 1` is again a cylinder point:
`ψ = cylInf (s + (logChart ζ).re) (t + (logChart ζ).im)`, with `logChart ζ = log(1 + ζ)/(2π)`
smooth on `ball 0 1`, and all its derivatives bounded on `closedBall 0 (1/2)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Real

noncomputable section

/-- `log(1 + ζ) / (2π)`. -/
def logChart (ζ : ℂ) : ℂ := Complex.log (1 + ζ) * (((2 * π : ℝ) : ℂ))⁻¹

lemma one_add_mem_slitPlane {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 + ζ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm ζ
  rw [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le ζ.re]

lemma logChart_contDiffAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ContDiffAt ℝ ∞ logChart ζ := by
  have hlog : ContDiffAt ℝ ∞ Complex.log (1 + ζ) :=
    (Complex.contDiffAt_log (one_add_mem_slitPlane hζ)).restrict_scalars ℝ
  exact (hlog.comp ζ (contDiffAt_const.add contDiffAt_id)).mul contDiffAt_const

lemma logChart_contDiffOn : ContDiffOn ℝ ∞ logChart (ball (0 : ℂ) 1) := fun ζ hζ =>
  (logChart_contDiffAt (mem_ball_zero_iff.1 hζ)).contDiffWithinAt

lemma logChart_iteratedFDeriv_bdd (m : ℕ) :
    ∃ C : ℝ, ∀ ζ ∈ closedBall (0 : ℂ) (1 / 2), ‖iteratedFDeriv ℝ m logChart ζ‖ ≤ C := by
  have hc : ContinuousOn (fun ζ => iteratedFDeriv ℝ m logChart ζ) (ball (0 : ℂ) 1) := by
    refine (logChart_contDiffOn.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast le_top) (isOpen_ball.uniqueDiffOn)).congr fun ζ hζ => ?_
    exact (iteratedFDerivWithin_of_isOpen m isOpen_ball hζ).symm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (hc.mono (closedBall_subset_ball (by norm_num)))
  exact ⟨C, hC⟩

/-- `cylInf s t (1 + ζ)` in log coordinates. -/
lemma cylInf_mul_one_add (s t : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cylInf s t * (1 + ζ) = cylInf (s + (logChart ζ).re) (t + (logChart ζ).im) := by
  have hne : 1 + ζ ≠ 0 := Complex.slitPlane_ne_zero (one_add_mem_slitPlane hζ)
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hre : 2 * π * (logChart ζ).re = (Complex.log (1 + ζ)).re := by
    simp only [logChart, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
  have him : 2 * π * (logChart ζ).im = (Complex.log (1 + ζ)).im := by
    simp only [logChart, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    field_simp
  unfold cylInf ccwLoop
  rw [← Complex.exp_log hne]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul]
    push_cast
    linarith [hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul, zero_add]
    push_cast
    linarith [him]

end

end FiniteEnergyPlane

/-!
# Q-N, layer 14 (local, NOT published): the `+∞` integrands

* `bddDerivOn_of_isCompact`, **`bddDerivOn_frame`**: `z ↦ Φ₀(τ z, F(σ z + ℓ(τ z), m(τ z)))` has
  bounded derivatives on `τ⁻¹' C` (`C` compact, `F` with bounded derivatives on `univ`).
* `kbar`, `Fh`: the four columns of `K̃` and their Hadamard quotients (vector valued);
  `Kt_apply_eq`: `K̃(y) h = w.re • lin h F₁ + w.im • lin h F_I` with `w = y.2`.
* `phiRZ`, `phiRP`: the jointly smooth `+∞` integrands of the zero-order and the product term.

All CLM types have depth `≤ 2` (`Norm` is not synthesized at depth 3 in this Mathlib).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN14

open QN9 QN10 QN11 QN13

/-! ### Generic bounded-derivative frame -/

lemma bddDerivOn_of_isCompact {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : Y → Z} (hf : ContDiff ℝ ∞ f) {K : Set Y}
    (hK : IsCompact K) : BddDerivOn f K :=
  ⟨hf, fun k => hK.exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).continuousOn⟩

/-- **Frame lemma.** -/
theorem bddDerivOn_frame {Z X Cs Vn Out : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Cs] [NormedSpace ℝ Cs]
    [NormedAddCommGroup Vn] [NormedSpace ℝ Vn] [FiniteDimensional ℝ Vn]
    [NormedAddCommGroup Out] [NormedSpace ℝ Out]
    (σ : Z →L[ℝ] X) (τ : Z →L[ℝ] Cs) (F : X × ℂ → Vn) (hF : BddDerivOn F univ)
    (ℓ : Cs → X) (hℓ : ContDiff ℝ ∞ ℓ) (m : Cs → ℂ) (hm : ContDiff ℝ ∞ m)
    (Φ₀ : Cs × Vn → Out) (hΦ : ContDiff ℝ ∞ Φ₀) (C : Set Cs) (hC : IsCompact C) :
    BddDerivOn (fun z => Φ₀ (τ z, F (σ z + ℓ (τ z), m (τ z)))) (τ ⁻¹' C) := by
  obtain ⟨M, hM⟩ := hF.2 0
  have hM' : ∀ y, ‖F y‖ ≤ M := fun y => by simpa using hM y (mem_univ y)
  have hlm : BddDerivOn (fun c => (ℓ c, m c)) C := bddDerivOn_of_isCompact (hℓ.prodMk hm) hC
  have hτ : BddDeriv1On τ (τ ⁻¹' C) := bddDeriv1On_clm τ _
  have hj : BddDeriv1On (fun z => (ContinuousLinearMap.inl ℝ X ℂ).comp σ z + (fun c => (ℓ c, m c)) (τ z))
      (τ ⁻¹' C) :=
    BddDeriv1On.add (bddDeriv1On_clm _ _) (BddDerivOn.comp hlm hτ fun z hz => hz).one
  have hFj := BddDerivOn.comp hF hj (fun _ _ => mem_univ _)
  have hι : BddDeriv1On (fun z => (ContinuousLinearMap.inl ℝ Cs Vn).comp τ z +
      (ContinuousLinearMap.inr ℝ Cs Vn ∘ (F ∘ fun z => (ContinuousLinearMap.inl ℝ X ℂ).comp σ z +
        (fun c => (ℓ c, m c)) (τ z))) z) (τ ⁻¹' C) :=
    BddDeriv1On.add (bddDeriv1On_clm _ _) (QN10.BddDerivOn.clm_comp hFj _).one
  have hK : IsCompact (C ×ˢ closedBall (0 : Vn) M) := hC.prod (isCompact_closedBall _ _)
  have h := BddDerivOn.comp (bddDerivOn_of_isCompact hΦ hK) hι (fun z hz => by
    refine ⟨?_, ?_⟩
    · simpa using hz
    · simp [hM'])
  have e : (fun z => Φ₀ (τ z, F (σ z + ℓ (τ z), m (τ z)))) = Φ₀ ∘ (fun z =>
      (ContinuousLinearMap.inl ℝ Cs Vn).comp τ z +
      (ContinuousLinearMap.inr ℝ Cs Vn ∘ (F ∘ fun z => (ContinuousLinearMap.inl ℝ X ℂ).comp σ z +
        (fun c => (ℓ c, m c)) (τ z))) z) := by
    funext z; simp
  rw [e]; exact h

/-! ### Columns of `K̃` and their Hadamard quotients -/

abbrev V := ℂ × ℂ
abbrev W4 := V × V × V × V

/-- Evaluation at the real basis `(1,0), (i,0), (0,1), (0,i)`. -/
def ev4 : (V →L[ℝ] V) →L[ℝ] W4 :=
  (ContinuousLinearMap.apply ℝ V ((1 : ℂ), (0 : ℂ))).prod
    ((ContinuousLinearMap.apply ℝ V (Complex.I, (0 : ℂ))).prod
      ((ContinuousLinearMap.apply ℝ V ((0 : ℂ), (1 : ℂ))).prod
        (ContinuousLinearMap.apply ℝ V ((0 : ℂ), Complex.I))))

/-- The linear combination `h ↦ h.1.re X₁ + h.1.im X₂ + h.2.re X₃ + h.2.im X₄`. -/
def lin (h : V) (X : W4) : V :=
  h.1.re • X.1 + h.1.im • X.2.1 + h.2.re • X.2.2.1 + h.2.im • X.2.2.2

lemma clm_eq_lin (M : V →L[ℝ] V) (h : V) : M h = lin h (ev4 M) := by
  have e : h = h.1.re • ((1 : ℂ), (0 : ℂ)) + h.1.im • (Complex.I, (0 : ℂ)) +
      h.2.re • ((0 : ℂ), (1 : ℂ)) + h.2.im • ((0 : ℂ), Complex.I) := by
    obtain ⟨h1, h2⟩ := h
    ext <;> simp
  have h1 := congrArg M e
  rw [h1, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  rfl

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

/-- The four columns of `K̃`. -/
def kbar (a : ℝ) (y : (ℝ × ℝ) × ℂ) : W4 := ev4 (Kt ρ Jbar a y)

/-- The Hadamard quotients of the columns, evaluated at `(0, 1)` and `(0, i)`. -/
def Fh (a : ℝ) (y : (ℝ × ℝ) × ℂ) : W4 × W4 :=
  (hq (kbar ρ Jbar a) y ((0 : ℝ × ℝ), (1 : ℂ)), hq (kbar ρ Jbar a) y ((0 : ℝ × ℝ), Complex.I))

lemma bddDerivOn_kbar (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (a : ℝ) : BddDerivOn (kbar ρ Jbar a) univ :=
  QN10.BddDerivOn.clm_comp (bddDerivOn_Kt' ρ b Jbar Jinf Sinf hρ hb hstd a) ev4

lemma kbar_zero (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) (a : ℝ) (x : ℝ × ℝ) :
    kbar ρ Jbar a (x, 0) = 0 := by
  simp [kbar, Kt_zero ρ Jbar h0]

lemma bddDerivOn_Fh (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (a : ℝ) : BddDerivOn (Fh ρ Jbar a) univ := by
  have h := bddDerivOn_hq (kbar ρ Jbar a) (bddDerivOn_kbar ρ b Jbar Jinf Sinf hρ hb hstd a)
  have h1 := QN10.BddDerivOn.clm_comp h
    (ContinuousLinearMap.apply ℝ W4 ((0 : ℝ × ℝ), (1 : ℂ)))
  have h2 := QN10.BddDerivOn.clm_comp h
    (ContinuousLinearMap.apply ℝ W4 ((0 : ℝ × ℝ), Complex.I))
  have h3 := BddDerivOn.add (QN10.BddDerivOn.clm_comp h1 (ContinuousLinearMap.inl ℝ W4 W4))
    (QN10.BddDerivOn.clm_comp h2 (ContinuousLinearMap.inr ℝ W4 W4))
  have e : Fh ρ Jbar a = fun y =>
      (ContinuousLinearMap.inl ℝ W4 W4 ∘ (ContinuousLinearMap.apply ℝ W4 ((0 : ℝ × ℝ), (1 : ℂ)) ∘
        hq (kbar ρ Jbar a))) y +
      (ContinuousLinearMap.inr ℝ W4 W4 ∘ (ContinuousLinearMap.apply ℝ W4 ((0 : ℝ × ℝ), Complex.I) ∘
        hq (kbar ρ Jbar a))) y := by
    funext y; simp [Fh]
  rw [e]; exact h3

/-- `Q(F, h, w) = lin h (w.re F₁ + w.im F_I)`. -/
def Qf (F : W4 × W4) (h : V) (w : ℂ) : V := lin h (w.re • F.1 + w.im • F.2)

/-- **The Hadamard form of `K̃`.** -/
lemma Kt_apply_eq (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (a : ℝ) (y : (ℝ × ℝ) × ℂ) (h : V) :
    Kt ρ Jbar a y h = Qf (Fh ρ Jbar a y) h y.2 := by
  have hk := eq_hq (kbar ρ Jbar a) (kbar_zero ρ Jbar hstd.2.2.1 a)
    (bddDerivOn_kbar ρ b Jbar Jinf Sinf hρ hb hstd a).1 y
  have e : ((0 : ℝ × ℝ), y.2) = y.2.re • ((0 : ℝ × ℝ), (1 : ℂ)) + y.2.im • ((0 : ℝ × ℝ), Complex.I) := by
    ext <;> simp
  rw [e, map_add, map_smul, map_smul] at hk
  rw [clm_eq_lin, Qf, Fh]
  exact congrArg (lin h) hk

/-! ### The jointly smooth integrands -/

/-- Compact coordinates `((λ̃, μ̃, ẽN, κ), (uT, uN, c))`. -/
abbrev Cs := (ℂ × ℂ × ℝ × ℝ) × (ℂ × ℂ × ℂ)

/-- `ζ = λ̃ uT`, retracted into `ball 0 (1/2)` (identity on `ball 0 (1/8)`). -/
def zr (c : Cs) : ℂ := rtr (1 / 2) (c.1.1 * c.2.1)

/-- The log-chart shift `(Re, Im) logChart ζ`. -/
def ell (c : Cs) : ℝ × ℝ := ((logChart (zr c)).re, (logChart (zr c)).im)

/-- `v = ẽN uN`. -/
def mN (c : Cs) : ℂ := (c.1.2.2.1 : ℂ) * c.2.2.1

/-- `2π (1 + ζ) μ̃`. -/
def czf (c : Cs) : ℂ := ((2 * π : ℝ) : ℂ) * (1 + zr c) * c.1.2.1

def Dz (c : Cs) (X : V) : V := (czf c * X.1, X.2)

/-- `i / (1 + ζ)`. -/
def gz (c : Cs) : ℂ := Complex.I * (1 + zr c)⁻¹

/-- `λ̃ / (2π (1 + ζ))`. -/
def d1 (c : Cs) : ℂ := c.1.1 * (((2 * π : ℝ) : ℂ) * (1 + zr c))⁻¹

/-- The `+∞` zero-order integrand (images of `uN = 1, i`). -/
def phiRZ0 (y : Cs × (W4 × W4)) : V × V :=
  y.1.1.2.2.2 • (Dz y.1 (Qf y.2 (gz y.1, 0) 1), Dz y.1 (Qf y.2 (gz y.1, 0) Complex.I))

/-- The `+∞` product integrand (images of `(a, b) = (1,0), (i,0), (0,1), (0,i)`). -/
def phiRP0 (y : Cs × (W4 × W4)) : W4 :=
  y.1.1.2.2.2 • (Dz y.1 (Qf y.2 (d1 y.1, 0) y.1.2.2.1),
    Dz y.1 (Qf y.2 (d1 y.1 * Complex.I, 0) y.1.2.2.1),
    Dz y.1 (Qf y.2 (0, (y.1.1.2.2.1 : ℂ)) y.1.2.2.1),
    Dz y.1 (Qf y.2 (0, (y.1.1.2.2.1 : ℂ) * Complex.I) y.1.2.2.1))

lemma norm_zr_lt (c : Cs) : ‖zr c‖ < 1 / 2 := norm_rtr_lt (by norm_num) _

lemma one_add_zr_ne (c : Cs) : 1 + zr c ≠ 0 := by
  intro h
  have h1 : zr c = -1 := by linear_combination h
  have := norm_zr_lt c
  rw [h1, norm_neg, norm_one] at this
  norm_num at this

lemma contDiff_zr : ContDiff ℝ ∞ zr :=
  (rtr_contDiff _).comp ((contDiff_fst.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))

lemma contDiff_inv_one_add_zr : ContDiff ℝ ∞ (fun c : Cs => (1 + zr c)⁻¹) :=
  (contDiff_const.add contDiff_zr).inv one_add_zr_ne

lemma contDiff_logChart_zr : ContDiff ℝ ∞ (fun c : Cs => logChart (zr c)) :=
  logChart_contDiffOn.comp_contDiff contDiff_zr fun c =>
    mem_ball_zero_iff.2 ((norm_zr_lt c).trans (by norm_num))

lemma contDiff_ell : ContDiff ℝ ∞ ell :=
  (Complex.reCLM.contDiff.comp contDiff_logChart_zr).prodMk
    (Complex.imCLM.contDiff.comp contDiff_logChart_zr)

lemma contDiff_mN : ContDiff ℝ ∞ mN :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp
    contDiff_fst)))).mul (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))

lemma contDiff_lin : ContDiff ℝ ∞ (fun p : V × W4 => lin p.1 p.2) := by
  unfold lin
  have hre1 : ContDiff ℝ ∞ (fun p : V × W4 => p.1.1.re) :=
    Complex.reCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)
  have him1 : ContDiff ℝ ∞ (fun p : V × W4 => p.1.1.im) :=
    Complex.imCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)
  have hre2 : ContDiff ℝ ∞ (fun p : V × W4 => p.1.2.re) :=
    Complex.reCLM.contDiff.comp (contDiff_snd.comp contDiff_fst)
  have him2 : ContDiff ℝ ∞ (fun p : V × W4 => p.1.2.im) :=
    Complex.imCLM.contDiff.comp (contDiff_snd.comp contDiff_fst)
  exact (((hre1.smul (contDiff_fst.comp contDiff_snd)).add
    (him1.smul (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)))).add
    (hre2.smul (contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))))).add
    (him2.smul (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))))

lemma contDiff_Qf {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Y → W4 × W4}
    {h : Y → V} {w : Y → ℂ} (hF : ContDiff ℝ ∞ F) (hh : ContDiff ℝ ∞ h) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun y => Qf (F y) (h y) (w y)) := by
  unfold Qf
  exact contDiff_lin.comp (hh.prodMk (((Complex.reCLM.contDiff.comp hw).smul
    (contDiff_fst.comp hF)).add ((Complex.imCLM.contDiff.comp hw).smul (contDiff_snd.comp hF))))

lemma contDiff_Dz {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {c : Y → Cs}
    {X : Y → V} (hc : ContDiff ℝ ∞ c) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun y => Dz (c y) (X y)) := by
  unfold Dz czf
  exact ((((contDiff_const.mul (contDiff_const.add (contDiff_zr.comp hc))).mul
    (contDiff_fst.comp (contDiff_snd.comp (contDiff_fst.comp hc))))).mul
    (contDiff_fst.comp hX)).prodMk (contDiff_snd.comp hX)

lemma contDiff_phiRZ0 : ContDiff ℝ ∞ phiRZ0 := by
  have hc : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => y.1) := contDiff_fst
  have hg : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => ((gz y.1, (0 : ℂ)) : V)) :=
    ((contDiff_const.mul (contDiff_inv_one_add_zr.comp hc))).prodMk contDiff_const
  have hκ : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => y.1.1.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_fst.comp hc)))
  unfold phiRZ0
  exact hκ.smul ((contDiff_Dz hc (contDiff_Qf contDiff_snd hg contDiff_const)).prodMk
    (contDiff_Dz hc (contDiff_Qf contDiff_snd hg contDiff_const)))

lemma contDiff_phiRP0 : ContDiff ℝ ∞ phiRP0 := by
  have hc : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => y.1) := contDiff_fst
  have hd : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => d1 y.1) := by
    unfold d1
    exact (contDiff_fst.comp (contDiff_fst.comp hc)).mul
      ((contDiff_const.mul (contDiff_const.add (contDiff_zr.comp hc))).inv fun y =>
        mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (one_add_zr_ne _))
  have heN : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => ((y.1.1.2.2.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_fst.comp hc))))
  have huN : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => y.1.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp hc))
  have hκ : ContDiff ℝ ∞ (fun y : Cs × (W4 × W4) => y.1.1.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp (contDiff_fst.comp hc)))
  unfold phiRP0
  refine hκ.smul ((contDiff_Dz hc (contDiff_Qf contDiff_snd (hd.prodMk contDiff_const) huN)).prodMk
    ((contDiff_Dz hc (contDiff_Qf contDiff_snd ((hd.mul contDiff_const).prodMk contDiff_const)
      huN)).prodMk ((contDiff_Dz hc (contDiff_Qf contDiff_snd (contDiff_const.prodMk heN) huN)).prodMk
      (contDiff_Dz hc (contDiff_Qf contDiff_snd (contDiff_const.prodMk (heN.mul contDiff_const))
        huN)))))

end QN14

end

end FiniteEnergyPlane

/-!
# Q-N, layer 15 (local, NOT published): the `+∞` parameter and the `UC` classes

* `bR q = (λ̃, μ̃, ẽN, κ)` with `λ = e^{χT}/z`, `μ = e^{χN} z/e^{χT}`, cut off by
  `κ' = smoothTransition (s + 1)`, and `κ = smoothTransition s`; continuous and bounded.
* `psiR Φ₀`: the integrand `((q, b), u) ↦ Φ₀((b, u), Fh((s, t) + ell, mN))`; `uc_psiR`: every `UC n`.
* `B2`, `B4`: the bilinear maps that feed the `L⁴` factors.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN15

open QN9 QN10 QN11 QN13 QN14

/-- A continuous `g`, zero on `(-∞, -1]` and bounded on `[1, ∞)`, is bounded. -/
lemma bdd_of_right_bdd (g : ℝ → ℝ) (hg : Continuous g) (D : ℝ) (hA : ∀ s ≤ -1, g s = 0)
    (hD : ∀ s ≥ 1, |g s| ≤ D) : ∃ M, ∀ s, |g s| ≤ M := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (max B D) 0, fun s => ?_⟩
  rcases le_or_gt 1 s with h | h
  · exact (hD s h).trans ((le_max_right _ _).trans (le_max_left _ _))
  rcases le_or_gt s (-1) with h' | h'
  · rw [hA s h', abs_zero]; exact le_max_right _ _
  · exact (hB s ⟨h'.le, h.le⟩).trans ((le_max_left _ _).trans (le_max_left _ _))

/-- The right cut-off `κ'(s) = smoothTransition (s + 1)` (`= 0` for `s ≤ -1`, `= 1` for `s ≥ 0`). -/
def kp (s : ℝ) : ℝ := Real.smoothTransition (s + 1)

lemma kp_contDiff : ContDiff ℝ ∞ kp :=
  Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

lemma kp_eq_zero {s : ℝ} (h : s ≤ -1) : kp s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma kp_eq_one {s : ℝ} (h : 0 ≤ s) : kp s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma abs_kp_le (s : ℝ) : |kp s| ≤ 1 := by
  unfold kp
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _

/-- The bounded `+∞` coefficients `(λ̃, μ̃, ẽN, κ)`. -/
def bR (χT χN : ℝ → ℝ) (q : ℝ × ℝ) : ℂ × ℂ × ℝ × ℝ :=
  (((kp q.1 * Real.exp (χT q.1) : ℝ) : ℂ) * (cylInf q.1 q.2)⁻¹,
    ((kp q.1 * Real.exp (χN q.1) * Real.exp (-χT q.1) : ℝ) : ℂ) * cylInf q.1 q.2,
    kp q.1 * Real.exp (χN q.1), Real.smoothTransition q.1)

lemma bR_continuous {χT χN : ℝ → ℝ} (hT : Continuous χT) (hN : Continuous χN) :
    Continuous (bR χT χN) := by
  have hk := kp_contDiff.continuous
  have hz : Continuous (fun q : ℝ × ℝ => cylInf q.1 q.2) := continuous_cylInf
  have hzi : Continuous (fun q : ℝ × ℝ => (cylInf q.1 q.2)⁻¹) :=
    hz.inv₀ fun q => cylInf_ne_zero _ _
  unfold bR
  refine ((Complex.continuous_ofReal.comp ((hk.comp continuous_fst).mul
    (Real.continuous_exp.comp (hT.comp continuous_fst)))).mul hzi).prodMk
    (((Complex.continuous_ofReal.comp (((hk.comp continuous_fst).mul
      (Real.continuous_exp.comp (hN.comp continuous_fst))).mul
      (Real.continuous_exp.comp (hT.comp continuous_fst).neg))).mul hz).prodMk
    (((hk.comp continuous_fst).mul (Real.continuous_exp.comp (hN.comp continuous_fst))).prodMk
      (Real.smoothTransition.continuous.comp continuous_fst)))

lemma bR_bdd {χT χN : ℝ → ℝ} {δ δT : ℝ} (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ) :
    ∃ M, ∀ q, ‖bR χT χN q‖ ≤ M := by
  have hk := kp_contDiff.continuous
  have hcT := hχT.1.continuous
  have hcN := hχN.1.continuous
  have hδ : δ < δT := lt_of_le_of_lt (le_max_left _ _) hδT.1
  have hδT0 : δT < 0 := hδT.2
  obtain ⟨M1, hM1⟩ := bdd_of_right_bdd (fun s => kp s * Real.exp (χT s) * Real.exp (-(2 * π * s)))
    ((hk.mul (Real.continuous_exp.comp hcT)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg))
    (Real.exp (χT 1 - 2 * π)) (fun s hs => by simp [kp_eq_zero hs]) (fun s hs => by
      rw [kp_eq_one (by linarith), one_mul, abs_of_pos (by positivity), ← Real.exp_add,
        hχT.eq_right hs]
      exact Real.exp_le_exp.2 (by nlinarith))
  obtain ⟨M2, hM2⟩ := bdd_of_right_bdd
    (fun s => kp s * Real.exp (χN s) * Real.exp (-χT s) * Real.exp (2 * π * s))
    (((hk.mul (Real.continuous_exp.comp hcN)).mul (Real.continuous_exp.comp hcT.neg)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    (Real.exp (χN 1 - χT 1 + 2 * π)) (fun s hs => by simp [kp_eq_zero hs]) (fun s hs => by
      rw [kp_eq_one (by linarith), one_mul, abs_of_pos (by positivity), ← Real.exp_add,
        ← Real.exp_add, hχT.eq_right hs, hχN.eq_right hs]
      exact Real.exp_le_exp.2 (by nlinarith))
  obtain ⟨M3, hM3⟩ := bdd_of_right_bdd (fun s => kp s * Real.exp (χN s))
    (hk.mul (Real.continuous_exp.comp hcN)) (Real.exp (χN 1))
    (fun s hs => by simp [kp_eq_zero hs]) (fun s hs => by
      rw [kp_eq_one (by linarith), one_mul, abs_of_pos (by positivity), hχN.eq_right hs]
      exact Real.exp_le_exp.2 (by nlinarith))
  refine ⟨max (max M1 M2) (max M3 1), fun q => ?_⟩
  simp only [bR, norm_prod_le_iff, Real.norm_eq_abs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, n2_norm_cylInf,
      ← Real.exp_neg, ← abs_of_pos (Real.exp_pos (-(2 * π * q.1))), ← abs_mul]
    exact (hM1 q.1).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, n2_norm_cylInf,
      ← abs_of_pos (Real.exp_pos (2 * π * q.1)), ← abs_mul]
    exact (hM2 q.1).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hM3 q.1).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (Real.smoothTransition.le_one _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-! ### The integrands and their `UC` classes -/

abbrev Bsp := ℂ × ℂ × ℝ × ℝ
abbrev Pp := (ℝ × ℝ) × Bsp
abbrev Ev := ℂ × ℂ × ℂ

def σR : Pp × Ev →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) Bsp).comp (ContinuousLinearMap.fst ℝ Pp Ev)

def τR : Pp × Ev →L[ℝ] Cs :=
  ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) Bsp).comp (ContinuousLinearMap.fst ℝ Pp Ev)).prod
    (ContinuousLinearMap.snd ℝ Pp Ev)

variable (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
  (Sinf : ℝ → Mat 1)

/-- The jointly smooth `+∞` integrand on `Pp × Ev`. -/
def psiR {Out : Type} (Φ₀ : Cs × (W4 × W4) → Out) (a : ℝ) (z : Pp × Ev) : Out :=
  Φ₀ (τR z, Fh ρ Jbar a (σR z + ell (τR z), mN (τR z)))

theorem uc_psiR (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    {Out : Type} [NormedAddCommGroup Out] [NormedSpace ℝ Out]
    (Φ₀ : Cs × (W4 × W4) → Out) (hΦ : ContDiff ℝ ∞ Φ₀) (a : ℝ)
    {χT χN : ℝ → ℝ} {δ δT : ℝ} (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ) (n : ℕ) :
    NEM.UC n Out (fun (q : ℝ × ℝ) (u : Ev) => psiR ρ Jbar Φ₀ a ((q, bR χT χN q), u)) := by
  obtain ⟨Mb, hMb⟩ := bR_bdd hδT hχT hχN
  have hF := bddDerivOn_Fh ρ b Jbar Jinf Sinf hρ hb hstd a
  have hfr : ∀ R : ℝ, BddDerivOn (psiR ρ Jbar Φ₀ a) (τR ⁻¹' closedBall (0 : Cs) (max Mb R)) :=
    fun R => bddDerivOn_frame σR τR (Fh ρ Jbar a) hF ell contDiff_ell mN contDiff_mN Φ₀ hΦ _
      (isCompact_closedBall _ _)
  refine NEM.uc_of_comp_bdd Out (psiR ρ Jbar Φ₀ a) (hfr 0).1 (fun q => (q, bR χT χN q))
    (continuous_id.prodMk (bR_continuous hχT.1.continuous hχN.1.continuous)) (fun k R => ?_) n
  obtain ⟨C, hC⟩ := (hfr R).2 k
  refine ⟨C, fun q u hu => hC _ ?_⟩
  simp only [mem_preimage, mem_closedBall_zero_iff, τR, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  rw [mem_closedBall_zero_iff] at hu
  exact norm_prod_le_iff.2 ⟨(hMb q).trans (le_max_left _ _), hu.trans (le_max_right _ _)⟩

/-! ### The bilinear maps -/

/-- `B2 (Z₁, Z_I) w = w.re Z₁ + w.im Z_I`. -/
def B2 : ((ℂ × ℂ) × (ℂ × ℂ)) →L[ℝ] ℂ →L[ℝ] (ℂ × ℂ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (ℂ →ₗ[ℝ] (ℂ × ℂ)) ≃ₗ[ℝ] (ℂ →L[ℝ] (ℂ × ℂ))).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun (Z : (ℂ × ℂ) × (ℂ × ℂ)) (w : ℂ) => w.re • Z.1 + w.im • Z.2)
        (fun Z Z' w => by simp only [Prod.fst_add, Prod.snd_add, smul_add]; abel)
        (fun r Z w => by simp only [Prod.smul_fst, Prod.smul_snd, smul_comm _ r, smul_add])
        (fun Z w w' => by simp only [Complex.add_re, Complex.add_im, add_smul]; abel)
        (fun r Z w => by
          simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, mul_smul, smul_add]))

@[simp] lemma B2_apply (Z : (ℂ × ℂ) × (ℂ × ℂ)) (w : ℂ) : B2 Z w = w.re • Z.1 + w.im • Z.2 := rfl

/-- `B4 (C₁, …, C₄) (a, b) = a.re C₁ + a.im C₂ + b.re C₃ + b.im C₄`. -/
def B4 : W4 →L[ℝ] (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ)) ≃ₗ[ℝ] ((ℂ × ℂ) →L[ℝ] (ℂ × ℂ))).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun (X : W4) (h : (ℂ × ℂ)) => lin h X)
        (fun X X' h => by simp only [lin, Prod.fst_add, Prod.snd_add, smul_add]; abel)
        (fun r X h => by simp only [lin, Prod.smul_fst, Prod.smul_snd, smul_comm _ r, smul_add])
        (fun X h h' => by
          simp only [lin, Prod.fst_add, Prod.snd_add, Complex.add_re, Complex.add_im, add_smul]
          abel)
        (fun r X h => by
          simp only [lin, Prod.smul_fst, Prod.smul_snd, Complex.smul_re, Complex.smul_im,
            smul_eq_mul, mul_smul, smul_add]))

@[simp] lemma B4_apply (X : W4) (h : (ℂ × ℂ)) : B4 X h = lin h X := rfl

end QN15

end

end FiniteEnergyPlane

/-!
# Q-N, layer 16 (local, NOT published): the pointwise `+∞` identities

For `s > 0`, with `‖λ uT‖ < 1/8`, `‖eN uN‖ < ρ/8` and `β s = 0`:
* `right_core`: `W · (Jbar(ψ, v) − jStd) X = Dz (Qf (Fh y) (cylScaleInv' X) uN)` (`y` the log-chart point);
* `right_zero`: the zero-order term `W (Jbar(ψ, v) − jStd)(2πi z, 0)` is `B2 (psiR phiRZ0 …) uN`;
* `right_prod`: the product term `W (Jbar(ψ, v) − jStd)(eT a, eN b)` is `B4 (psiR phiRP0 …) (a, b)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN16

open QN9 QN10 QN11 QN13 QN14 QN15

/-! ### Linearity helpers -/

lemma Qf_eq_B4 (F : W4 × W4) (h : ℂ × ℂ) (w : ℂ) :
    Qf F h w = B4 (w.re • F.1 + w.im • F.2) h := rfl

lemma Qf_ofReal_mul (F : W4 × W4) (h : ℂ × ℂ) (r : ℝ) (w : ℂ) :
    Qf F h ((r : ℂ) * w) = r • Qf F h w := by
  rw [Qf_eq_B4, Qf_eq_B4, Complex.re_ofReal_mul, Complex.im_ofReal_mul, mul_smul, mul_smul,
    ← smul_add, map_smul, ContinuousLinearMap.smul_apply]

lemma Qf_decomp (F : W4 × W4) (h : ℂ × ℂ) (w : ℂ) :
    Qf F h w = w.re • Qf F h 1 + w.im • Qf F h Complex.I := by
  simp only [Qf_eq_B4, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, one_smul,
    zero_smul, add_zero, zero_add, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]

lemma Qf_add_h (F : W4 × W4) (h h' : ℂ × ℂ) (w : ℂ) :
    Qf F (h + h') w = Qf F h w + Qf F h' w := by
  simp only [Qf_eq_B4, map_add]

lemma Qf_smul_h (F : W4 × W4) (r : ℝ) (h : ℂ × ℂ) (w : ℂ) :
    Qf F (r • h) w = r • Qf F h w := by
  simp only [Qf_eq_B4, map_smul]

lemma Dz_add (c : Cs) (X Y : ℂ × ℂ) : Dz c (X + Y) = Dz c X + Dz c Y := by
  ext <;> simp [Dz, mul_add]

lemma Dz_smul (c : Cs) (r : ℝ) (X : ℂ × ℂ) : Dz c (r • X) = r • Dz c X := by
  ext <;> simp [Dz, Complex.real_smul] <;> ring

/-! ### Algebra of the cylinder conjugation -/

variable (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)

lemma cyl_conj (s t : ℝ) (v : ℂ) (X : ℂ × ℂ) :
    (Jbar (cylInf s t, v) - jStd) X =
      cylScale s t ((cylJ Jbar s t v - jStd) (cylScaleInv s t X)) := by
  have hc : ((2 * π : ℝ) : ℂ) * cylInf s t ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (cylInf_ne_zero s t)
  obtain ⟨X1, X2⟩ := X
  have key : ((2 * π : ℝ) : ℂ) * cylInf s t * ((((2 * π : ℝ) : ℂ) * cylInf s t)⁻¹ * X1) = X1 :=
    mul_inv_cancel_left₀ hc X1
  simp only [cylJ, cylScale, cylScaleInv, jStd, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, key]
  ext
  · simp only [Prod.fst_sub]
    field_simp
    rw [mul_div_cancel_right₀ _ (cylInf_ne_zero s t)]
  · simp

lemma logChart_re_ge {ζ : ℂ} (hζ : ‖ζ‖ < 1 / 8) : -1 ≤ (logChart ζ).re := by
  have h1 : (7 : ℝ) / 8 ≤ ‖1 + ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-ζ)
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  have hpos : (0 : ℝ) < ‖1 + ζ‖ := by linarith
  have h2 : -1 ≤ Real.log ‖1 + ζ‖ := by
    rw [Real.le_log_iff_exp_le hpos]
    have := Real.exp_neg_one_lt_half
    linarith
  have hre : (logChart ζ).re = Real.log ‖1 + ζ‖ / (2 * π) := by
    simp only [logChart, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re]
    rw [div_eq_mul_inv]
  rw [hre, le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three]

/-! ### The core identity -/

variable (ρ b : ℝ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → Mat 1)

/-- The log-chart point and its pieces, for `c = (bR q, u)`. -/
theorem right_core (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (hs : 0 < q.1) (u : Ev)
    (h1 : ‖(bR χT χN q).1 * u.1‖ < 1 / 8) (h2 : ‖((bR χT χN q).2.2.1 : ℂ) * u.2.1‖ < ρ / 8)
    (hβ0 : β q.1 = 0) (X : ℂ × ℂ) :
    ((Real.exp (-χT q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd) X).1,
      (Real.exp (-χN q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd) X).2) =
      Dz (bR χT χN q, u) (Qf (Fh ρ Jbar (-2) (q + ell (bR χT χN q, u), mN (bR χT χN q, u)))
        (cylScaleInv (q + ell (bR χT χN q, u)).1 (q + ell (bR χT χN q, u)).2 X) u.2.1) := by
  obtain ⟨s, t⟩ := q
  obtain ⟨uT, uN, c0⟩ := u
  simp only at hs h1 h2 hβ0 ⊢
  set c : Cs := (bR χT χN (s, t), (uT, uN, c0)) with hc
  have hk : kp s = 1 := kp_eq_one hs.le
  set z := cylInf s t with hz
  have hz0 : z ≠ 0 := cylInf_ne_zero s t
  have hb1 : (bR χT χN (s, t)).1 = (Real.exp (χT s) : ℂ) * z⁻¹ := by simp [bR, hk, hz]
  have hb2 : (bR χT χN (s, t)).2.1 =
      ((Real.exp (χN s) * Real.exp (-χT s) : ℝ) : ℂ) * z := by simp [bR, hk, hz]
  have hb3 : (bR χT χN (s, t)).2.2.1 = Real.exp (χN s) := by simp [bR, hk]
  set ζ := (Real.exp (χT s) : ℂ) * z⁻¹ * uT with hζ
  have hζ1 : ‖ζ‖ < 1 / 8 := by rw [hζ, ← hb1]; exact h1
  have hzr : zr c = ζ := by
    simp only [zr, hc, hb1]
    exact rtr_eq (by norm_num) (by rw [← hζ]; linarith)
  set L := logChart ζ with hL
  have hell : ell c = (L.re, L.im) := by simp [ell, hzr, hL]
  have hv : (β s : ℂ) * c0 + (Real.exp (χN s) : ℂ) * uN = (Real.exp (χN s) : ℂ) * uN := by
    simp [hβ0]
  have hmN : mN c = (Real.exp (χN s) : ℂ) * uN := by simp [mN, hc, hb3]
  have hψ : z + (Real.exp (χT s) : ℂ) * uT = cylInf (s + L.re) (t + L.im) := by
    rw [← cylInf_mul_one_add s t (hζ1.trans (by norm_num)), ← hz, hζ]
    field_simp
  have hs' : -1 ≤ s + L.re := by have := logChart_re_ge hζ1; linarith
  have hvr : ‖(Real.exp (χN s) : ℂ) * uN‖ < ρ / 2 / 4 := by
    rw [← hb3]; linarith
  -- `cylJ − jStd = K̃`
  have hK : cylJ Jbar (s + L.re) (t + L.im) ((Real.exp (χN s) : ℂ) * uN) - jStd =
      Kt ρ Jbar (-2) ((s + L.re, t + L.im), (Real.exp (χN s) : ℂ) * uN) := by
    simp only [Kt, gJ]
    rw [sfl_eq (by linarith), rtr_eq (half_pos hρ) hvr]
  rw [hv, hψ, cyl_conj, hK, Kt_apply_eq ρ b Jbar Jinf Sinf hρ hb hstd, hell, hmN]
  simp only [Prod.mk_add_mk]
  rw [Qf_ofReal_mul]
  set Y := Qf (Fh ρ Jbar (-2) ((s + L.re, t + L.im), (Real.exp (χN s) : ℂ) * uN))
    (cylScaleInv (s + L.re) (t + L.im) X) uN
  have hN : (Real.exp (-χN s) : ℂ) * (Real.exp (χN s) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hT : (Real.exp (-χT s) : ℂ) * (Real.exp (χT s) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hcz : czf c = ((2 * π : ℝ) : ℂ) * (1 + ζ) *
      (((Real.exp (χN s) * Real.exp (-χT s) : ℝ) : ℂ) * z) := by
    show ((2 * π : ℝ) : ℂ) * (1 + zr c) * (bR χT χN (s, t)).2.1 = _
    rw [hzr, hb2]
  simp only [cylScale, ContinuousLinearMap.coe_prodMap', Prod.map, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Complex.real_smul,
    Dz, hcz]
  have hzz : z + (Real.exp (χT s) : ℂ) * uT = z * (1 + ζ) := by rw [hζ]; field_simp
  clear_value ζ z
  rw [← hψ, hzz]
  simp only [Complex.ofReal_mul]
  ext
  · simp only
    ring
  · simp only
    linear_combination Y.2 * hN

/-- The scaled point of the log chart is `z (1 + ζ)`. -/
lemma cylInf_ell (χT χN : ℝ → ℝ) (q : ℝ × ℝ) (hs : 0 < q.1) (u : Ev)
    (h1 : ‖(bR χT χN q).1 * u.1‖ < 1 / 8) :
    cylInf (q + ell (bR χT χN q, u)).1 (q + ell (bR χT χN q, u)).2 =
      cylInf q.1 q.2 * (1 + zr (bR χT χN q, u)) := by
  obtain ⟨s, t⟩ := q
  simp only at hs h1 ⊢
  have hzr : zr (bR χT χN (s, t), u) = (bR χT χN (s, t)).1 * u.1 :=
    rtr_eq (by norm_num) (by linarith)
  rw [hzr, cylInf_mul_one_add s t (h1.trans (by norm_num))]
  simp [ell, hzr]

/-- The `+∞` zero-order integrand. -/
def phiRZ (ρ : ℝ) (χT χN : ℝ → ℝ) (q : ℝ × ℝ) (u : Ev) : (ℂ × ℂ) × (ℂ × ℂ) :=
  psiR ρ Jbar phiRZ0 (-2) ((q, bR χT χN q), u)

/-- The `+∞` product integrand. -/
def phiRP (ρ : ℝ) (χT χN : ℝ → ℝ) (q : ℝ × ℝ) (u : Ev) : W4 :=
  psiR ρ Jbar phiRP0 (-2) ((q, bR χT χN q), u)

lemma bR_kappa (χT χN : ℝ → ℝ) (q : ℝ × ℝ) : (bR χT χN q).2.2.2 = Real.smoothTransition q.1 := rfl

/-- **`+∞` zero-order identity.** -/
theorem right_zero (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (χT χN β : ℝ → ℝ) (hβ : IsLeftCutoff β) (q : ℝ × ℝ) (u : Ev)
    (h1 : ‖(bR χT χN q).1 * u.1‖ < 1 / 8) (h2 : ‖((bR χT χN q).2.2.1 : ℂ) * u.2.1‖ < ρ / 8) :
    B2 (phiRZ Jbar ρ χT χN q u) u.2.1 = Real.smoothTransition q.1 •
      ((Real.exp (-χT q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd)
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0)).1,
      (Real.exp (-χN q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd)
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0)).2) := by
  rcases le_or_gt q.1 0 with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos hs, zero_smul]
    simp [phiRZ, psiR, phiRZ0, τR, bR_kappa, Real.smoothTransition.zero_of_nonpos hs]
  rw [right_core Jbar ρ b Jinf Sinf hρ hb hstd χT χN β q hs u h1 h2 (hβ.2.2 _ hs.le)]
  have hc := cylInf_ell χT χN q hs u h1
  have hz0 := cylInf_ne_zero q.1 q.2
  have h1z : 1 + zr (bR χT χN q, u) ≠ 0 := one_add_zr_ne _
  have hX : cylScaleInv (q + ell (bR χT χN q, u)).1 (q + ell (bR χT χN q, u)).2
      (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0) = (gz (bR χT χN q, u), 0) := by
    simp only [cylScaleInv, hc, ContinuousLinearMap.coe_prodMap', Prod.map,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, gz]
    congr 1
    field_simp
  rw [hX]
  simp only [phiRZ, psiR, phiRZ0, τR, σR, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', map_smul, ContinuousLinearMap.smul_apply, B2_apply, bR_kappa]
  rw [Qf_decomp _ _ u.2.1, Dz_add, Dz_smul, Dz_smul]

/-- **`+∞` product identity.** -/
theorem right_prod (hρ : 0 < ρ) (hb : 0 < b) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (χT χN β : ℝ → ℝ) (hβ : IsLeftCutoff β) (q : ℝ × ℝ) (u : Ev)
    (h1 : ‖(bR χT χN q).1 * u.1‖ < 1 / 8) (h2 : ‖((bR χT χN q).2.2.1 : ℂ) * u.2.1‖ < ρ / 8)
    (a3 b3 : ℂ) :
    B4 (phiRP Jbar ρ χT χN q u) (a3, b3) = Real.smoothTransition q.1 •
      ((Real.exp (-χT q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd)
          ((Real.exp (χT q.1) : ℂ) * a3, (Real.exp (χN q.1) : ℂ) * b3)).1,
      (Real.exp (-χN q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd)
          ((Real.exp (χT q.1) : ℂ) * a3, (Real.exp (χN q.1) : ℂ) * b3)).2) := by
  rcases le_or_gt q.1 0 with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos hs, zero_smul]
    simp [phiRP, psiR, phiRP0, τR, bR_kappa, Real.smoothTransition.zero_of_nonpos hs]
  rw [right_core Jbar ρ b Jinf Sinf hρ hb hstd χT χN β q hs u h1 h2 (hβ.2.2 _ hs.le)]
  have hc := cylInf_ell χT χN q hs u h1
  have hz0 := cylInf_ne_zero q.1 q.2
  have h1z : 1 + zr (bR χT χN q, u) ≠ 0 := one_add_zr_ne _
  have hk : kp q.1 = 1 := kp_eq_one hs.le
  have hb1 : (bR χT χN q).1 = (Real.exp (χT q.1) : ℂ) * (cylInf q.1 q.2)⁻¹ := by simp [bR, hk]
  have hb3 : (bR χT χN q).2.2.1 = Real.exp (χN q.1) := by simp [bR, hk]
  have hX : cylScaleInv (q + ell (bR χT χN q, u)).1 (q + ell (bR χT χN q, u)).2
      ((Real.exp (χT q.1) : ℂ) * a3, (Real.exp (χN q.1) : ℂ) * b3) =
      a3.re • (d1 (bR χT χN q, u), (0 : ℂ)) + a3.im • (d1 (bR χT χN q, u) * Complex.I, (0 : ℂ)) +
        b3.re • ((0 : ℂ), (((bR χT χN q).2.2.1 : ℝ) : ℂ)) +
        b3.im • ((0 : ℂ), (((bR χT χN q).2.2.1 : ℝ) : ℂ) * Complex.I) := by
    simp only [cylScaleInv, hc, ContinuousLinearMap.coe_prodMap', Prod.map,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, d1, hb1, hb3]
    ext <;> simp [Complex.real_smul] <;> field_simp <;> ring_nf <;>
      simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hX, Qf_add_h, Qf_add_h, Qf_add_h, Qf_smul_h, Qf_smul_h, Qf_smul_h, Qf_smul_h,
    Dz_add, Dz_add, Dz_add, Dz_smul, Dz_smul, Dz_smul, Dz_smul]
  simp only [phiRP, psiR, phiRP0, τR, σR, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', map_smul, ContinuousLinearMap.smul_apply, B4_apply, bR_kappa,
    lin]

end QN16

end

end FiniteEnergyPlane

/-!
# Q-N, layer 17 (local, NOT published): the `-∞` product term

`lcut 0 · W (Jbar(ψ, v) − jStd)(eT a, eN b) = B4 (phiLP q u) (a, b)`, where `phiLP` is a
Nemytskii integrand through a compact parameter (N2's `pLeft`, plus the bounded ratios
`e^{χT − χN}`, `e^{χN − χT}` cut off at `s ≤ 3`).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN17

open QN14 QN15 QN16

/-- The four weighted columns of `M`: `(M f).1, r₁ (M f).2` for `f = (1,0), (i,0)` and
`r₂ (M f).1, (M f).2` for `f = (0,1), (0,i)`. -/
def E4 (M : ℂ × ℂ →L[ℝ] ℂ × ℂ) (r : ℝ × ℝ) : W4 :=
  (((M ((1 : ℂ), (0 : ℂ))).1, (r.1 : ℂ) * (M ((1 : ℂ), (0 : ℂ))).2),
    ((M (Complex.I, (0 : ℂ))).1, (r.1 : ℂ) * (M (Complex.I, (0 : ℂ))).2),
    ((r.2 : ℂ) * (M ((0 : ℂ), (1 : ℂ))).1, (M ((0 : ℂ), (1 : ℂ))).2),
    ((r.2 : ℂ) * (M ((0 : ℂ), Complex.I)).1, (M ((0 : ℂ), Complex.I)).2))

lemma contDiff_E4 {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {M : Y → ℂ × ℂ →L[ℝ] ℂ × ℂ} {r : Y → ℝ × ℝ} (hM : ContDiff ℝ ∞ M) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (fun y => E4 (M y) (r y)) := by
  have hap : ∀ f : ℂ × ℂ, ContDiff ℝ ∞ (fun y => M y f) := fun f =>
    (ContinuousLinearMap.apply ℝ (ℂ × ℂ) f).contDiff.comp hM
  have h1 : ContDiff ℝ ∞ (fun y => ((r y).1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp hr)
  have h2 : ContDiff ℝ ∞ (fun y => ((r y).2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp hr)
  unfold E4
  exact ((contDiff_fst.comp (hap _)).prodMk (h1.mul (contDiff_snd.comp (hap _)))).prodMk
    (((contDiff_fst.comp (hap _)).prodMk (h1.mul (contDiff_snd.comp (hap _)))).prodMk
      (((h2.mul (contDiff_fst.comp (hap _))).prodMk (contDiff_snd.comp (hap _))).prodMk
        ((h2.mul (contDiff_fst.comp (hap _))).prodMk (contDiff_snd.comp (hap _)))))

/-- The bounded ratios, cut off at `s ≤ 3`. -/
def rL (χT χN : ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (lcut 2 q.1 * Real.exp (χT q.1 - χN q.1), lcut 2 q.1 * Real.exp (χN q.1 - χT q.1))

abbrev PL := (ℝ × (ℝ × ℂ × ℝ × ℝ × ℝ)) × (ℝ × ℝ)

/-- The compact parameter. -/
def pLP (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) : PL :=
  ((lcut 0 q.1, pLeft χT χN β q), rL χT χN q)

/-- The jointly smooth integrand. -/
def psiLP (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (y : PL × Ev) : W4 :=
  y.1.1.1 • E4 (psiLeft ρ Jbar (y.1.1.2, y.2)) y.1.2

lemma psiLP_contDiff (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) : ContDiff ℝ ∞ (psiLP ρ Jbar) := by
  unfold psiLP
  exact (contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).smul
    (contDiff_E4 ((psiLeft_contDiff ρ hρ Jbar hJ).comp
      ((contDiff_snd.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd))
      (contDiff_snd.comp contDiff_fst))

lemma rL_continuous {χT χN : ℝ → ℝ} (hT : Continuous χT) (hN : Continuous χN) :
    Continuous (rL χT χN) := by
  have h2 := (lcut_contDiff 2).continuous
  unfold rL
  exact ((h2.comp continuous_fst).mul (Real.continuous_exp.comp
    ((hT.comp continuous_fst).sub (hN.comp continuous_fst)))).prodMk
    ((h2.comp continuous_fst).mul (Real.continuous_exp.comp
      ((hN.comp continuous_fst).sub (hT.comp continuous_fst))))

lemma pLP_bdd {χT χN β : ℝ → ℝ} {bT b : ℝ} (hχT : IsSlopeWeight χT π bT)
    (hχN : IsSlopeWeight χN π b) (hβ : IsLeftCutoff β) : ∃ M, ∀ q, ‖pLP χT χN β q‖ ≤ M := by
  obtain ⟨M0, hM0⟩ := pLeft_bdd hχT hχN hβ
  have h2 := (lcut_contDiff 2).continuous
  have hcT := hχT.1.continuous
  have hcN := hχN.1.continuous
  have hl2 : ∀ s, |lcut 2 s| ≤ 1 := fun s => by
    rw [abs_of_nonneg (lcut_nonneg _ _)]; exact lcut_le_one _ _
  have hz3 : ∀ s ≥ (3 : ℝ), lcut 2 s = 0 := fun s hs => lcut_eq_zero (by linarith)
  obtain ⟨M1, -, hM1⟩ := bdd_of_left_bdd (fun s => lcut 2 s * Real.exp (χT s - χN s))
    (h2.mul (Real.continuous_exp.comp (hcT.sub hcN))) 3 (Real.exp (χT (-1) - χN (-1)))
    (fun s hs => by simp [hz3 s hs]) (fun s hs => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), hχT.eq_left hs, hχN.eq_left hs]
      calc |lcut 2 s| * Real.exp (χT (-1) + π * (s + 1) - (χN (-1) + π * (s + 1)))
          ≤ 1 * Real.exp (χT (-1) - χN (-1)) :=
            mul_le_mul (hl2 s) (le_of_eq (by congr 1; ring)) (Real.exp_pos _).le zero_le_one
        _ = _ := one_mul _)
  obtain ⟨M2, -, hM2⟩ := bdd_of_left_bdd (fun s => lcut 2 s * Real.exp (χN s - χT s))
    (h2.mul (Real.continuous_exp.comp (hcN.sub hcT))) 3 (Real.exp (χN (-1) - χT (-1)))
    (fun s hs => by simp [hz3 s hs]) (fun s hs => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), hχT.eq_left hs, hχN.eq_left hs]
      calc |lcut 2 s| * Real.exp (χN (-1) + π * (s + 1) - (χT (-1) + π * (s + 1)))
          ≤ 1 * Real.exp (χN (-1) - χT (-1)) :=
            mul_le_mul (hl2 s) (le_of_eq (by congr 1; ring)) (Real.exp_pos _).le zero_le_one
        _ = _ := one_mul _)
  refine ⟨max (max 1 M0) (max M1 M2), fun q => ?_⟩
  simp only [pLP, rL]
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;>
    simp only [Real.norm_eq_abs]
  · rw [abs_of_nonneg (lcut_nonneg _ _)]
    exact (lcut_le_one _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hM0 q).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hM1 q.1).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hM2 q.1).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The `-∞` product integrand. -/
def phiLP (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ)
    (u : Ev) : W4 :=
  psiLP ρ Jbar (pLP χT χN β q, u)

theorem uc_phiLP (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) {χT χN β : ℝ → ℝ} {bT b : ℝ}
    (hχT : IsSlopeWeight χT π bT) (hχN : IsSlopeWeight χN π b) (hβ : IsLeftCutoff β) (n : ℕ) :
    NEM.UC n W4 (phiLP ρ Jbar χT χN β) := by
  obtain ⟨M, hM⟩ := pLP_bdd hχT hχN hβ
  have hc : Continuous (pLP χT χN β) :=
    (((lcut_contDiff 0).continuous.comp continuous_fst).prodMk
      (pLeft_continuous hχT.1.continuous hχN.1.continuous hβ.1.continuous)).prodMk
      (rL_continuous hχT.1.continuous hχN.1.continuous)
  exact NEM.uc_of_comp W4 (psiLP ρ Jbar) (psiLP_contDiff ρ hρ Jbar hJ) (pLP χT χN β) hc
    (closedBall 0 M) (isCompact_closedBall 0 M) (fun q => mem_closedBall_zero_iff.2 (hM q)) n

lemma exp_mul_exp_eq (a b : ℝ) :
    (Real.exp (-a) : ℂ) * (Real.exp b : ℂ) = (Real.exp (b - a) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring

/-- **`-∞` product identity.** -/
theorem left_prod (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (u : Ev)
    (hu : ‖(β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1‖ < ρ / 4) (a3 b3 : ℂ) :
    B4 (phiLP ρ Jbar χT χN β q u) (a3, b3) = lcut 0 q.1 •
      ((Real.exp (-χT q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd)
          ((Real.exp (χT q.1) : ℂ) * a3, (Real.exp (χN q.1) : ℂ) * b3)).1,
      (Real.exp (-χN q.1) : ℂ) * ((Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
        (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd)
          ((Real.exp (χT q.1) : ℂ) * a3, (Real.exp (χN q.1) : ℂ) * b3)).2) := by
  rcases le_or_gt 1 q.1 with hs | hs
  · rw [lcut_eq_zero (show (0 : ℝ) + 1 ≤ q.1 by linarith), zero_smul]
    simp [phiLP, psiLP, pLP, lcut_eq_zero (show (0 : ℝ) + 1 ≤ q.1 by linarith)]
  set A := Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * u.1,
    (β q.1 : ℂ) * u.2.2 + (Real.exp (χN q.1) : ℂ) * u.2.1) - jStd with hA
  have hpsi : psiLeft ρ Jbar (pLeft χT χN β q, u) = A := by
    simp only [psiLeft, pLeft, lcut_eq_one (show q.1 ≤ 1 from hs.le),
      lcut_eq_one (show q.1 ≤ 2 by linarith), Complex.ofReal_one, one_mul, one_smul]
    rw [rtr_eq hρ hu]
  have hr : rL χT χN q = (Real.exp (χT q.1 - χN q.1), Real.exp (χN q.1 - χT q.1)) := by
    simp [rL, lcut_eq_one (show q.1 ≤ 2 by linarith)]
  simp only [phiLP, psiLP, pLP, hpsi, hr, map_smul, ContinuousLinearMap.smul_apply, B4_apply]
  congr 1
  rw [clm_eq_lin A]
  simp only [lin, E4, ev4, ContinuousLinearMap.prod_apply, ContinuousLinearMap.apply_apply,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Complex.real_smul, mul_smul]
  have e1 := exp_mul_exp_eq (χT q.1) (χT q.1)
  have e2 := exp_mul_exp_eq (χN q.1) (χN q.1)
  have e3 := exp_mul_exp_eq (χN q.1) (χT q.1)
  have e4 := exp_mul_exp_eq (χT q.1) (χN q.1)
  rw [sub_self, Real.exp_zero, Complex.ofReal_one] at e1 e2
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.real_smul]
    linear_combination (-1 : ℂ) * (↑a3.re * (A ((1 : ℂ), (0 : ℂ))).1 + ↑a3.im * (A (Complex.I, (0 : ℂ))).1) * e1 -
      (↑b3.re * (A ((0 : ℂ), (1 : ℂ))).1 + ↑b3.im * (A ((0 : ℂ), Complex.I)).1) * e4
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.real_smul]
    linear_combination (-1 : ℂ) * (↑a3.re * (A ((1 : ℂ), (0 : ℂ))).2 + ↑a3.im * (A (Complex.I, (0 : ℂ))).2) * e3 -
      (↑b3.re * (A ((0 : ℂ), (1 : ℂ))).2 + ↑b3.im * (A ((0 : ℂ), Complex.I)).2) * e2

end QN17

end

end FiniteEnergyPlane

/-!
# Q-N, layer 6 (local, NOT published): `qMap 0 = 0` and the derivative of `qMap` at `0`

Decoupled from the smoothness proof: assuming only that `qMap` is differentiable at `0` and that
its components are the `L⁴` classes of the pointwise formula near `0`, the derivative in the
directions `(ζ, 0, 0)` and `(0, 0, ζ)` is identified a.e. through difference quotients along
`r_n = 1/(n+1)` (an `L⁴`-convergent sequence has an a.e.-convergent subsequence).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

namespace QN

/-! ### `ℂ ↔ ℝ²` and `toLpOrZero` -/

lemma vecToC_J₀ (a : Vec 1) :
    vecToC (Matrix.toEuclideanLin (J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Fintype.sum_sum_type]

lemma cToVec_vecToC (a : Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

lemma cToVec_add (a b : ℂ) : cToVec (a + b) = cToVec a + cToVec b := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma cToVec_smul (r : ℝ) (a : ℂ) : cToVec ((r : ℂ) * a) = r • cToVec a := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma cToVec_zero : cToVec 0 = 0 := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma continuous_cToVec : Continuous cToVec := by
  unfold cToVec
  exact (EuclideanSpace.equiv (Fin 1 ⊕ Fin 1) ℝ).symm.continuous.comp
    (continuous_pi fun i => by rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop)

lemma toLpOrZero_eq_toLp {f : ℝ × ℝ → Vec 1} (hf : MemLp f 4 cylMeasure) :
    toLpOrZero f = hf.toLp f := by
  simp [toLpOrZero, hf]

lemma coeFn_toLpOrZero {f : ℝ × ℝ → Vec 1} (hf : MemLp f 4 cylMeasure) :
    (toLpOrZero f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] f := by
  rw [toLpOrZero_eq_toLp hf]; exact hf.coeFn_toLp

lemma toLpOrZero_of_ae_zero {f : ℝ × ℝ → Vec 1} (hf : f =ᵐ[cylMeasure] 0) : toLpOrZero f = 0 := by
  have hm : MemLp f 4 cylMeasure := (MemLp.zero (ε := Vec 1)).ae_eq hf.symm
  rw [toLpOrZero_eq_toLp hm]
  exact (MemLp.toLp_eq_toLp_iff hm MemLp.zero).2 hf |>.trans (MemLp.toLp_zero _)

/-! ### The pointwise formula in terms of values -/

/-- `qPoint` with the nine values `T.i q`, `N.i q` (as complex numbers) and `c` made explicit. -/
def qPt (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (c : ℂ)
    (a1 a2 a3 b1 b2 b3 : ℂ) : ℂ × ℂ :=
  let s := q.1
  let z := cylInf q.1 q.2
  let eT : ℂ := (Real.exp (χT s) : ℂ)
  let eN : ℂ := (Real.exp (χN s) : ℂ)
  let ψ := z + eT * a1
  let ψs := ((2 * π : ℝ) : ℂ) * z + eT * (((deriv χT s : ℝ) : ℂ) * a1 + a2)
  let ψt := ((2 * π : ℝ) : ℂ) * Complex.I * z + eT * a3
  let v := (β s : ℂ) * c + eN * b1
  let vs := ((deriv β s : ℝ) : ℂ) * c + eN * (((deriv χN s : ℝ) : ℂ) * b1 + b2)
  let vt := eN * b3
  let E := (ψs, vs) + Jbar (ψ, v) (ψt, vt)
  ((Real.exp (-χT s) : ℂ) * E.1, (Real.exp (-χN s) : ℂ) * E.2)

lemma qPoint_eq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (x : QDom) (q : ℝ × ℝ) :
    qPoint Jbar χT χN β x q = qPt Jbar χT χN β q x.2.1
      (vecToC ((x.1 : Triple 1 4).1 q)) (vecToC ((x.1 : Triple 1 4).2.1 q))
      (vecToC ((x.1 : Triple 1 4).2.2 q)) (vecToC ((x.2.2 : Triple 1 4).1 q))
      (vecToC ((x.2.2 : Triple 1 4).2.1 q)) (vecToC ((x.2.2 : Triple 1 4).2.2 q)) := rfl

lemma exp_mul_exp_neg (a : ℝ) : (Real.exp (-a) : ℂ) * (Real.exp a : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

lemma jStd_apply (a b : ℂ) : jStd (a, b) = (Complex.I * a, Complex.I * b) := by
  simp [jStd]

/-- Tangential values: `N = 0`, `c = 0`. -/
lemma qPt_tangential (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (a1 a2 a3 : ℂ) :
    qPt Jbar χT χN β q 0 a1 a2 a3 0 0 0 =
      (((deriv χT q.1 : ℝ) : ℂ) * a1 + a2 + Complex.I * a3, 0) := by
  simp only [qPt, mul_zero, add_zero, h0, jStd_apply, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_
  · have := exp_mul_exp_neg (χT q.1)
    linear_combination (((deriv χT q.1 : ℝ) : ℂ) * a1 + a2 + Complex.I * a3) * this +
      (Real.exp (-χT q.1) : ℂ) * ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2 * Complex.I_sq
  · simp

/-! ### The a.e. limit of difference quotients -/

lemma tendsto_rn : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩

/-- If `f : ℝ → L⁴` has derivative `D` at `0`, `f 0 = 0`, and the representatives of
`f (1/(n+1))`, scaled by `n+1`, converge a.e. to `G`, then `D = G` a.e. -/
lemma ae_eq_of_hasDerivAt {f : ℝ → LpCyl 1 4} {D : LpCyl 1 4} (hf : HasDerivAt f D 0)
    (hf0 : f 0 = 0) (g : ℕ → ℝ × ℝ → Vec 1)
    (hg : ∀ n : ℕ, (f (1 / ((n : ℝ) + 1)) : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g n)
    (G : ℝ × ℝ → Vec 1)
    (hG : ∀ᵐ q ∂cylMeasure, Tendsto (fun n : ℕ => ((n : ℝ) + 1) • g n q) atTop (𝓝 (G q))) :
    (D : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] G := by
  have h1 := hf.tendsto_slope_zero_right.comp tendsto_rn
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) • f (1 / ((n : ℝ) + 1))) atTop (𝓝 D) := by
    refine h1.congr fun n => ?_
    simp only [Function.comp, zero_add, hf0, sub_zero, one_div, inv_inv]
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp h2).exists_seq_tendsto_ae
  have hsm : ∀ n : ℕ, ((((n : ℝ) + 1) • f (1 / ((n : ℝ) + 1)) : LpCyl 1 4) : ℝ × ℝ → Vec 1)
      =ᵐ[cylMeasure] fun q => ((n : ℝ) + 1) • g n q := fun n => by
    filter_upwards [Lp.coeFn_smul ((n : ℝ) + 1) (f (1 / ((n : ℝ) + 1))), hg n] with q h1 h2
    rw [h1, Pi.smul_apply, h2]
  have hall := ae_all_iff.2 hsm
  have hG' : ∀ᵐ q ∂cylMeasure, Tendsto (fun i => ((ns i : ℝ) + 1) • g (ns i) q) atTop
      (𝓝 (G q)) := by
    filter_upwards [hG] with q hq
    exact hq.comp hmono.tendsto_atTop
  have hD : ∀ᵐ q ∂cylMeasure, Tendsto (fun i => ((ns i : ℝ) + 1) • g (ns i) q) atTop
      (𝓝 (D q)) := by
    filter_upwards [hns, hall] with q h1 h2
    exact h1.congr fun i => h2 (ns i)
  exact MeasureTheory.AEEqFun.tendsto_ae_unique hD hG'

/-! ### Values of scaled unknowns -/

lemma vecToC_smul (r : ℝ) (a : Vec 1) : vecToC (r • a) = (r : ℂ) * vecToC a := by
  apply Complex.ext <;> simp [vecToC]

lemma vecToC_add (a b : Vec 1) : vecToC (a + b) = vecToC a + vecToC b := by
  apply Complex.ext <;> simp [vecToC]

/-- The nine values of `r • (A, c, B)`, a.e. -/
lemma qPoint_smul_ae (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ)
    (A B : ↥(W1p 4 1)) (c : ℂ) (r : ℝ) :
    (fun q => qPoint Jbar χT χN β (r • ((A, c, B) : QDom)) q) =ᵐ[cylMeasure] fun q =>
      qPt Jbar χT χN β q (r • c)
        ((r : ℂ) * vecToC ((A : Triple 1 4).1 q)) ((r : ℂ) * vecToC ((A : Triple 1 4).2.1 q))
        ((r : ℂ) * vecToC ((A : Triple 1 4).2.2 q)) ((r : ℂ) * vecToC ((B : Triple 1 4).1 q))
        ((r : ℂ) * vecToC ((B : Triple 1 4).2.1 q)) ((r : ℂ) * vecToC ((B : Triple 1 4).2.2 q)) := by
  have e1 : ((r • A : ↥(W1p 4 1)) : Triple 1 4) = r • (A : Triple 1 4) := Submodule.coe_smul r A
  have e2 : ((r • B : ↥(W1p 4 1)) : Triple 1 4) = r • (B : Triple 1 4) := Submodule.coe_smul r B
  filter_upwards [Lp.coeFn_smul r (A : Triple 1 4).1, Lp.coeFn_smul r (A : Triple 1 4).2.1,
    Lp.coeFn_smul r (A : Triple 1 4).2.2, Lp.coeFn_smul r (B : Triple 1 4).1,
    Lp.coeFn_smul r (B : Triple 1 4).2.1, Lp.coeFn_smul r (B : Triple 1 4).2.2]
    with q h1 h2 h3 h4 h5 h6
  rw [qPoint_eq]
  show qPt Jbar χT χN β q (r • c) (vecToC (((r • A : ↥(W1p 4 1)) : Triple 1 4).1 q))
    (vecToC (((r • A : ↥(W1p 4 1)) : Triple 1 4).2.1 q))
    (vecToC (((r • A : ↥(W1p 4 1)) : Triple 1 4).2.2 q))
    (vecToC (((r • B : ↥(W1p 4 1)) : Triple 1 4).1 q))
    (vecToC (((r • B : ↥(W1p 4 1)) : Triple 1 4).2.1 q))
    (vecToC (((r • B : ↥(W1p 4 1)) : Triple 1 4).2.2 q)) = _
  rw [e1, e2]
  simp only [Prod.smul_fst, Prod.smul_snd]
  rw [h1, h2, h3, h4, h5, h6]
  simp only [Pi.smul_apply, vecToC_smul]

lemma coeFn_zero_triple (i : Fin 3) :
    (((0 : ↥(W1p 4 1)) : Triple 1 4).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 ∧
    (((0 : ↥(W1p 4 1)) : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 ∧
    (((0 : ↥(W1p 4 1)) : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 :=
  ⟨Lp.coeFn_zero _ _ _, Lp.coeFn_zero _ _ _, Lp.coeFn_zero _ _ _⟩

lemma toEL_smul_one' (c : ℝ) (v : Vec 1) :
    Matrix.toEuclideanLin (c • (1 : Mat 1)) v = c • v := by
  simp

lemma toEL_add_smul_one' (A : Mat 1) (c : ℝ) (y : Vec 1) :
    Matrix.toEuclideanLin (A + c • (1 : Mat 1)) y = Matrix.toEuclideanLin A y + c • y := by
  rw [map_add, LinearMap.add_apply, toEL_smul_one']

lemma vecToC_crApply_slope (χ : ℝ → ℝ) (w : Triple 1 4) (q : ℝ × ℝ) :
    vecToC (crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w q) =
      ((deriv χ q.1 : ℝ) : ℂ) * vecToC (w.1 q) + vecToC (w.2.1 q) +
        Complex.I * vecToC (w.2.2 q) := by
  simp only [crApply, vecToC_add, vecToC_J₀, toEL_smul_one', vecToC_smul]
  ring

lemma vecToC_crApply_normal (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χ : ℝ → ℝ) (w : Triple 1 4)
    (q : ℝ × ℝ) :
    vecToC (crApply (fun x => normalCoeff Jbar x + deriv χ x.1 • (1 : Mat 1)) w q) =
      ((deriv χ q.1 : ℝ) : ℂ) * vecToC (w.1 q) + vecToC (w.2.1 q) +
        Complex.I * vecToC (w.2.2 q) + QS.tN Jbar (cylInf q.1 q.2) (vecToC (w.1 q)) := by
  simp only [crApply, toEL_add_smul_one', vecToC_add, vecToC_J₀, vecToC_smul,
    QS.normalCoeff_eq, QS.vecToC_cMat]
  ring

end QN

namespace QN18

/-! ### `ℂ → ℝ²` as a continuous linear map -/

/-- `vecToC` as a continuous linear map. -/
def vL : Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun a b => by apply Complex.ext <;> simp [vecToC]
      map_smul' := fun c a => by apply Complex.ext <;> simp [vecToC] }

@[simp] lemma vL_apply (a : Vec 1) : vL a = vecToC a := rfl

/-- `cToVec` as a continuous linear map. -/
def cL : ℂ →L[ℝ] Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := QN.cToVec_add
      map_smul' := fun r a => by
        have := QN.cToVec_smul r a
        simpa [Complex.real_smul] using this }

@[simp] lemma cL_apply (a : ℂ) : cL a = cToVec a := rfl

end QN18

end

end FiniteEnergyPlane

/-!
# Q-N, layer 18 (local, NOT published): the pointwise split of `qPt` and global bounds

`qPt = Lin + W·A(2πiz, 0) + W·A(eT a3, eN b3)` with `A = Jbar(ψ, v) - jStd`, the partition
`lcut 0 + smoothTransition = 1`, the left zero-order recombination, and the bounded coefficients
used by the assembly.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

namespace QN18

open QN

/-- `A = Jbar(ψ, v) - jStd` at the values `(c, a1, b1)`. -/
def Aq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (c a1 b1 : ℂ) :
    ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * a1,
    (β q.1 : ℂ) * c + (Real.exp (χN q.1) : ℂ) * b1) - jStd

/-- The weight `W = diag(e^{-χT}, e^{-χN})`. -/
def wt (χT χN : ℝ → ℝ) (s : ℝ) (X : ℂ × ℂ) : ℂ × ℂ :=
  ((Real.exp (-χT s) : ℂ) * X.1, (Real.exp (-χN s) : ℂ) * X.2)

/-- `X0 = (2πi z, 0)`. -/
def X0 (q : ℝ × ℝ) : ℂ × ℂ := (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0)

/-- `X1 = (eT a3, eN b3)`. -/
def X1 (χT χN : ℝ → ℝ) (q : ℝ × ℝ) (a3 b3 : ℂ) : ℂ × ℂ :=
  ((Real.exp (χT q.1) : ℂ) * a3, (Real.exp (χN q.1) : ℂ) * b3)

/-- The linear part. -/
def linPt (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (c a1 a2 a3 b1 b2 b3 : ℂ) : ℂ × ℂ :=
  (((deriv χT q.1 : ℝ) : ℂ) * a1 + a2 + Complex.I * a3,
    (Real.exp (-χN q.1) : ℂ) * ((deriv β q.1 : ℝ) : ℂ) * c + ((deriv χN q.1 : ℝ) : ℂ) * b1 + b2 +
      Complex.I * b3)

/-- **Exact split of the pointwise formula.** -/
theorem qPt_split (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ)
    (c a1 a2 a3 b1 b2 b3 : ℂ) :
    qPt Jbar χT χN β q c a1 a2 a3 b1 b2 b3 = linPt χT χN β q c a1 a2 a3 b1 b2 b3 +
      wt χT χN q.1 (Aq Jbar χT χN β q c a1 b1 (X0 q)) +
      wt χT χN q.1 (Aq Jbar χT χN β q c a1 b1 (X1 χT χN q a3 b3)) := by
  have hJ : Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * a1,
      (β q.1 : ℂ) * c + (Real.exp (χN q.1) : ℂ) * b1) = Aq Jbar χT χN β q c a1 b1 + jStd := by
    simp [Aq]
  have hX : ((((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * a3,
      (Real.exp (χN q.1) : ℂ) * b3) : ℂ × ℂ) = X0 q + X1 χT χN q a3 b3 := by
    simp [X0, X1]
  have hT := exp_mul_exp_neg (χT q.1)
  have hN := exp_mul_exp_neg (χN q.1)
  simp only [qPt]
  rw [hJ, ContinuousLinearMap.add_apply, hX, map_add, map_add]
  simp only [X0, X1, jStd_apply, wt, linPt, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]
  refine Prod.ext ?_ ?_
  · simp only
    linear_combination (((deriv χT q.1 : ℝ) : ℂ) * a1 + a2 + Complex.I * a3) * hT +
      (Real.exp (-χT q.1) : ℂ) * ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2 * Complex.I_sq
  · simp only
    linear_combination (((deriv χN q.1 : ℝ) : ℂ) * b1 + b2 + Complex.I * b3) * hN

/-! ### The partition and the left zero-order recombination -/

lemma lcut_add_st (s : ℝ) : lcut 0 s + Real.smoothTransition s = 1 := by
  simp [lcut]

lemma split_one (s : ℝ) (Y : ℂ × ℂ) : Y = lcut 0 s • Y + Real.smoothTransition s • Y := by
  rw [← add_smul, lcut_add_st, one_smul]

/-- The diagonal real multiplier `(r, X) ↦ (r.1 X.1, r.2 X.2)`. -/
def Bd : (ℝ × ℝ) →L[ℝ] (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ)) ≃ₗ[ℝ] ((ℂ × ℂ) →L[ℝ] (ℂ × ℂ))).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun (r : ℝ × ℝ) (X : ℂ × ℂ) => ((r.1 • X.1, r.2 • X.2) : ℂ × ℂ))
        (fun r r' X => by simp only [Prod.fst_add, Prod.snd_add, add_smul, Prod.mk_add_mk])
        (fun a r X => by simp only [Prod.smul_fst, Prod.smul_snd, smul_assoc, Prod.smul_mk])
        (fun r X X' => by simp only [Prod.fst_add, Prod.snd_add, smul_add, Prod.mk_add_mk])
        (fun a r X => by
          simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_comm r.1 a, smul_comm r.2 a]))

@[simp] lemma Bd_apply (r : ℝ × ℝ) (X : ℂ × ℂ) : Bd r X = ((r.1 • X.1, r.2 • X.2) : ℂ × ℂ) := rfl

/-- The fixed multiplier of the first component of the left zero-order term. -/
def gL (χT χN : ℝ → ℝ) (s : ℝ) : ℝ := lcut 1 s * Real.exp (χN s - χT s)

lemma left_zero_recomb (χT χN : ℝ → ℝ) (s : ℝ) (Y : ℂ × ℂ) :
    Bd (gL χT χN s, 1) ((lcut 0 s * Real.exp (-χN s)) • Y) = lcut 0 s • wt χT χN s Y := by
  have key : gL χT χN s * (lcut 0 s * Real.exp (-χN s)) = lcut 0 s * Real.exp (-χT s) := by
    unfold gL
    rcases le_or_gt s 1 with hs | hs
    · rw [lcut_eq_one hs, one_mul, mul_left_comm, ← Real.exp_add]
      congr 2; ring
    · rw [lcut_eq_zero (show (0 : ℝ) + 1 ≤ s by linarith)]; ring
  simp only [Bd_apply, Prod.smul_fst, Prod.smul_snd, wt, smul_smul, one_mul, key]
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_one] <;> ring

/-! ### Bounds -/

lemma bdd_mid (g : ℝ → ℝ) (hg : Continuous g) (D : ℝ) (h : ∀ s, (s ≤ -1 ∨ 1 ≤ s) → |g s| ≤ D) :
    ∃ M, 0 ≤ M ∧ ∀ s, |g s| ≤ M := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (max B D) 0, le_max_right _ _, fun s => ?_⟩
  rcases le_or_gt s (-1) with h1 | h1
  · exact (h s (Or.inl h1)).trans ((le_max_right _ _).trans (le_max_left _ _))
  rcases le_or_gt 1 s with h2 | h2
  · exact (h s (Or.inr h2)).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hB s ⟨h1.le, h2.le⟩).trans ((le_max_left _ _).trans (le_max_left _ _))

lemma expN_bdd {χN : ℝ → ℝ} {δ : ℝ} (hδ : δ < 0) (hχN : IsSlopeWeight χN π δ) :
    ∃ M, 0 ≤ M ∧ ∀ s, |Real.exp (χN s)| ≤ M := by
  refine bdd_mid _ (Real.continuous_exp.comp hχN.1.continuous)
    (max (Real.exp (χN (-1))) (Real.exp (χN 1))) fun s hs => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  rcases hs with hs | hs
  · exact (exp_le_left hχN hs).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [hχN.eq_right hs]
    exact Real.exp_le_exp.2 (by nlinarith)

lemma beta_bdd {β : ℝ → ℝ} (hβ : IsLeftCutoff β) : ∃ M, 0 ≤ M ∧ ∀ s, |β s| ≤ M := by
  refine bdd_mid _ hβ.1.continuous 1 fun s hs => ?_
  rcases hs with hs | hs
  · rw [hβ.2.1 s hs]; simp
  · rw [hβ.2.2 s (by linarith)]; simp

lemma deriv_bdd {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) :
    ∃ M, 0 ≤ M ∧ ∀ s, |deriv χ s| ≤ M := by
  refine bdd_mid _ (hχ.1.continuous_deriv (by simp)) (max |a| |b|) fun s hs => ?_
  rcases hs with hs | hs
  · rw [hχ.2.1 s hs]; exact le_max_left _ _
  · rw [hχ.2.2 s hs]; exact le_max_right _ _

lemma gL_continuous {χT χN : ℝ → ℝ} (hT : Continuous χT) (hN : Continuous χN) :
    Continuous (gL χT χN) :=
  (lcut_contDiff 1).continuous.mul (Real.continuous_exp.comp (hN.sub hT))

lemma gL_bdd {χT χN : ℝ → ℝ} {bT b : ℝ} (hχT : IsSlopeWeight χT π bT)
    (hχN : IsSlopeWeight χN π b) : ∃ M, 0 ≤ M ∧ ∀ s, |gL χT χN s| ≤ M := by
  refine bdd_of_left_bdd _ (gL_continuous hχT.1.continuous hχN.1.continuous) 2
    (Real.exp (χN (-1) - χT (-1))) (fun s hs => ?_) (fun s hs => ?_)
  · simp [gL, lcut_eq_zero (show (1 : ℝ) + 1 ≤ s by linarith)]
  · unfold gL
    rw [lcut_eq_one (show s ≤ 1 by linarith), one_mul, hχN.eq_left hs, hχT.eq_left hs,
      abs_of_pos (Real.exp_pos _)]
    exact le_of_eq (by congr 1; ring)

end QN18

end

end FiniteEnergyPlane

/-!
# Q-N, layer 20 (local, NOT published): the `L⁴` factors and the linear part

Component selectors `QDom →L LpCyl 1 4`, their complex pairs in `L⁴(ℂ × ℂ)`, and the linear part
`Lin x = (χT' a1 + a2 + i a3, e^{-χN} β' c + χN' b1 + b2 + i b3)` as a continuous linear map.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal BoundedContinuousFunction

noncomputable section

namespace QN20

open QN QN18

abbrev LC2 := Lp (ℂ × ℂ) 4 cylMeasure

/-! ### Selectors and factors -/

def sT : QDom →L[ℝ] Triple 1 4 := (W1p 4 1).subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)

def sN : QDom →L[ℝ] Triple 1 4 :=
  (W1p 4 1).subtypeL.comp ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

def sC : QDom →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def c1 : Triple 1 4 →L[ℝ] LpCyl 1 4 := ContinuousLinearMap.fst ℝ _ _

def c2 : Triple 1 4 →L[ℝ] LpCyl 1 4 :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def c3 : Triple 1 4 →L[ℝ] LpCyl 1 4 :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

lemma sT_apply (x : QDom) : sT x = (x.1 : Triple 1 4) := rfl
lemma sN_apply (x : QDom) : sN x = (x.2.2 : Triple 1 4) := rfl
lemma sC_apply (x : QDom) : sC x = x.2.1 := rfl
lemma c1_apply (w : Triple 1 4) : c1 w = w.1 := rfl
lemma c2_apply (w : Triple 1 4) : c2 w = w.2.1 := rfl
lemma c3_apply (w : Triple 1 4) : c3 w = w.2.2 := rfl

/-- A complex factor `vecToC ∘ c (s x)` in `L⁴(ℂ)`. -/
def fac (c : Triple 1 4 →L[ℝ] LpCyl 1 4) (s : QDom →L[ℝ] Triple 1 4) :
    QDom →L[ℝ] Lp ℂ 4 cylMeasure :=
  (vL.compLpL 4 cylMeasure).comp (c.comp s)

lemma fac_ae (c : Triple 1 4 →L[ℝ] LpCyl 1 4) (s : QDom →L[ℝ] Triple 1 4) (x : QDom) :
    (fac c s x : ℝ × ℝ → ℂ) =ᵐ[cylMeasure] fun q => vecToC ((c (s x) : ℝ × ℝ → Vec 1) q) :=
  vL.coeFn_compLpL (c (s x))

/-- The pair `(vecToC ∘ ci T, vecToC ∘ cj N)` in `L⁴(ℂ × ℂ)`. -/
def pr (ci cj : Triple 1 4 →L[ℝ] LpCyl 1 4) : QDom →L[ℝ] LC2 :=
  (((ContinuousLinearMap.inl ℝ ℂ ℂ).comp vL).compLpL 4 cylMeasure).comp (ci.comp sT) +
    (((ContinuousLinearMap.inr ℝ ℂ ℂ).comp vL).compLpL 4 cylMeasure).comp (cj.comp sN)

lemma pr_ae (ci cj : Triple 1 4 →L[ℝ] LpCyl 1 4) (x : QDom) :
    (pr ci cj x : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q =>
      (vecToC ((ci (sT x) : ℝ × ℝ → Vec 1) q), vecToC ((cj (sN x) : ℝ × ℝ → Vec 1) q)) := by
  have h := Lp.coeFn_add
    ((((ContinuousLinearMap.inl ℝ ℂ ℂ).comp vL).compLpL 4 cylMeasure) (ci (sT x)))
    ((((ContinuousLinearMap.inr ℝ ℂ ℂ).comp vL).compLpL 4 cylMeasure) (cj (sN x)))
  filter_upwards [h, ((ContinuousLinearMap.inl ℝ ℂ ℂ).comp vL).coeFn_compLpL (ci (sT x)),
    ((ContinuousLinearMap.inr ℝ ℂ ℂ).comp vL).coeFn_compLpL (cj (sN x))] with q h1 h2 h3
  simp only [pr, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply] at h1 ⊢
  rw [h1, Pi.add_apply, h2, h3]
  simp

/-! ### The fixed coefficients -/

/-- `q ↦ (χT'(s), χN'(s))` as a bounded continuous function. -/
def fD {χT χN : ℝ → ℝ} {aT bT aN bN : ℝ} (hT : IsSlopeWeight χT aT bT)
    (hN : IsSlopeWeight χN aN bN) : ℝ × ℝ →ᵇ ℝ × ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun q => (deriv χT q.1, deriv χN q.1))
    (((hT.1.continuous_deriv (by simp)).comp continuous_fst).prodMk
      ((hN.1.continuous_deriv (by simp)).comp continuous_fst))
    (max (Classical.choose (deriv_bdd hT)) (Classical.choose (deriv_bdd hN)))
    (fun q => norm_prod_le_iff.2 ⟨by
      rw [Real.norm_eq_abs]
      exact ((Classical.choose_spec (deriv_bdd hT)).2 q.1).trans (le_max_left _ _), by
      rw [Real.norm_eq_abs]
      exact ((Classical.choose_spec (deriv_bdd hN)).2 q.1).trans (le_max_right _ _)⟩)

lemma fD_apply {χT χN : ℝ → ℝ} {aT bT aN bN : ℝ} (hT : IsSlopeWeight χT aT bT)
    (hN : IsSlopeWeight χN aN bN) (q : ℝ × ℝ) : fD hT hN q = (deriv χT q.1, deriv χN q.1) := rfl

lemma deriv_beta_zero {β : ℝ → ℝ} (hβ : IsLeftCutoff β) {s : ℝ} (hs : s < -1 ∨ 0 < s) :
    deriv β s = 0 := by
  rcases hs with hs | hs
  · have : β =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with y hy using hβ.2.1 y (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]
  · have : β =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with y hy using hβ.2.2 y (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]

/-- `e^{-χN} β'`. -/
def gB (χN β : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (-χN s) * deriv β s

lemma gB_continuous {χN β : ℝ → ℝ} {δ : ℝ} (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β) :
    Continuous (gB χN β) :=
  (Real.continuous_exp.comp hχN.1.continuous.neg).mul (hβ.1.continuous_deriv (by simp))

/-- The fixed `L⁴` function `(0, e^{-χN} β')`. -/
def mB (χN β : ℝ → ℝ) (q : ℝ × ℝ) : ℂ × ℂ := (0, ((gB χN β q.1 : ℝ) : ℂ))

lemma mB_memLp {χN β : ℝ → ℝ} {δ : ℝ} (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β) :
    MemLp (mB χN β) 4 cylMeasure := by
  have hg := gB_continuous hχN hβ
  obtain ⟨C, hC⟩ := exp_bound_of_left (gB χN β) hg π Real.pi_pos 1
    (|gB χN β (-1)| * Real.exp π) (fun s hs => by
      simp [gB, deriv_beta_zero hβ (Or.inr (by linarith : (0 : ℝ) < s))])
    (fun s hs => by
      rcases hs.lt_or_eq with hs | rfl
      · rw [show gB χN β s = 0 by simp [gB, deriv_beta_zero hβ (Or.inl hs)], abs_zero]
        positivity
      · rw [mul_assoc, ← Real.exp_add, show π + π * (-1) = 0 by ring, Real.exp_zero, mul_one])
  have hcont : Continuous (mB χN β) :=
    continuous_const.prodMk (Complex.continuous_ofReal.comp (hg.comp continuous_fst))
  refine memLp_four_of_exp_bound (mB χN β) hcont.aestronglyMeasurable C π Real.pi_pos
    (fun s t => ?_)
  have := hC s
  simpa [mB, Complex.norm_real, Real.norm_eq_abs] using this

/-! ### The linear part -/

/-- **The linear part.** -/
def Lin {χT χN β : ℝ → ℝ} {aT bT aN bN δ : ℝ} (hT : IsSlopeWeight χT aT bT)
    (hN : IsSlopeWeight χN aN bN) (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β) :
    QDom →L[ℝ] LC2 :=
  ((NEM.mulLp (μ := cylMeasure) (p := 4) Bd (fD hT hN)).comp (pr c1 c1) + pr c2 c2 +
      (jStd.compLpL 4 cylMeasure).comp (pr c3 c3)) +
    ((Complex.reCLM.smulRight ((mB_memLp hχN hβ).toLp _)).comp sC +
      (Complex.imCLM.smulRight (jStd.compLpL 4 cylMeasure ((mB_memLp hχN hβ).toLp _))).comp sC)

theorem Lin_ae {χT χN β : ℝ → ℝ} {aT bT aN bN δ : ℝ} (hT : IsSlopeWeight χT aT bT)
    (hN : IsSlopeWeight χN aN bN) (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β) (x : QDom) :
    (Lin hT hN hχN hβ x : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q =>
      linPt χT χN β q x.2.1 (vecToC ((x.1 : Triple 1 4).1 q)) (vecToC ((x.1 : Triple 1 4).2.1 q))
        (vecToC ((x.1 : Triple 1 4).2.2 q)) (vecToC ((x.2.2 : Triple 1 4).1 q))
        (vecToC ((x.2.2 : Triple 1 4).2.1 q)) (vecToC ((x.2.2 : Triple 1 4).2.2 q)) := by
  let M := (mB_memLp hχN hβ).toLp (mB χN β)
  let P1 := pr c1 c1 x
  let P2 := pr c2 c2 x
  let P3 := pr c3 c3 x
  let A1 := NEM.mulLp (μ := cylMeasure) (p := 4) Bd (fD hT hN) P1
  let A3 := jStd.compLpL 4 cylMeasure P3
  let JM := jStd.compLpL 4 cylMeasure M
  have hL : Lin hT hN hχN hβ x = (A1 + P2 + A3) + (x.2.1.re • M + x.2.1.im • JM) := rfl
  rw [hL]
  have f7 : (A1 : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q => Bd (fD hT hN q) (P1 q) :=
    NEM.coeFn_mulLp (μ := cylMeasure) (p := 4) Bd (fD hT hN) P1
  have f11 : (A3 : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q => jStd (P3 q) := jStd.coeFn_compLpL P3
  have f12 : (JM : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q => jStd (M q) := jStd.coeFn_compLpL M
  have f13 : (M : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] mB χN β := (mB_memLp hχN hβ).coeFn_toLp
  have f8 : (P1 : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] _ := pr_ae c1 c1 x
  have f9 : (P2 : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] _ := pr_ae c2 c2 x
  have f10 : (P3 : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] _ := pr_ae c3 c3 x
  clear_value JM A3 A1 M P1 P2 P3
  filter_upwards [Lp.coeFn_add (A1 + P2 + A3) (x.2.1.re • M + x.2.1.im • JM),
    Lp.coeFn_add (A1 + P2) A3, Lp.coeFn_add A1 P2,
    Lp.coeFn_add (x.2.1.re • M) (x.2.1.im • JM), Lp.coeFn_smul x.2.1.re M,
    Lp.coeFn_smul x.2.1.im JM, f7, f8, f9, f10, f11, f12, f13]
    with q e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
  simp only [e1, Pi.add_apply, e2, e3, e4, e5, e6, Pi.smul_apply, e7, e11, e12, e13, e8, e9, e10]
  simp only [sT_apply, sN_apply, c1_apply, c2_apply, c3_apply, fD_apply, Bd_apply, mB, jStd_apply,
    linPt, gB]
  have hc := Complex.re_add_im x.2.1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.real_smul, mul_zero, add_zero]
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.real_smul, Complex.ofReal_mul]
    linear_combination (↑(Real.exp (-χN q.1)) * ↑(deriv β q.1) : ℂ) * hc

end QN20

end

end FiniteEnergyPlane

/-!
# Q-N, layer 21 (local, NOT published): the pieces of `exists_smooth_rep`

`G x = Lin x + LZ x + RZ x + RP x + LP x ∈ L⁴(ℂ × ℂ)`, with the four Nemytskii terms evaluated at the
value map `U x`, and `F x = (cToVec ∘ (G x).1, cToVec ∘ (G x).2)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal BoundedContinuousFunction

noncomputable section

namespace QN21

open QN QN18 QN19 QN20

/-! ### The pointwise recombination -/

theorem sum_eq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ)
    (c a1 a2 a3 b1 b2 b3 : ℂ) (L Z0 R0 RP LP : ℂ × ℂ)
    (hL : L = linPt χT χN β q c a1 a2 a3 b1 b2 b3)
    (hZ : Z0 = Bd (gL χT χN q.1, 1)
      ((lcut 0 q.1 * Real.exp (-χN q.1)) • Aq Jbar χT χN β q c a1 b1 (X0 q)))
    (hR : R0 = Real.smoothTransition q.1 • wt χT χN q.1 (Aq Jbar χT χN β q c a1 b1 (X0 q)))
    (hRP : RP = Real.smoothTransition q.1 •
      wt χT χN q.1 (Aq Jbar χT χN β q c a1 b1 (X1 χT χN q a3 b3)))
    (hLP : LP = lcut 0 q.1 • wt χT χN q.1 (Aq Jbar χT χN β q c a1 b1 (X1 χT χN q a3 b3))) :
    L + Z0 + R0 + RP + LP = qPt Jbar χT χN β q c a1 a2 a3 b1 b2 b3 := by
  rw [qPt_split, hL, hZ, hR, hRP, hLP, left_zero_recomb]
  conv_rhs => rw [split_one q.1 (wt χT χN q.1 (Aq Jbar χT χN β q c a1 b1 (X0 q))),
    split_one q.1 (wt χT χN q.1 (Aq Jbar χT χN β q c a1 b1 (X1 χT χN q a3 b3)))]
  abel

/-! ### Smallness -/

set_option maxHeartbeats 1000000 in
theorem small {ρ : ℝ} (hρ : 0 < ρ) {δ δT : ℝ} (hδ : δ < 0)
    (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    {χT χN β : ℝ → ℝ} (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, ∀ q : ℝ × ℝ,
      ‖(QN15.bR χT χN q).1 * (U x q).1‖ < 1 / 8 ∧
      ‖((QN15.bR χT χN q).2.2.1 : ℂ) * (U x q).2.1‖ < ρ / 8 ∧
      ‖(β q.1 : ℂ) * (U x q).2.2 + (Real.exp (χN q.1) : ℂ) * (U x q).2.1‖ < ρ / 4 := by
  obtain ⟨Mb, hMb⟩ := QN15.bR_bdd hδT hχT hχN
  obtain ⟨Mβ, hMβ0, hMβ⟩ := beta_bdd hβ
  have hE : ∃ M, 0 ≤ M ∧ ∀ s, |Real.exp (χN s)| ≤ M := QN18.expN_bdd hδ hχN
  obtain ⟨ME, hME0, hME⟩ := hE
  generalize hK' : max Mb 0 + Mβ + ME + 1 = K
  have hK : K = max Mb 0 + Mβ + ME + 1 := hK'.symm
  have hK1 : 1 ≤ K := by have := le_max_right Mb 0; rw [hK]; linarith
  have hKp : 0 < K := by linarith
  have hUK := UK_pos
  generalize hm' : min (1 / 8 : ℝ) (ρ / 8) = m
  have hm : m = min (1 / 8 : ℝ) (ρ / 8) := hm'.symm
  have hm0 : 0 < m := by rw [hm]; exact lt_min (by norm_num) (by positivity)
  refine ⟨m / (K * UK), by positivity, fun x hx q => ?_⟩
  have hx' : ‖x‖ < m / (K * UK) := mem_ball_zero_iff.1 hx
  have hu : ‖U x q‖ ≤ UK * ‖x‖ := norm_U_apply_le x q
  generalize U x q = u at hu ⊢
  have hKu : K * ‖u‖ < m := by
    calc K * ‖u‖ ≤ K * (UK * ‖x‖) := mul_le_mul_of_nonneg_left hu hKp.le
      _ < K * (UK * (m / (K * UK))) := by
          refine mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hx' hUK) hKp
      _ = m := by field_simp
  have hu1 : ‖u.1‖ ≤ ‖u‖ := norm_fst_le u
  have hu2 : ‖u.2.1‖ ≤ ‖u‖ := (norm_fst_le u.2).trans (norm_snd_le u)
  have hu3 : ‖u.2.2‖ ≤ ‖u‖ := (norm_snd_le u.2).trans (norm_snd_le u)
  have hb1 : ‖(QN15.bR χT χN q).1‖ ≤ K :=
    (norm_fst_le _).trans ((hMb q).trans (by have := le_max_left Mb 0; rw [hK]; linarith))
  have hb2 : ‖((QN15.bR χT χN q).2.2.1 : ℂ)‖ ≤ K := by
    rw [Complex.norm_real]
    exact (((norm_fst_le _).trans (norm_snd_le _)).trans (norm_snd_le _)).trans
      ((hMb q).trans (by have := le_max_left Mb 0; rw [hK]; linarith))
  have hm1 : m ≤ 1 / 8 := by rw [hm]; exact min_le_left _ _
  have hm2 : m ≤ ρ / 8 := by rw [hm]; exact min_le_right _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul]
    calc _ ≤ K * ‖u‖ := mul_le_mul hb1 hu1 (norm_nonneg _) hKp.le
      _ < 1 / 8 := hKu.trans_le hm1
  · rw [norm_mul]
    calc _ ≤ K * ‖u‖ := mul_le_mul hb2 hu2 (norm_nonneg _) hKp.le
      _ < ρ / 8 := hKu.trans_le hm2
  · have e1 : ‖(β q.1 : ℂ) * u.2.2‖ ≤ Mβ * ‖u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hMβ _) hu3 (norm_nonneg _) hMβ0
    have e2 : ‖(Real.exp (χN q.1) : ℂ) * u.2.1‖ ≤ ME * ‖u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hME _) hu2 (norm_nonneg _) hME0
    calc _ ≤ ‖(β q.1 : ℂ) * u.2.2‖ + ‖(Real.exp (χN q.1) : ℂ) * u.2.1‖ := norm_add_le _ _
      _ ≤ Mβ * ‖u‖ + ME * ‖u‖ := add_le_add e1 e2
      _ ≤ K * ‖u‖ := by
          have := le_max_right Mb 0
          rw [hK]; nlinarith [norm_nonneg u]
      _ < ρ / 4 := hKu.trans_le (hm2.trans (by linarith))

/-! ### The fixed multiplier of the left zero-order term -/

def fG {χT χN : ℝ → ℝ} {bT b : ℝ} (hχT : IsSlopeWeight χT π bT) (hχN : IsSlopeWeight χN π b) :
    ℝ × ℝ →ᵇ ℝ × ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun q => (gL χT χN q.1, (1 : ℝ)))
    (((gL_continuous hχT.1.continuous hχN.1.continuous).comp continuous_fst).prodMk
      continuous_const)
    (max (Classical.choose (gL_bdd hχT hχN)) 1)
    (fun q => norm_prod_le_iff.2 ⟨by
      rw [Real.norm_eq_abs]
      exact ((Classical.choose_spec (gL_bdd hχT hχN)).2 q.1).trans (le_max_left _ _), by
      simp⟩)

lemma fG_apply {χT χN : ℝ → ℝ} {bT b : ℝ} (hχT : IsSlopeWeight χT π bT)
    (hχN : IsSlopeWeight χN π b) (q : ℝ × ℝ) : fG hχT hχN q = (gL χT χN q.1, 1) := rfl

/-! ### The pointwise identity -/

theorem pt_eq (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (χT χN β : ℝ → ℝ) (hβ : IsLeftCutoff β) (q : ℝ × ℝ) (c a1 a2 a3 b1 b2 b3 : ℂ)
    (h1 : ‖(QN15.bR χT χN q).1 * a1‖ < 1 / 8)
    (h2 : ‖((QN15.bR χT χN q).2.2.1 : ℂ) * b1‖ < ρ / 8)
    (h3 : ‖(β q.1 : ℂ) * c + (Real.exp (χN q.1) : ℂ) * b1‖ < ρ / 4)
    (L Z0 R0 RP LP : ℂ × ℂ)
    (hL : L = linPt χT χN β q c a1 a2 a3 b1 b2 b3)
    (hZ : Z0 = Bd (gL χT χN q.1, 1) ((lcut 0 q.1 * Real.exp (-χN q.1)) •
      (Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * a1,
        (β q.1 : ℂ) * c + (Real.exp (χN q.1) : ℂ) * b1) - jStd)
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0)))
    (hR : R0 = QN15.B2 (QN16.phiRZ Jbar ρ χT χN q (a1, b1, c)) b1)
    (hRP : RP = QN15.B4 (QN16.phiRP Jbar ρ χT χN q (a1, b1, c)) (a3, b3))
    (hLP : LP = QN15.B4 (QN17.phiLP ρ Jbar χT χN β q (a1, b1, c)) (a3, b3)) :
    L + Z0 + R0 + RP + LP = qPt Jbar χT χN β q c a1 a2 a3 b1 b2 b3 := by
  refine sum_eq Jbar χT χN β q c a1 a2 a3 b1 b2 b3 L Z0 R0 RP LP hL hZ ?_ ?_ ?_
  · rw [hR]; exact QN16.right_zero Jbar ρ b Jinf Sinf hρ hb hstd χT χN β hβ q (a1, b1, c) h1 h2
  · rw [hRP]
    exact QN16.right_prod Jbar ρ b Jinf Sinf hρ hb hstd χT χN β hβ q (a1, b1, c) h1 h2 a3 b3
  · rw [hLP]; exact QN17.left_prod ρ hρ Jbar χT χN β q (a1, b1, c) h3 a3 b3

/-! ### The four nonlinear terms -/

section Terms

variable (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ)

def tLZ {bT b : ℝ} (hχT : IsSlopeWeight χT π bT) (hχN : IsSlopeWeight χN π b)
    (ΦL : ℝ × ℝ → ℂ × ℂ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ)) (hbL : NEM.IsBaseNem ΦL)
    (mL : Lp ℂ 4 cylMeasure) (x : QDom) : LC2 :=
  NEM.mulLp (μ := cylMeasure) (p := 4) Bd (fG hχT hχN)
    (NEM.mulLp (μ := cylMeasure) (p := 4) bZero (NEM.nem ΦL hbL (U x)) mL)

def tRZ (hb : NEM.IsBaseNem (QN16.phiRZ Jbar ρ χT χN)) (x : QDom) : LC2 :=
  NEM.mulLp (μ := cylMeasure) (p := 4) QN15.B2 (NEM.nem _ hb (U x)) (fac c1 sN x)

def tRP (hb : NEM.IsBaseNem (QN16.phiRP Jbar ρ χT χN)) (x : QDom) : LC2 :=
  NEM.mulLp (μ := cylMeasure) (p := 4) QN15.B4 (NEM.nem _ hb (U x)) (pr c3 c3 x)

def tLP (hb : NEM.IsBaseNem (QN17.phiLP ρ Jbar χT χN β)) (x : QDom) : LC2 :=
  NEM.mulLp (μ := cylMeasure) (p := 4) QN15.B4 (NEM.nem _ hb (U x)) (pr c3 c3 x)

end Terms

lemma ucRZ (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    {δ δT : ℝ} (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    {χT χN : ℝ → ℝ} (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ) :
    ∀ n, NEM.UC n ((ℂ × ℂ) × (ℂ × ℂ)) (QN16.phiRZ Jbar ρ χT χN) := fun n =>
  QN15.uc_psiR ρ b Jbar Jinf Sinf hρ hb hstd QN14.phiRZ0 QN14.contDiff_phiRZ0 (-2) hδT hχT hχN n

lemma ucRP (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    {δ δT : ℝ} (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    {χT χN : ℝ → ℝ} (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ) :
    ∀ n, NEM.UC n QN14.W4 (QN16.phiRP Jbar ρ χT χN) := fun n =>
  QN15.uc_psiR ρ b Jbar Jinf Sinf hρ hb hstd QN14.phiRP0 QN14.contDiff_phiRP0 (-2) hδT hχT hχN n

/-! ### Smoothness of the terms -/

lemma contDiff_tLZ (χT χN : ℝ → ℝ) {bT b : ℝ}
    (hχT : IsSlopeWeight χT π bT) (hχN : IsSlopeWeight χN π b)
    (ΦL : ℝ × ℝ → ℂ × ℂ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ)) (hbL : NEM.IsBaseNem ΦL)
    (mL : Lp ℂ 4 cylMeasure)
    (hcd : ContDiff ℝ ∞ (fun u : ℝ × ℝ →ᵇ ℂ × ℂ × ℂ =>
      NEM.mulLp (μ := cylMeasure) bZero (NEM.nem ΦL hbL u) mL)) :
    ContDiff ℝ ∞ (tLZ χT χN hχT hχN ΦL hbL mL) :=
  (NEM.mulLp (μ := cylMeasure) (p := 4) Bd (fG hχT hχN)).contDiff.comp (hcd.comp U.contDiff)

lemma contDiff_tRZ (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN : ℝ → ℝ)
    (h : ∀ n, NEM.UC n ((ℂ × ℂ) × (ℂ × ℂ)) (QN16.phiRZ Jbar ρ χT χN)) :
    ContDiff ℝ ∞ (tRZ ρ Jbar χT χN (h 0).base) := by
  have := (NEM.contDiff_mulLp_nem (μ := cylMeasure) (p := 4) QN15.B2 (QN16.phiRZ Jbar ρ χT χN) h
    (h 0).base).comp
    (U.contDiff.prodMk (fac c1 sN).contDiff)
  exact this

lemma contDiff_tRP (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN : ℝ → ℝ)
    (h : ∀ n, NEM.UC n QN14.W4 (QN16.phiRP Jbar ρ χT χN)) :
    ContDiff ℝ ∞ (tRP ρ Jbar χT χN (h 0).base) := by
  have := (NEM.contDiff_mulLp_nem (μ := cylMeasure) (p := 4) QN15.B4 (QN16.phiRP Jbar ρ χT χN) h
    (h 0).base).comp
    (U.contDiff.prodMk (pr c3 c3).contDiff)
  exact this

lemma contDiff_tLP (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ)
    (h : ∀ n, NEM.UC n QN14.W4 (QN17.phiLP ρ Jbar χT χN β)) :
    ContDiff ℝ ∞ (tLP ρ Jbar χT χN β (h 0).base) := by
  have := (NEM.contDiff_mulLp_nem (μ := cylMeasure) (p := 4) QN15.B4 (QN17.phiLP ρ Jbar χT χN β) h
    (h 0).base).comp
    (U.contDiff.prodMk (pr c3 c3).contDiff)
  exact this

/-! ### The a.e. values of the terms -/

lemma tLZ_ae (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) {bT b : ℝ}
    (hχT : IsSlopeWeight χT π bT) (hχN : IsSlopeWeight χN π b)
    (ΦL : ℝ × ℝ → ℂ × ℂ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ)) (hbL : NEM.IsBaseNem ΦL)
    (mL : Lp ℂ 4 cylMeasure) (x : QDom)
    (hid : (NEM.mulLp (μ := cylMeasure) bZero (NEM.nem ΦL hbL (U x)) mL : ℝ × ℝ → ℂ × ℂ)
      =ᵐ[cylMeasure] fun q => (lcut 0 q.1 * Real.exp (-χN q.1)) •
        (Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * (U x q).1,
            (β q.1 : ℂ) * (U x q).2.2 + (Real.exp (χN q.1) : ℂ) * (U x q).2.1) - jStd)
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0)) :
    (tLZ χT χN hχT hχN ΦL hbL mL x : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q =>
      Bd (gL χT χN q.1, 1) ((lcut 0 q.1 * Real.exp (-χN q.1)) •
        (Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * (U x q).1,
            (β q.1 : ℂ) * (U x q).2.2 + (Real.exp (χN q.1) : ℂ) * (U x q).2.1) - jStd)
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0)) := by
  filter_upwards [NEM.coeFn_mulLp (μ := cylMeasure) (p := 4) Bd (fG hχT hχN)
    (NEM.mulLp (μ := cylMeasure) (p := 4) bZero (NEM.nem ΦL hbL (U x)) mL), hid] with q e1 e2
  simp only [tLZ, e1, e2, fG_apply]

lemma tRZ_ae (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN : ℝ → ℝ)
    (hb : NEM.IsBaseNem (QN16.phiRZ Jbar ρ χT χN)) (x : QDom) :
    (tRZ ρ Jbar χT χN hb x : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q =>
      QN15.B2 (QN16.phiRZ Jbar ρ χT χN q (U x q)) (vecToC ((x.2.2 : Triple 1 4).1 q)) := by
  filter_upwards [NEM.coeFn_mulLp (μ := cylMeasure) (p := 4) QN15.B2 (NEM.nem _ hb (U x))
    (fac c1 sN x), fac_ae c1 sN x] with q e1 e2
  simp only [tRZ, e1, NEM.nem_apply, e2, c1_apply, sN_apply]

lemma tRP_ae (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN : ℝ → ℝ)
    (hb : NEM.IsBaseNem (QN16.phiRP Jbar ρ χT χN)) (x : QDom) :
    (tRP ρ Jbar χT χN hb x : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q =>
      QN15.B4 (QN16.phiRP Jbar ρ χT χN q (U x q))
        (vecToC ((x.1 : Triple 1 4).2.2 q), vecToC ((x.2.2 : Triple 1 4).2.2 q)) := by
  filter_upwards [NEM.coeFn_mulLp (μ := cylMeasure) (p := 4) QN15.B4 (NEM.nem _ hb (U x))
    (pr c3 c3 x), pr_ae c3 c3 x] with q e1 e2
  simp only [tRP, e1, NEM.nem_apply, e2, c3_apply, sT_apply, sN_apply]

lemma tLP_ae (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ)
    (hb : NEM.IsBaseNem (QN17.phiLP ρ Jbar χT χN β)) (x : QDom) :
    (tLP ρ Jbar χT χN β hb x : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q =>
      QN15.B4 (QN17.phiLP ρ Jbar χT χN β q (U x q))
        (vecToC ((x.1 : Triple 1 4).2.2 q), vecToC ((x.2.2 : Triple 1 4).2.2 q)) := by
  filter_upwards [NEM.coeFn_mulLp (μ := cylMeasure) (p := 4) QN15.B4 (NEM.nem _ hb (U x))
    (pr c3 c3 x), pr_ae c3 c3 x] with q e1 e2
  simp only [tLP, e1, NEM.nem_apply, e2, c3_apply, sT_apply, sN_apply]


end QN21

end

end FiniteEnergyPlane

/-!
# Q-N, layer 22 (local, NOT published): `exists_smooth_rep`

`G x = Lin x + LZ x + RZ x + RP x + LP x ∈ L⁴(ℂ × ℂ)` (layers 18-21), and
`F x = (cToVec ∘ (G x).1, cToVec ∘ (G x).2)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology CauchyRiemannIndex
open scoped ContDiff Real ENNReal BoundedContinuousFunction

noncomputable section

namespace QN22

open QN QN18 QN19 QN20 QN21

/-- The sum of the five terms. -/
def Gm {χT χN β : ℝ → ℝ} {δT δ : ℝ} (ρ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β)
    (ΦL : ℝ × ℝ → ℂ × ℂ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ)) (hbL : NEM.IsBaseNem ΦL)
    (mL : Lp ℂ 4 cylMeasure) (hRZ : NEM.IsBaseNem (QN16.phiRZ Jbar ρ χT χN))
    (hRP : NEM.IsBaseNem (QN16.phiRP Jbar ρ χT χN))
    (hLP : NEM.IsBaseNem (QN17.phiLP ρ Jbar χT χN β)) (x : QDom) : LC2 :=
  Lin hχT hχN hχN hβ x + tLZ χT χN hχT hχN ΦL hbL mL x + tRZ ρ Jbar χT χN hRZ x +
    tRP ρ Jbar χT χN hRP x + tLP ρ Jbar χT χN β hLP x

theorem Gm_ae (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    {χT χN β : ℝ → ℝ} {δT δ : ℝ}
    (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ) (hβ : IsLeftCutoff β)
    (ΦL : ℝ × ℝ → ℂ × ℂ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ)) (hbL : NEM.IsBaseNem ΦL)
    (mL : Lp ℂ 4 cylMeasure) (hRZ : NEM.IsBaseNem (QN16.phiRZ Jbar ρ χT χN))
    (hRP : NEM.IsBaseNem (QN16.phiRP Jbar ρ χT χN))
    (hLP : NEM.IsBaseNem (QN17.phiLP ρ Jbar χT χN β)) (x : QDom)
    (hsm : ∀ q : ℝ × ℝ,
      ‖(QN15.bR χT χN q).1 * (U x q).1‖ < 1 / 8 ∧
      ‖((QN15.bR χT χN q).2.2.1 : ℂ) * (U x q).2.1‖ < ρ / 8 ∧
      ‖(β q.1 : ℂ) * (U x q).2.2 + (Real.exp (χN q.1) : ℂ) * (U x q).2.1‖ < ρ / 4)
    (hid : (NEM.mulLp (μ := cylMeasure) bZero (NEM.nem ΦL hbL (U x)) mL : ℝ × ℝ → ℂ × ℂ)
      =ᵐ[cylMeasure] fun q => (lcut 0 q.1 * Real.exp (-χN q.1)) •
        (Jbar (cylInf q.1 q.2 + (Real.exp (χT q.1) : ℂ) * (U x q).1,
            (β q.1 : ℂ) * (U x q).2.2 + (Real.exp (χN q.1) : ℂ) * (U x q).2.1) - jStd)
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, 0)) :
    (Gm ρ Jbar hχT hχN hβ ΦL hbL mL hRZ hRP hLP x : ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure]
      fun q => qPoint Jbar χT χN β x q := by
  have fL := Lin_ae hχT hχN hχN hβ x
  have fZ := tLZ_ae Jbar χT χN β hχT hχN ΦL hbL mL x hid
  have fRZ := tRZ_ae ρ Jbar χT χN hRZ x
  have fRP := tRP_ae ρ Jbar χT χN hRP x
  have fLP := tLP_ae ρ Jbar χT χN β hLP x
  have a1 := Lp.coeFn_add (Lin hχT hχN hχN hβ x + tLZ χT χN hχT hχN ΦL hbL mL x +
    tRZ ρ Jbar χT χN hRZ x + tRP ρ Jbar χT χN hRP x) (tLP ρ Jbar χT χN β hLP x)
  have a2 := Lp.coeFn_add (Lin hχT hχN hχN hβ x + tLZ χT χN hχT hχN ΦL hbL mL x +
    tRZ ρ Jbar χT χN hRZ x) (tRP ρ Jbar χT χN hRP x)
  have a3 := Lp.coeFn_add (Lin hχT hχN hχN hβ x + tLZ χT χN hχT hχN ΦL hbL mL x)
    (tRZ ρ Jbar χT χN hRZ x)
  have a4 := Lp.coeFn_add (Lin hχT hχN hχN hβ x) (tLZ χT χN hχT hχN ΦL hbL mL x)
  filter_upwards [a1, a2, a3, a4, fL, fZ, fRZ, fRP, fLP, U_ae x]
    with q e1 e2 e3 e4 eL eZ eRZ eRP eLP eU
  obtain ⟨u1, u2, u3⟩ := eU
  have hu : U x q =
      (vecToC ((x.1 : Triple 1 4).1 q), vecToC ((x.2.2 : Triple 1 4).1 q), x.2.1) :=
    Prod.ext u1 (Prod.ext u2 u3)
  obtain ⟨h1, h2, h3⟩ := hsm q
  rw [hu] at h1 h2 h3 eZ eRZ eRP eLP
  simp only [Gm, e1, Pi.add_apply, e2, e3, e4]
  rw [qPoint_eq]
  exact pt_eq ρ b hρ hb Jbar Jinf Sinf hstd χT χN β hβ q _ _ _ _ _ _ _ h1 h2 h3 _ _ _ _ _
    eL eZ eRZ eRP eLP

theorem exists_smooth_rep_proof (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ F : QDom → LpCyl 1 4 × LpCyl 1 4, ContDiff ℝ ∞ F ∧ ∀ x ∈ ball (0 : QDom) ε,
      ((F x).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] (fun q => cToVec (qPoint Jbar χT χN β x q).1) ∧
      ((F x).2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] (fun q => cToVec (qPoint Jbar χT χN β x q).2) := by
  obtain ⟨ΦL, hbL, mL, -, hcdL, hidL⟩ :=
    cTerm_left_shortcut ρ hρ Jbar hstd.1 χT χN β (2 * π + δT) δ hχT hχN hβ
  have hRZ := ucRZ ρ b hρ hb Jbar Jinf Sinf hstd hδT hχT hχN
  have hRP := ucRP ρ b hρ hb Jbar Jinf Sinf hstd hδT hχT hχN
  have hLP : ∀ n, NEM.UC n QN14.W4 (QN17.phiLP ρ Jbar χT χN β) := fun n =>
    QN17.uc_phiLP ρ hρ Jbar hstd.1 hχT hχN hβ n
  obtain ⟨ε, hε, hsm⟩ := small hρ hδ hδT hχT hχN hβ
  have cG : ContDiff ℝ ∞ (Gm ρ Jbar hχT hχN hβ ΦL hbL mL (hRZ 0).base (hRP 0).base (hLP 0).base) :=
    ((((Lin hχT hχN hχN hβ).contDiff.add
      (contDiff_tLZ χT χN hχT hχN ΦL hbL mL hcdL)).add
      (contDiff_tRZ ρ Jbar χT χN hRZ)).add (contDiff_tRP ρ Jbar χT χN hRP)).add
      (contDiff_tLP ρ Jbar χT χN β hLP)
  have hG : ∀ x ∈ ball (0 : QDom) ε,
      (Gm ρ Jbar hχT hχN hβ ΦL hbL mL (hRZ 0).base (hRP 0).base (hLP 0).base x :
        ℝ × ℝ → ℂ × ℂ) =ᵐ[cylMeasure] fun q => qPoint Jbar χT χN β x q := fun x hx =>
    Gm_ae ρ b hρ hb Jbar Jinf Sinf hstd hχT hχN hβ ΦL hbL mL _ _ _ x (hsm x hx)
      (hidL (U x) fun q => (hsm x hx q).2.2)
  generalize Gm ρ Jbar hχT hχN hβ ΦL hbL mL (hRZ 0).base (hRP 0).base (hLP 0).base = G at cG hG
  let o1 : LC2 →L[ℝ] LpCyl 1 4 := (cL.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).compLpL 4 cylMeasure
  let o2 : LC2 →L[ℝ] LpCyl 1 4 := (cL.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)).compLpL 4 cylMeasure
  refine ⟨ε, hε, fun x => (o1 (G x), o2 (G x)),
    (o1.contDiff.comp cG).prodMk (o2.contDiff.comp cG), fun x hx => ⟨?_, ?_⟩⟩
  · filter_upwards [(cL.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).coeFn_compLpL (G x), hG x hx]
      with q e1 e2
    simp only [o1, e1, e2, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', cL_apply]
  · filter_upwards [(cL.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)).coeFn_compLpL (G x), hG x hx]
      with q e1 e2
    simp only [o2, e1, e2, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_snd', cL_apply]

end QN22

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ F : QDom → LpCyl 1 4 × LpCyl 1 4, ContDiff ℝ ∞ F ∧ ∀ x ∈ ball (0 : QDom) ε,
      ((F x).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] (fun q => cToVec (qPoint Jbar χT χN β x q).1) ∧
      ((F x).2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] (fun q => cToVec (qPoint Jbar χT χN β x q).2) :=
  QN22.exists_smooth_rep_proof ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
