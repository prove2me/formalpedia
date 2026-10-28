-- Prove2me | solution 1 for FunctionalInequalities.Analysis.local_taylor_two_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:39.381262+00:00
-- url     : https://prove2.me/submissions/b2838939-a026-4505-a600-c5b122a9d6ca

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12C2TaylorHessianBound
 lemma solution
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ ball x₀ r,
      |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
        (1 / 2 : ℝ) *
          (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀))| ≤
        ε * ‖x - x₀‖ ^ 2 := by
  classical
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ ψ) x₀
  have hsymm :
      ∀ v w : EuclideanSpace ℝ (Fin n), B v w = B w v := by
    intro v w
    exact hψ.isSymmSndFDerivAt (by norm_num) v w
  rcases hψ.contDiffOn (m := 2) le_rfl (by simp) with ⟨u, hu, hψu⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨ρ, hρ, hρu⟩
  let s : Set (EuclideanSpace ℝ (Fin n)) := ball x₀ ρ
  have hs : Convex ℝ s := convex_ball x₀ ρ
  have hx₀s : x₀ ∈ s := mem_ball_self hρ
  have hψs : ContDiffOn ℝ 2 ψ s := hψu.mono hρu
  let q : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => (1 / 2 : ℝ) * B (y - x₀) (y - x₀)
  let g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => ψ y - ψ x₀ - fderiv ℝ ψ x₀ (y - x₀) - q y
  let dg : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun y => fderiv ℝ ψ y - fderiv ℝ ψ x₀ - B (y - x₀)
  have hderiv :
      ∀ y ∈ s, HasFDerivWithinAt g (dg y) s y := by
    intro y hy
    have hy' : ContDiffAt ℝ 2 ψ y :=
      (hψs y hy).contDiffAt (Metric.isOpen_ball.mem_nhds hy)
    have hψy : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
      (hy'.differentiableAt (by norm_num)).hasFDerivAt
    have hsub : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) => z - x₀)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).sub_const x₀
    have hlin :=
      (ContinuousLinearMap.hasFDerivAt (fderiv ℝ ψ x₀)).comp y hsub
    rw [ContinuousLinearMap.comp_id] at hlin
    have hB :=
      (ContinuousLinearMap.hasFDerivAt B).comp y hsub
    rw [ContinuousLinearMap.comp_id] at hB
    have hquad₀ := hB.clm_apply hsub
    simp only [Function.comp_apply] at hquad₀
    have hquad_eq :
        B (y - x₀) ∘SL
              (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) +
            B.flip (y - x₀) =
          2 • B (y - x₀) := by
      ext z
      simp only [ContinuousLinearMap.comp_id, add_apply,
        ContinuousLinearMap.flip_apply, smul_apply]
      rw [hsymm z (y - x₀)]
      ring
    rw [hquad_eq] at hquad₀
    have hq : HasFDerivAt q (B (y - x₀)) y := by
      convert hquad₀.const_mul (1 / 2 : ℝ) using 1 <;>
        first
        | rfl
        | (ext z; norm_num [smul_apply, smul_eq_mul]; ring)
    have hg₀ := ((hψy.sub_const (ψ x₀)).sub hlin).sub hq
    have hg : HasFDerivAt g (dg y) y := by
      convert hg₀ using 1 <;> rfl
    convert hg.hasFDerivWithinAt (s := s) using 1
  have hB₀ :
      (fun y : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ ψ y - fderiv ℝ ψ x₀ - B (y - x₀)) =o[𝓝 x₀]
        fun y => ‖y - x₀‖ := by
    have hfd : HasFDerivAt (fderiv ℝ ψ) B x₀ := by
      exact
        ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)).hasFDerivAt
    simpa [B] using hfd.isLittleO.norm_right
  have hB₀' :
      dg =o[𝓝[s] x₀] fun y => ‖y - x₀‖ := by
    rw [Asymptotics.isLittleO_iff] at hB₀ ⊢
    intro c hc
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (hB₀ hc)
  have hB₀'' :
      dg =o[𝓝[s] x₀] fun y => ‖y - x₀‖ ^ 1 := by
    simpa using hB₀'
  have hg₀ :
      (fun y => g y - g x₀) =o[𝓝[s] x₀]
        fun y => ‖y - x₀‖ ^ (1 + 1) :=
    hs.isLittleO_pow_succ hx₀s hderiv hB₀''
  have hgzero : g x₀ = 0 := by
    simp [g, q]
  have hg₀' :
      g =o[𝓝[s] x₀] fun y => ‖y - x₀‖ ^ 2 := by
    simpa [hgzero, pow_two] using hg₀
  have hev :
      ∀ᶠ y in 𝓝[s] x₀, ‖g y‖ ≤ ε * ‖y - x₀‖ ^ 2 := by
    have h := Asymptotics.IsLittleO.bound hg₀' hε
    filter_upwards [h] with y hy
    calc
      ‖g y‖ ≤ ε * ‖‖y - x₀‖ ^ 2‖ := hy
      _ = ε * ‖y - x₀‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖y - x₀‖))]
  rcases Metric.mem_nhdsWithin_iff.mp hev with ⟨δ, hδ, hδev⟩
  refine ⟨min ρ δ, lt_min hρ hδ, ?_⟩
  intro x hx
  have hx' : dist x x₀ < min ρ δ := Metric.mem_ball.mp hx
  have hxρ : x ∈ s :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hx' (min_le_left ρ δ))
  have hxδ : x ∈ ball x₀ δ :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hx' (min_le_right ρ δ))
  have hbound : ‖g x‖ ≤ ε * ‖x - x₀‖ ^ 2 := by
    have h := hδev ⟨hxδ, hxρ⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖x - x₀‖))] using h
  have hgexpr :
      g x =
        ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
          (1 / 2 : ℝ) *
            (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀)) := by
    simp [g, q, sub_eq_add_neg]
    ring
  rw [hgexpr] at hbound
  simpa only [Real.norm_eq_abs] using hbound
