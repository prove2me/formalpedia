-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_weakDeriv_mul_eq_swap_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:25.800999+00:00
-- url     : https://prove2.me/submissions/8bd7bbef-d786-48e1-94bf-daec8d7b7d2e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_compact_weak_deriv_approximation_readable

noncomputable section
open MeasureTheory
open scoped ContDiff
section WeakProducts
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
section
private lemma FunctionalInequalities.Analysis.tendsto_integral_mul_of_l2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {u : ℕ → X → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hu : ∀ m, MemLp (u m) 2 μ)
    (hconv : Tendsto (fun m => eLpNorm (u m - b) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, a x * u m x ∂μ) atTop
      (𝓝 (∫ x, a x * b x ∂μ)) := by
  have hp {z : X → ℝ} (hz : MemLp z 2 μ) :
      inner ℝ (ha.toLp a) (hz.toLp z) = ∫ x, a x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hz.coeFn_toLp] with x hx hz'
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, hz']
    exact mul_comm _ _
  have ht :
      Tendsto (fun m => (hu m).toLp (u m)) atTop (𝓝 (hb.toLp b)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu b hb).2 hconv
  have hi :
      Tendsto (fun m => inner ℝ (ha.toLp a) ((hu m).toLp (u m)))
        atTop (𝓝 (inner ℝ (ha.toLp a) (hb.toLp b))) :=
    tendsto_const_nhds.inner ht
  simpa only [hp] using hi
end
end WeakProducts
universe u
section CompactWeakDerivativeTesting
noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
set_option maxHeartbeats 800000 in
/-- Compact rough H1 tests preserve the curl identity of two weak derivatives
of the same scalar function. Supporting interface for Letwin2607.24164v1 (2.6). -/
theorem solution {n : ℕ}
    {f p q η a b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v w : EuclideanSpace ℝ (Fin n)}
    (hp : FunctionalInequalities.Analysis.HasWeakDerivAlong f p v) (hq : FunctionalInequalities.Analysis.HasWeakDerivAlong f q w)
    (hp2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp p 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hq2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp q 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hηv : FunctionalInequalities.Analysis.HasWeakDerivAlong η a v) (hηw : FunctionalInequalities.Analysis.HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, q x * a x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  rcases FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation_readable
      hηv hηw hηc hac hbc ha2 hb2 with
    ⟨S, hS, _hηS, haS, hbS, θ, hθ, hconvv, hconvw⟩

  have hpS : MemLp (S.indicator p) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet).2 (hp2 S hS)

  have hqS : MemLp (S.indicator q) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet).2 (hq2 S hS)

  have hθvS (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x v) ⊆ S :=
    (hθ m).2.2.2.1

  have hθwS (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x w) ⊆ S :=
    (hθ m).2.2.2.2.1

  have hu_v (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x v) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hθ m).2.2.2.2.2.1

  have hu_w (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x w) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hθ m).2.2.2.2.2.2

  have hsmooth :
      ∀ chi : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ chi → HasCompactSupport chi →
          (∫ x, p x * fderiv ℝ chi x w
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            ∫ x, q x * fderiv ℝ chi x v
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro chi hchi hchic
    have hchi2 : ContDiff ℝ (2 : WithTop ℕ∞) chi :=
      hchi.of_le (WithTop.coe_le_coe.mpr le_top)
    have hfd : ContDiff ℝ 1 (fderiv ℝ chi) :=
      hchi2.fderiv_right (by norm_num)
    have hchi_v : ContDiff ℝ 1 (fun x => fderiv ℝ chi x v) :=
      hfd.clm_apply
        (contDiff_const : ContDiff ℝ 1
          (fun _ : EuclideanSpace ℝ (Fin n) => v))
    have hchi_w : ContDiff ℝ 1 (fun x => fderiv ℝ chi x w) :=
      hfd.clm_apply
        (contDiff_const : ContDiff ℝ 1
          (fun _ : EuclideanSpace ℝ (Fin n) => w))
    have hchi_vc : HasCompactSupport (fun x => fderiv ℝ chi x v) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘ fderiv ℝ chi)
      exact (hchic.fderiv ℝ).comp_left (by simp)
    have hchi_wc : HasCompactSupport (fun x => fderiv ℝ chi x w) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L w) ∘ fderiv ℝ chi)
      exact (hchic.fderiv ℝ).comp_left (by simp)
    have hsymm (x : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun y => fderiv ℝ chi y v) x w =
          fderiv ℝ (fun y => fderiv ℝ chi y w) x v := by
      have hfdx : DifferentiableAt ℝ (fderiv ℝ chi) x :=
        (hfd.differentiable (by simp)).differentiableAt
      have hcv :
          DifferentiableAt ℝ
            (fun _ : EuclideanSpace ℝ (Fin n) => v) x :=
        (differentiable_const v : Differentiable ℝ
          (fun _ : EuclideanSpace ℝ (Fin n) => v)).differentiableAt
      have hcw :
          DifferentiableAt ℝ
            (fun _ : EuclideanSpace ℝ (Fin n) => w) x :=
        (differentiable_const w : Differentiable ℝ
          (fun _ : EuclideanSpace ℝ (Fin n) => w)).differentiableAt
      have hv := fderiv_clm_apply hfdx hcv
      have hw := fderiv_clm_apply hfdx hcw
      have hv' := congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L w) hv
      have hw' := congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hw
      simp at hv' hw'
      have hs :=
        second_derivative_symmetric
          (fun y => (hchi2.differentiable (by norm_num) y).hasFDerivAt)
          hfdx.hasFDerivAt w v
      calc
        fderiv ℝ (fun y => fderiv ℝ chi y v) x w =
            ((fderiv ℝ (fderiv ℝ chi) x) w) v := hv'
        _ = ((fderiv ℝ (fderiv ℝ chi) x) v) w := hs
        _ = fderiv ℝ (fun y => fderiv ℝ chi y w) x v := hw'.symm
    have ep := hp.2.2 (fun x => fderiv ℝ chi x w) hchi_w hchi_wc
    have eq := hq.2.2 (fun x => fderiv ℝ chi x v) hchi_v hchi_vc
    have hleft :
        (∫ x, f x * fderiv ℝ (fun y => fderiv ℝ chi y w) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ chi y v) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        congrArg (fun z : ℝ => f x * z) (hsymm x).symm)
    linarith [ep, eq, hleft]

  have hpair (m : ℕ) :
      (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hpind :
        (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx]
        · have hd : fderiv ℝ (θ m) x w = 0 := by
            by_contra hd
            exact hx (hθwS m hd)
          simp only [Set.indicator_of_notMem hx, hd, mul_zero])
    have hqind :
        (∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx]
        · have hd : fderiv ℝ (θ m) x v = 0 := by
            by_contra hd
            exact hx (hθvS m hd)
          simp only [Set.indicator_of_notMem hx, hd, mul_zero])
    calc
      (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hpind
      _ = ∫ x, q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        hsmooth (θ m) (hθ m).1 (hθ m).2.1
      _ = ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hqind.symm

  have ht_p :
      Tendsto
          (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
    FunctionalInequalities.Analysis.tendsto_integral_mul_of_l2
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (a := S.indicator p) (b := b)
      (u := fun m x => fderiv ℝ (θ m) x w)
      hpS hb2 hu_w hconvw

  have ht_q :
      Tendsto
          (fun m => ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
    FunctionalInequalities.Analysis.tendsto_integral_mul_of_l2
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (a := S.indicator q) (b := a)
      (u := fun m x => fderiv ℝ (θ m) x v)
      hqS ha2 hu_v hconvv

  have hseq :
      (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (fun m => ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    funext m
    exact hpair m

  have ht_q' :
      Tendsto
          (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    rw [hseq]
    exact ht_q

  have hind :
      (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    tendsto_nhds_unique ht_p ht_q'

  have hremove_b :
      (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]
      · have hbx : b x = 0 := by
          by_contra hbx
          exact hx (hbS hbx)
        simp only [Set.indicator_of_notMem hx, hbx, mul_zero])

  have hremove_a :
      (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]
      · have hax : a x = 0 := by
          by_contra hax
          exact hx (haS hax)
        simp only [Set.indicator_of_notMem hx, hax, mul_zero])

  calc
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hremove_b.symm
    _ = ∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hind
    _ = ∫ x, q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hremove_a
