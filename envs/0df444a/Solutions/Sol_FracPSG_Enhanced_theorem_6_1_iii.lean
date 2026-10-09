-- Prove2me | solution 1 for FracPSG.Enhanced.theorem_6_1_iii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T22:27:10.470555+00:00
-- url     : https://prove2.me/submissions/d2ced0ca-40eb-4eef-a396-0011de2327f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Enhanced_Basic
import Definitions.Def_FracPSG_Enhanced_Algorithm2
import Theorems.Thm_FracPSG_Enhanced_eq_34
import Theorems.Thm_FracPSG_Enhanced_lemma_2_2_i
import Theorems.Thm_FracPSG_Enhanced_theorem_6_1_i
import Theorems.Thm_FracPSG_Enhanced_theorem_6_1_ii

open Filter Topology
open scoped InnerProductSpace Pointwise

set_option autoImplicit false

namespace P2e99

open NonconvexSplitting.Shared FracPSG.Enhanced

/-- Line derivative of a differentiable function. -/
theorem line_hasDerivAt {N : ℕ} {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    {z : EuclideanSpace ℝ (Fin N)} (hd : DifferentiableAt ℝ φ z) (h : EuclideanSpace ℝ (Fin N)) :
    HasDerivAt (fun s : ℝ => φ (z + s • h)) (⟪gradient φ z, h⟫_ℝ) 0 := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ z) (z + (0:ℝ) • h) := by
    simpa using hd.hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => z + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add z
  have h3 := h1.comp_hasDerivAt (0:ℝ) h2
  have : fderiv ℝ φ z h = ⟪gradient φ z, h⟫_ℝ := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← this]
  exact h3

/-- A regular subgradient of a finite max at `z` lies in the convex hull of the gradients
of the pieces indexed by `J`, when the pieces outside `J` are strictly inactive at `z`. -/
theorem regSubgrad_max_mem_hull {N p : ℕ} [NeZero p]
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} (J : Finset (Fin p))
    {z w : EuclideanSpace ℝ (Fin N)}
    (hd : ∀ i ∈ J, DifferentiableAt ℝ (gi i) z)
    (hc : ∀ i ∉ J, ContinuousAt (gi i) z ∧ gi i z < maxFn gi z)
    (hw : IsRegularSubgrad (fun y => ((maxFn gi y : ℝ) : EReal)) z w) :
    w ∈ convexHull ℝ ((fun i => gradient (gi i) z) '' (J : Set (Fin p))) := by
  by_contra hw'
  set K := convexHull ℝ ((fun i => gradient (gi i) z) '' (J : Set (Fin p))) with hK
  have hKc : Convex ℝ K := convex_convexHull ℝ _
  have hKcl : IsClosed K := ((J.finite_toSet.image _).isCompact_convexHull ℝ).isClosed
  obtain ⟨f, u, hfw, hfb⟩ := geometric_hahn_banach_point_closed hKc hKcl hw'
  set h : EuclideanSpace ℝ (Fin N) := -((InnerProductSpace.toDual ℝ _).symm f) with hh
  have hinner : ∀ y, ⟪y, h⟫_ℝ = - f y := by
    intro y
    rw [hh, inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  set a := ⟪w, h⟫_ℝ
  set b := -u
  have hab : b < a := by
    simp only [a, b, hinner]; linarith
  set gap := a - b
  have hgap : 0 < gap := by simp only [gap]; linarith
  have hJ : ∀ i ∈ J, ⟪gradient (gi i) z, h⟫_ℝ < b := by
    intro i hi
    have := hfb _ (subset_convexHull ℝ _ ⟨i, hi, rfl⟩)
    rw [hinner]; simp only [b]; linarith
  -- lower bound from regularity
  set ε := gap / (2 * (‖h‖ + 1))
  have hε : 0 < ε := by positivity
  have hεh : ε * ‖h‖ ≤ gap / 2 := by
    simp only [ε]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg h]
  have hline : Tendsto (fun s : ℝ => z + s • h) (𝓝[>] (0:ℝ)) (𝓝 z) := by
    have : Continuous (fun s : ℝ => z + s • h) := by fun_prop
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hlow : ∀ᶠ s in 𝓝[>] (0:ℝ), maxFn gi z + s * (b + gap / 2) ≤ maxFn gi (z + s • h) := by
    have := hline.eventually (hw.2 ε hε)
    filter_upwards [this, self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    simp only [add_sub_cancel_left] at hs
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hs
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hs
    have : ε * (s * ‖h‖) ≤ s * (gap / 2) := by nlinarith
    simp only [gap] at this ⊢
    nlinarith
  -- upper bound for every piece
  have hup : ∀ i, ∀ᶠ s in 𝓝[>] (0:ℝ), gi i (z + s • h) < maxFn gi z + s * (b + gap / 2) := by
    intro i
    by_cases hi : i ∈ J
    · have hder := (line_hasDerivAt (hd i hi) h).tendsto_slope_zero_right
      have hlt : ⟪gradient (gi i) z, h⟫_ℝ < b + gap / 2 := by linarith [hJ i hi]
      have hev := hder.eventually (gt_mem_nhds hlt)
      filter_upwards [hev, self_mem_nhdsWithin] with s hs hs0
      have hs0 : 0 < s := hs0
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hs
      have hle : gi i z ≤ maxFn gi z :=
        Finset.le_sup' (fun j => gi j z) (Finset.mem_univ i)
      have := (inv_mul_lt_iff₀ hs0).1 hs
      linarith
    · obtain ⟨hci, hlt⟩ := hc i hi
      have hcont : ContinuousAt (fun s : ℝ => gi i (z + s • h) - s * (b + gap / 2)) 0 := by
        have hl : ContinuousAt (fun s : ℝ => z + s • h) 0 := by fun_prop
        have : ContinuousAt (fun s : ℝ => gi i (z + s • h)) 0 := by
          apply ContinuousAt.comp (g := gi i) _ hl
          simpa using hci
        exact this.sub (by fun_prop)
      have ht := hcont.tendsto
      simp only [zero_smul, add_zero, zero_mul, sub_zero] at ht
      have hev := (ht.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).eventually (gt_mem_nhds hlt)
      filter_upwards [hev] with s hs
      linarith
  have hall : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ i, gi i (z + s • h) < maxFn gi z + s * (b + gap / 2) :=
    eventually_all.2 hup
  obtain ⟨s, hs1, hs2⟩ := (hlow.and hall).exists
  have : maxFn gi (z + s • h) < maxFn gi z + s * (b + gap / 2) := by
    unfold maxFn
    rw [Finset.sup'_lt_iff]
    intro i _
    exact hs2 i
  linarith

/-- Limiting subdifferential of a finite max of `C¹` functions is in the hull of the active
gradients. -/
theorem limitingSubdiff_maxFn_subset {N p : ℕ} [NeZero p]
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {O : Set (EuclideanSpace ℝ (Fin N))}
    (hO : IsOpen O) (hC : ∀ i, ContDiffOn ℝ 1 (gi i) O) {xbar : EuclideanSpace ℝ (Fin N)}
    (hx : xbar ∈ O) :
    LimitingSubdiff (fun y => ((maxFn gi y : ℝ) : EReal)) xbar ⊆
      convexHull ℝ ((fun i => gradient (gi i) xbar) '' (activeSet 0 gi xbar : Set (Fin p))) := by
  intro v hv
  obtain ⟨-, xs, vs, hxs, -, hvs, hreg⟩ := hv
  set J := activeSet 0 gi xbar with hJdef
  set K := convexHull ℝ ((fun i => gradient (gi i) xbar) '' (J : Set (Fin p))) with hK
  have hdiff : ∀ i, ∀ z ∈ O, DifferentiableAt ℝ (gi i) z := fun i z hz =>
    ((hC i).differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hz)
  have hgc : ∀ i, ContinuousAt (fun z => gradient (gi i) z) xbar := by
    intro i
    have h1 := ((hC i).continuousOn_fderiv_of_isOpen hO le_rfl).continuousAt (hO.mem_nhds hx)
    have h2 : Continuous (fun L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm L) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous
    exact h2.continuousAt.comp h1
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => gi i xbar)
  have hj0J : j0 ∈ J := by
    simp [hJdef, activeSet, maxFn, hj0]
  have hKne : K.Nonempty := ⟨_, subset_convexHull ℝ _ ⟨j0, hj0J, rfl⟩⟩
  have hKcl : IsClosed K := ((J.finite_toSet.image _).isCompact_convexHull ℝ).isClosed
  -- near xbar: inside O and pieces outside J strictly inactive
  have hnear : ∀ᶠ z in 𝓝 xbar, z ∈ O ∧ ∀ i, i ∉ J → gi i z < maxFn gi z := by
    refine (show ∀ᶠ z in 𝓝 xbar, z ∈ O from hO.mem_nhds hx).and (eventually_all.2 fun i => ?_)
    by_cases hi : i ∈ J
    · exact Eventually.of_forall fun _ h => absurd hi h
    · have hlt : gi i xbar < gi j0 xbar := by
        have : ¬ (maxFn gi xbar - 0 ≤ gi i xbar) := by simpa [hJdef, activeSet] using hi
        simp only [maxFn] at this
        rw [hj0] at this
        linarith
      have hc1 : ContinuousAt (gi i) xbar := (hdiff i xbar hx).continuousAt
      have hc2 : ContinuousAt (gi j0) xbar := (hdiff j0 xbar hx).continuousAt
      have : ∀ᶠ z in 𝓝 xbar, gi i z < gi j0 z :=
        (hc1.prodMk hc2).eventually (isOpen_lt_prod.mem_nhds hlt)
      filter_upwards [this] with z hz _
      exact lt_of_lt_of_le hz (Finset.le_sup' (fun j => gi j z) (Finset.mem_univ j0))
  -- the error term
  set η : EuclideanSpace ℝ (Fin N) → ℝ :=
    fun z => ∑ i, ‖gradient (gi i) z - gradient (gi i) xbar‖ with hη
  have hηt : Tendsto η (𝓝 xbar) (𝓝 0) := by
    have : Tendsto η (𝓝 xbar) (𝓝 (∑ i : Fin p, ‖gradient (gi i) xbar - gradient (gi i) xbar‖)) := by
      apply tendsto_finsetSum
      intro i _
      exact ((hgc i).tendsto.sub tendsto_const_nhds).norm
    simpa using this
  have hmem : ∀ z, z ∈ O → (∀ i, i ∉ J → gi i z < maxFn gi z) → ∀ w,
      IsRegularSubgrad (fun y => ((maxFn gi y : ℝ) : EReal)) z w →
      Metric.infDist w K ≤ η z := by
    intro z hzO hzJ w hw
    have hw' := regSubgrad_max_mem_hull J (fun i _ => hdiff i z hzO)
      (fun i hi => ⟨(hdiff i z hzO).continuousAt, hzJ i hi⟩) hw
    have hsub : convexHull ℝ ((fun i => gradient (gi i) z) '' (J : Set (Fin p))) ⊆
        K + Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) (η z) := by
      apply convexHull_min
      · rintro _ ⟨i, hi, rfl⟩
        refine Set.mem_add.2 ⟨gradient (gi i) xbar, subset_convexHull ℝ _ ⟨i, hi, rfl⟩,
          gradient (gi i) z - gradient (gi i) xbar, ?_, by abel⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact Finset.single_le_sum (f := fun i => ‖gradient (gi i) z - gradient (gi i) xbar‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      · exact (convex_convexHull ℝ _).add (convex_closedBall (0 : EuclideanSpace ℝ (Fin N)) (η z))
    obtain ⟨k, hk, e, he, rfl⟩ := Set.mem_add.1 (hsub hw')
    calc Metric.infDist (k + e) K ≤ dist (k + e) k := Metric.infDist_le_dist_of_mem hk
      _ = ‖e‖ := by rw [dist_eq_norm]; simp
      _ ≤ η z := by simpa [dist_zero_right] using he
  have hev : ∀ᶠ t in atTop, Metric.infDist (vs t) K ≤ η (xs t) := by
    filter_upwards [hxs.eventually hnear] with t ht
    exact hmem (xs t) ht.1 ht.2 (vs t) (hreg t)
  have hlim : Metric.infDist v K ≤ 0 := by
    have h1 : Tendsto (fun t => Metric.infDist (vs t) K) atTop (𝓝 (Metric.infDist v K)) :=
      ((Metric.continuous_infDist_pt K).tendsto v).comp hvs
    exact le_of_tendsto_of_tendsto h1 (hηt.comp hxs) hev
  have : Metric.infDist v K = 0 := le_antisymm hlim Metric.infDist_nonneg
  exact (hKcl.mem_iff_infDist_zero hKne).2 this

end P2e99

namespace P2e99

open NonconvexSplitting.Shared FracPSG.Enhanced

theorem fn_real {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ)
    {y : EuclideanSpace ℝ (Fin N)} (hy : FracPSG.Subseq.objF fs fn y ≠ ⊤) :
    ∃ r : ℝ, fn y = r ∧ FracPSG.Subseq.objF fs fn y = ((fs y + r : ℝ) : EReal) ∧
      (FracPSG.Subseq.objF fs fn y).toReal = fs y + r := by
  have h1 : fn y ≠ ⊥ := hA1.fn_proper.1 y
  have h2 : fn y ≠ ⊤ := by
    intro h; apply hy; simp [FracPSG.Subseq.objF, h]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, fn y = r := ⟨_, (EReal.coe_toReal h2 h1).symm⟩
  have h3 : FracPSG.Subseq.objF fs fn y = ((fs y + r : ℝ) : EReal) := by
    unfold FracPSG.Subseq.objF; rw [hr, EReal.coe_add]
  exact ⟨r, hr, h3, by rw [h3, EReal.toReal_coe]⟩

/-- The Step-2 optimality of `x (n+1)` tested against `y = xbar`, in real form. -/
theorem step_upper {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ) (n : ℕ)
    {xbar : EuclideanSpace ℝ (Fin N)} (hxbS : xbar ∈ S)
    (hxbf : FracPSG.Subseq.objF fs fn xbar ≠ ⊤)
    (hyf : FracPSG.Subseq.objF fs fn (x (n + 1)) ≠ ⊤) :
    (FracPSG.Subseq.objF fs fn (x (n + 1))).toReal ≤ (FracPSG.Subseq.objF fs fn xbar).toReal
      + (fs (x (n + 1)) - fs xbar)
      + ⟪gradient fs (FracPSG.Subseq.extrap x κ n), xbar - x (n + 1)⟫_ℝ
      + 1 / (2 * τ n) *
          (‖xbar - FracPSG.Subseq.extrap x μ n - (τ n * FracPSG.Subseq.ratio
              (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) • gradient (gi (ihat n)) (x n)‖ ^ 2
            - ‖x (n + 1) - FracPSG.Subseq.extrap x μ n - (τ n * FracPSG.Subseq.ratio
              (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) • gradient (gi (ihat n)) (x n)‖ ^ 2)
      + ℓ / 2 * (‖xbar - FracPSG.Subseq.extrap x κ n‖ ^ 2
          - ‖x (n + 1) - FracPSG.Subseq.extrap x κ n‖ ^ 2) := by
  have h := hrun.cand_argmin n (ihat n) (hrun.ihat_mem n) xbar hxbS
  rw [← hrun.next_eq n] at h
  obtain ⟨r1, hr1, -, ha⟩ := fn_real hA1 hyf
  obtain ⟨r2, hr2, -, hb⟩ := fn_real hA1 hxbf
  unfold FracPSG.Subseq.subObj at h
  rw [hr1, hr2, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [ha, hb]
  have e : ⟪gradient fs (FracPSG.Subseq.extrap x κ n), xbar - x (n + 1)⟫_ℝ =
      ⟪gradient fs (FracPSG.Subseq.extrap x κ n), xbar - FracPSG.Subseq.extrap x κ n⟫_ℝ -
      ⟪gradient fs (FracPSG.Subseq.extrap x κ n), x (n + 1) - FracPSG.Subseq.extrap x κ n⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  rw [e]
  have e2 : ∀ (a b : ℝ), 1 / (2 * τ n) * (a - b) = 1 / (2 * τ n) * a - 1 / (2 * τ n) * b := by
    intro a b; ring
  rw [e2]
  linarith

theorem T2_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (xb y v gr : E)
    (τ θ T0 δ Θ Γ : ℝ) (hT0 : 0 < T0) (hτ0 : T0 ≤ τ) (hτδ : τ ≤ 1 / δ) (hδ : 0 < δ)
    (hθ : |θ| ≤ Θ) (hgr : ‖gr‖ ≤ Γ) (h1 : ‖xb - v‖ ≤ 1) (h2 : ‖y - v‖ ≤ 1) :
    |1 / (2 * τ) * (‖xb - v - (τ * θ) • gr‖ ^ 2 - ‖y - v - (τ * θ) • gr‖ ^ 2)| ≤
      1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)) * ‖xb - y‖ := by
  have hτ : 0 < τ := lt_of_lt_of_le hT0 hτ0
  set c := (τ * θ) • gr with hcdef
  have hΘ : 0 ≤ Θ := le_trans (abs_nonneg _) hθ
  have hΓ : 0 ≤ Γ := le_trans (norm_nonneg _) hgr
  have hc : ‖c‖ ≤ 1 / δ * Θ * Γ := by
    rw [hcdef, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hτ]
    have := mul_le_mul hτδ hθ (abs_nonneg _) (by positivity)
    exact mul_le_mul this hgr (norm_nonneg _) (by positivity)
  set K := 1 / δ * Θ * Γ
  have ha : ‖xb - v - c‖ ≤ 1 + K := (norm_sub_le _ _).trans (add_le_add h1 hc)
  have hb : ‖y - v - c‖ ≤ 1 + K := (norm_sub_le _ _).trans (add_le_add h2 hc)
  have hab : |‖xb - v - c‖ - ‖y - v - c‖| ≤ ‖xb - y‖ := by
    have := abs_norm_sub_norm_le (xb - v - c) (y - v - c)
    have e : xb - v - c - (y - v - c) = xb - y := by abel
    rwa [e] at this
  have hsq : |‖xb - v - c‖ ^ 2 - ‖y - v - c‖ ^ 2| ≤ ‖xb - y‖ * (2 + 2 * K) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖xb - v - c‖ + ‖y - v - c‖),
      mul_comm]
    exact mul_le_mul hab (by linarith) (by positivity) (norm_nonneg _)
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * τ))]
  have hinv : 1 / (2 * τ) ≤ 1 / (2 * T0) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc 1 / (2 * τ) * |‖xb - v - c‖ ^ 2 - ‖y - v - c‖ ^ 2|
      ≤ 1 / (2 * T0) * (‖xb - y‖ * (2 + 2 * K)) :=
        mul_le_mul hinv hsq (abs_nonneg _) (by positivity)
    _ = 1 / (2 * T0) * (2 + 2 * K) * ‖xb - y‖ := by ring

theorem gradient_continuousAt {N : ℕ} {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    {O : Set (EuclideanSpace ℝ (Fin N))} (hO : IsOpen O) (hC : ContDiffOn ℝ 1 φ O)
    {z : EuclideanSpace ℝ (Fin N)} (hz : z ∈ O) :
    ContinuousAt (fun y => gradient φ y) z := by
  have h1 := (hC.continuousOn_fderiv_of_isOpen hO le_rfl).continuousAt (hO.mem_nhds hz)
  have h2 : Continuous (fun L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ =>
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm L) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous
  exact h2.continuousAt.comp h1

theorem common_open {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {f : EuclideanSpace ℝ (Fin N) → EReal} {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ}
    {β m M : ℝ} (hA2 : Assumption2' S f gi β m M) :
    ∃ O : Set (EuclideanSpace ℝ (Fin N)), IsOpen O ∧ S ⊆ O ∧ ∀ i, ContDiffOn ℝ 1 (gi i) O := by
  choose O hO hSO hC using hA2.contDiff
  exact ⟨⋂ i, O i, isOpen_iInter_of_finite hO, Set.subset_iInter hSO,
    fun i => (hC i).mono (Set.iInter_subset _ i)⟩

/-- Part (3): the limit of the ratios equals the ratio at any cluster point. -/
theorem ratio_limit_eq {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ)
    (hA2 : Assumption2' S (FracPSG.Subseq.objF fs fn) gi β m M)
    (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ)
    (hτ : 0 < Filter.liminf τ atTop)
    (hxn : ∀ n, x n ∈ S ∧ FracPSG.Subseq.objF fs fn (x n) ≠ ⊤)
    {L : ℝ} (hL : Tendsto (fun n => FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n))
      atTop (𝓝 L))
    (hstep : Tendsto (fun n => ‖x (n + 1) - x n‖) atTop (𝓝 0))
    {xbar : EuclideanSpace ℝ (Fin N)} (hcl : MapClusterPt xbar atTop x) (hxbS : xbar ∈ S)
    (hxbf : FracPSG.Subseq.objF fs fn xbar ≠ ⊤)
    (hlsc : LowerSemicontinuous (FracPSG.Subseq.objF fs fn)) :
    L = FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) xbar := by
  set f := FracPSG.Subseq.objF fs fn with hf
  set g := maxFn gi with hg
  have hδ : 0 < δ := hpar.1
  obtain ⟨O, hO, hSO, hCO⟩ := common_open hA2
  have hxbO : xbar ∈ O := hSO hxbS
  have hdiff : ∀ i, DifferentiableAt ℝ (gi i) xbar := fun i =>
    ((hCO i).differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hxbO)
  have hgcont : ContinuousAt g xbar := by
    have := ContinuousAt.finset_sup'_apply (s := Finset.univ) (f := gi) (x := xbar)
      Finset.univ_nonempty (fun i _ => (hdiff i).continuousAt)
    exact this
  have hgradc : ∀ i, ContinuousAt (fun z => gradient (gi i) z) xbar := fun i =>
    gradient_continuousAt hO (hCO i) hxbO
  have hgpos : 0 < g xbar := hA2.g_pos xbar hxbS
  have hτle : ∀ n, τ n ≤ 1 / δ := fun n =>
    (hrun.step_le n).trans (one_div_le_one_div_of_le hδ (le_max_right _ _))
  -- subsequence
  obtain ⟨ψ, hψm, hψt⟩ := hcl.tendsto_subseq
  obtain ⟨nn, hnn1, hnnk⟩ : ∃ nn : ℕ → ℕ, (∀ k, nn k + 1 = ψ (k + 1)) ∧ ∀ k, k ≤ nn k := by
    refine ⟨fun k => ψ (k + 1) - 1, fun k => ?_, fun k => ?_⟩
    · have hle : k + 1 ≤ ψ (k + 1) := hψm.id_le (k + 1)
      show ψ (k + 1) - 1 + 1 = ψ (k + 1)
      omega
    · have hle : k + 1 ≤ ψ (k + 1) := hψm.id_le (k + 1)
      show k ≤ ψ (k + 1) - 1
      omega
  have hnnt : Tendsto nn atTop atTop := tendsto_atTop_mono hnnk tendsto_id
  have hnnt1 : Tendsto (fun k => nn k + 1) atTop atTop := tendsto_add_atTop_nat 1 |>.comp hnnt
  have hy : Tendsto (fun k => x (nn k + 1)) atTop (𝓝 xbar) := by
    have := hψt.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun k => ?_)
    simp [Function.comp, hnn1]
  have hsteps : Tendsto (fun k => x (nn k + 1) - x (nn k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]; exact hstep.comp hnnt
  have hx0 : Tendsto (fun k => x (nn k)) atTop (𝓝 xbar) := by
    have := hy.sub hsteps; simpa using this
  have hprevd : Tendsto (fun n => x n - FracPSG.Subseq.xPrev x n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 := hstep.comp (tendsto_sub_atTop_nat 1)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp, FracPSG.Subseq.xPrev, if_neg (by omega : n ≠ 0),
      Nat.sub_add_cancel hn]
  have hprevk := hprevd.comp hnnt
  have hu : Tendsto (fun k => FracPSG.Subseq.extrap x κ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => κ (nn k) • (x (nn k) - FracPSG.Subseq.xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => κbar * ‖x (nn k) - FracPSG.Subseq.xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.kappa_mem (nn k)).1]
        exact mul_le_mul_of_nonneg_right (hrun.kappa_mem (nn k)).2 (norm_nonneg _)
      · simpa using (hprevk.norm).const_mul κbar
    have := hx0.add hz
    simpa [FracPSG.Subseq.extrap] using this
  have hv : Tendsto (fun k => FracPSG.Subseq.extrap x μ (nn k)) atTop (𝓝 xbar) := by
    have hz : Tendsto (fun k => μ (nn k) • (x (nn k) - FracPSG.Subseq.xPrev x (nn k))) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm
        (a := fun k => (μbar * (1 / δ)) * ‖x (nn k) - FracPSG.Subseq.xPrev x (nn k)‖)
        (fun k => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hrun.mu_mem (nn k)).1]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (hrun.mu_mem (nn k)).2.trans
          (mul_le_mul_of_nonneg_left (hτle _) hpar.2.2.2.2.1)
      · simpa using (hprevk.norm).const_mul (μbar * (1 / δ))
    have := hx0.add hz
    simpa [FracPSG.Subseq.extrap] using this
  -- a_k
  set a : ℕ → ℝ := fun k => (f (x (nn k + 1))).toReal with ha
  have ha_eq : ∀ k, a k = FracPSG.Subseq.ratio f g (x (nn k + 1)) * g (x (nn k + 1)) := by
    intro k
    have hp : 0 < g (x (nn k + 1)) := hA2.g_pos _ (hxn _).1
    simp only [ha, FracPSG.Subseq.ratio]
    field_simp
  have hA : Tendsto a atTop (𝓝 (L * g xbar)) := by
    have := (hL.comp hnnt1).mul (hgcont.tendsto.comp hy)
    refine this.congr (fun k => ?_)
    rw [ha_eq k]; rfl
  obtain ⟨F0, -, hF0, hF⟩ := fn_real hA1 hxbf
  set F := (f xbar).toReal with hFdef
  -- lower bound by lower semicontinuity
  have hlow : F ≤ L * g xbar := by
    have hfin : ∀ k, f (x (nn k + 1)) = ((a k : ℝ) : EReal) := by
      intro k
      obtain ⟨r, -, h1, h2⟩ := fn_real hA1 (hxn (nn k + 1)).2
      simp only [ha]; rw [← hf] at h1 h2; rw [h2, h1]
    have hfx : f xbar = ((F : ℝ) : EReal) := by
      rw [hFdef, ← hf] at *; rw [hF0, EReal.toReal_coe]
    by_contra hcon
    push Not at hcon
    have hlt : (((L * g xbar : ℝ)) : EReal) < f xbar := by
      rw [hfx]; exact EReal.coe_lt_coe_iff.2 hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hev : ∀ᶠ k in atTop, c < ((a k : ℝ) : EReal) := by
      have := hy.eventually (hlsc xbar c hc2)
      filter_upwards [this] with k hk
      rwa [hfin k] at hk
    have hAE : Tendsto (fun k => ((a k : ℝ) : EReal)) atTop (𝓝 ((L * g xbar : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hA
    have : c ≤ ((L * g xbar : ℝ) : EReal) := ge_of_tendsto hAE (hev.mono fun k hk => hk.le)
    exact absurd hc1 (not_lt.2 this)
  -- upper bound
  set E : ℕ → ℝ := fun k =>
      (fs (x (nn k + 1)) - fs xbar)
      + ⟪gradient fs (FracPSG.Subseq.extrap x κ (nn k)), xbar - x (nn k + 1)⟫_ℝ
      + 1 / (2 * τ (nn k)) *
          (‖xbar - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio f g
              (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2
            - ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio
              f g (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2)
      + ℓ / 2 * (‖xbar - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2) with hE
  have hupk : ∀ k, a k ≤ F + E k := by
    intro k
    have := step_upper hA1 hrun (nn k) hxbS hxbf (hxn (nn k + 1)).2
    simp only [ha, hE, hFdef]
    linarith
  have hfsc : Continuous fs := hA1.fs_contDiff.continuous
  have hgfs : Continuous (fun z => gradient fs z) := by
    have h1 := hA1.fs_contDiff.continuous_fderiv one_ne_zero
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous.comp h1
  have hdy : Tendsto (fun k => xbar - x (nn k + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := xbar)).sub hy; simpa using this
  have hE1 : Tendsto (fun k => fs (x (nn k + 1)) - fs xbar) atTop (𝓝 0) := by
    have := ((hfsc.tendsto xbar).comp hy).sub (tendsto_const_nhds (x := fs xbar))
    simpa using this
  have hE2 : Tendsto (fun k => ⟪gradient fs (FracPSG.Subseq.extrap x κ (nn k)),
      xbar - x (nn k + 1)⟫_ℝ) atTop (𝓝 0) := by
    have := Filter.Tendsto.inner (𝕜 := ℝ) ((hgfs.tendsto xbar).comp hu) hdy
    simpa using this
  have hE4 : Tendsto (fun k => ℓ / 2 * (‖xbar - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2
          - ‖x (nn k + 1) - FracPSG.Subseq.extrap x κ (nn k)‖ ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => xbar - FracPSG.Subseq.extrap x κ (nn k)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := xbar)).sub hu; simpa using this
    have h2 : Tendsto (fun k => x (nn k + 1) - FracPSG.Subseq.extrap x κ (nn k)) atTop (𝓝 0) := by
      have := hy.sub hu; simpa using this
    have := ((h1.norm.pow 2).sub (h2.norm.pow 2)).const_mul (ℓ / 2)
    simpa using this
  -- the quadratic term, by a squeeze
  set T0 := Filter.liminf τ atTop / 2 with hT0
  have hT0pos : 0 < T0 := by rw [hT0]; linarith
  set Θ := |L| + 1
  set Γ := ∑ i, (‖gradient (gi i) xbar‖ + 1)
  have ev1 : ∀ᶠ k in atTop, T0 ≤ τ (nn k) := by
    have h := Filter.eventually_lt_of_lt_liminf (f := atTop) (u := τ) (b := T0)
      (by rw [hT0]; linarith) (isBoundedUnder_of ⟨0, fun n => (hrun.step_pos n).le⟩)
    exact (hnnt.eventually h).mono fun k hk => hk.le
  have ev2 : ∀ᶠ k in atTop, |FracPSG.Subseq.ratio f g (x (nn k))| ≤ Θ := by
    have := (hL.comp hnnt).eventually (Metric.ball_mem_nhds L one_pos)
    filter_upwards [this] with k hk
    have hk' : |FracPSG.Subseq.ratio f g (x (nn k)) - L| < 1 := by
      simpa [Real.dist_eq] using hk
    have := abs_sub_abs_le_abs_sub (FracPSG.Subseq.ratio f g (x (nn k))) L
    linarith
  have ev3 : ∀ᶠ k in atTop, ∀ i, ‖gradient (gi i) (x (nn k))‖ ≤ ‖gradient (gi i) xbar‖ + 1 := by
    refine eventually_all.2 fun i => ?_
    have := (((hgradc i).tendsto.comp hx0).norm).eventually
      (gt_mem_nhds (lt_add_one ‖gradient (gi i) xbar‖))
    exact this.mono fun k hk => hk.le
  have ev4 : ∀ᶠ k in atTop, ‖xbar - FracPSG.Subseq.extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖xbar - FracPSG.Subseq.extrap x μ (nn k)‖) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := xbar)).sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have ev5 : ∀ᶠ k in atTop, ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k)‖ ≤ 1 := by
    have h1 : Tendsto (fun k => ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k)‖) atTop
        (𝓝 0) := by
      have := (hy.sub hv).norm; simpa using this
    exact (h1.eventually (gt_mem_nhds one_pos)).mono fun k hk => hk.le
  have hE3 : Tendsto (fun k => 1 / (2 * τ (nn k)) *
          (‖xbar - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio f g
              (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2
            - ‖x (nn k + 1) - FracPSG.Subseq.extrap x μ (nn k) - (τ (nn k) * FracPSG.Subseq.ratio
              f g (x (nn k))) • gradient (gi (ihat (nn k))) (x (nn k))‖ ^ 2)) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => 1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)) *
        ‖xbar - x (nn k + 1)‖) atTop (𝓝 0) := by
      have := (hdy.norm).const_mul (1 / (2 * T0) * (2 + 2 * (1 / δ * Θ * Γ)))
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [ev1, ev2, ev3, ev4, ev5] with k h1 h2 h3 h4 h5
    rw [Real.norm_eq_abs]
    refine T2_bound _ _ _ _ _ _ T0 δ Θ Γ hT0pos h1 (hτle _) hδ h2 ?_ h4 h5
    exact (h3 _).trans (Finset.single_le_sum (f := fun i => ‖gradient (gi i) xbar‖ + 1)
      (fun i _ => by positivity) (Finset.mem_univ _))
  have hEt : Tendsto E atTop (𝓝 0) := by
    have := ((hE1.add hE2).add hE3).add hE4
    simpa [hE] using this
  have hup : L * g xbar ≤ F := by
    have := le_of_tendsto_of_tendsto hA ((tendsto_const_nhds (x := F)).add hEt)
      (Eventually.of_forall hupk)
    simpa using this
  have heq : L * g xbar = F := le_antisymm hup hlow
  simp only [FracPSG.Subseq.ratio]
  rw [← hFdef, ← heq]
  field_simp

end P2e99


namespace P2e99

open NonconvexSplitting.Shared FracPSG.Enhanced

theorem objF_lsc {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ) :
    LowerSemicontinuous (FracPSG.Subseq.objF fs fn) := by
  have h1 : LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hA1.fs_contDiff.continuous).lowerSemicontinuous
  show LowerSemicontinuous (fun y => ((fs y : ℝ) : EReal) + fn y)
  exact LowerSemicontinuous.add' h1 hA1.fn_lsc (fun y =>
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))

theorem objF_proper {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))} {fs : EuclideanSpace ℝ (Fin N) → ℝ}
    {fn : EuclideanSpace ℝ (Fin N) → EReal} {ℓ : ℝ} (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ) :
    IsProperFn (FracPSG.Subseq.objF fs fn) := by
  refine ⟨fun y => ?_, ?_⟩
  · unfold FracPSG.Subseq.objF
    exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, hA1.fn_proper.1 y⟩
  · obtain ⟨y, -, hy⟩ := hA1.dom_nonempty
    exact ⟨y, hy⟩

/-- Part (5): strong lifted stationarity from (28), convexity of `∂_L(f + ι_S)` and the max rule. -/
theorem part5 {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β m M : ℝ} {xbar : EuclideanSpace ℝ (Fin N)}
    (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ)
    (hA2 : Assumption2' S (FracPSG.Subseq.objF fs fn) gi β m M) (hxbS : xbar ∈ S)
    (h34 : ∀ i ∈ activeSet 0 gi xbar,
        FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) xbar • gradient (gi i) xbar ∈
          LimitingSubdiff (FracPSG.Subseq.addInd (FracPSG.Subseq.objF fs fn) S) xbar)
    (hwc : ∃ ρ : ℝ, IsWeaklyConvexOnE S (FracPSG.Subseq.objF fs fn) ρ) :
    IsStrongLiftedStationary (FracPSG.Subseq.objF fs fn) (maxFn gi) S xbar := by
  have hconv := (FracPSG.Enhanced.lemma_2_2_i ⟨xbar, hxbS⟩ hS hSconv (objF_proper hA1)
    (objF_lsc hA1) hwc xbar).2
  obtain ⟨O, hO, hSO, hCO⟩ := common_open hA2
  refine ⟨hxbS, fun v hv => ?_⟩
  have hvK := limitingSubdiff_maxFn_subset hO hCO (hSO hxbS) hv
  set θ := FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) xbar with hθ
  refine ⟨θ • v, ?_, ?_⟩
  · have hsub : (fun i => gradient (gi i) xbar) '' (activeSet 0 gi xbar : Set (Fin p)) ⊆
        (θ • LinearMap.id : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) ⁻¹'
          LimitingSubdiff (FracPSG.Subseq.addInd (FracPSG.Subseq.objF fs fn) S) xbar := by
      rintro _ ⟨i, hi, rfl⟩
      simpa using h34 i hi
    have hc := hconv.linear_preimage
      (θ • LinearMap.id : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    simpa using convexHull_min hsub hc hvK
  · have hg : 0 < maxFn gi xbar := hA2.g_pos xbar hxbS
    rw [smul_smul, hθ, FracPSG.Subseq.ratio]
    congr 1
    field_simp

end P2e99

open FracPSG.Enhanced NonconvexSplitting.Shared in
theorem solution
    {N p : ℕ} [NeZero p] {S : Set (EuclideanSpace ℝ (Fin N))}
    {fs : EuclideanSpace ℝ (Fin N) → ℝ} {fn : EuclideanSpace ℝ (Fin N) → EReal}
    {gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ} {ℓ β δ ζ ε μbar κbar m M : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin N)} {w : ℕ → Fin p → EuclideanSpace ℝ (Fin N)}
    {ihat : ℕ → Fin p} {τ κ μ : ℕ → ℝ}
    (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hA1 : FracPSG.Subseq.Assumption1 S fs fn ℓ) (hA2 : Assumption2' S (FracPSG.Subseq.objF fs fn) gi β m M)
    (hpar : Step1Params ℓ β δ ε ζ μbar κbar m M)
    (hrun : IsEnhancedRun S fs fn gi ℓ β δ ζ ε μbar κbar m M x w ihat τ κ μ)
    (hS0 : Bornology.IsBounded (FracPSG.Subseq.S0 S (FracPSG.Subseq.objF fs fn) (maxFn gi) (x 0)))
    (hτ : 0 < Filter.liminf τ atTop) :
    ∀ xbar : EuclideanSpace ℝ (Fin N), MapClusterPt xbar atTop x →
      xbar ∈ S ∧ FracPSG.Subseq.objF fs fn xbar ≠ ⊤ ∧
      Tendsto (fun n => FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) atTop
        (𝓝 (FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) xbar)) ∧
      (∀ i ∈ activeSet 0 gi xbar,
        FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) xbar • gradient (gi i) xbar ∈
          LimitingSubdiff (FracPSG.Subseq.addInd (FracPSG.Subseq.objF fs fn) S) xbar) ∧
      ((∃ ρ : ℝ, IsWeaklyConvexOnE S (FracPSG.Subseq.objF fs fn) ρ) →
        IsStrongLiftedStationary (FracPSG.Subseq.objF fs fn) (maxFn gi) S xbar) := by
  intro xbar hcl
  obtain ⟨hxbS, hxbf, hact⟩ :=
    FracPSG.Enhanced.eq_34 hS hSconv hA1 hA2 hpar hrun hS0 hτ xbar hcl
  obtain ⟨hxn, -, -, L, hL⟩ := FracPSG.Enhanced.theorem_6_1_i hS hSconv hA1 hA2 hpar hrun hS0
  obtain ⟨-, hstep, -⟩ := FracPSG.Enhanced.theorem_6_1_ii hS hSconv hA1 hA2 hpar hrun hS0
  have hLeq := P2e99.ratio_limit_eq hA1 hA2 hpar hrun hτ hxn hL hstep hcl hxbS hxbf
    (P2e99.objF_lsc hA1)
  refine ⟨hxbS, hxbf, hLeq ▸ hL, hact, fun hwc => P2e99.part5 hS hSconv hA1 hA2 hxbS hact hwc⟩
