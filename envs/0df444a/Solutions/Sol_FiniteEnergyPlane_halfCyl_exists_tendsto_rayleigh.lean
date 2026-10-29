-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_exists_tendsto_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T00:22:25.975702+00:00
-- url     : https://prove2.me/submissions/4f870579-7011-488e-8a3e-fbf17e745e9e

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_upcrossing_levels
import Theorems.Thm_FiniteEnergyPlane_exists_uniform_loop_gap

open scoped Topology
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

/-! Slice calculus on the half-cylinder, taken from the accepted solution of
`FiniteEnergyPlane.halfCyl_alpha_eta_bounds` (420c53a6). -/

set_option linter.all false

section HD_a

/-! Global existence for linear ODEs `x' = L t (x t)` with bounded coefficients (Picard series). -/


namespace HCWK

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end HCWK

end HD_a

section HD_b

/-! Fundamental solution of `Ψ' = J₀ S∞ Ψ`, its inverse, and the sup-norm gap estimate. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HCWK

variable {n : ℕ}

abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

/-- matrices as operators -/
noncomputable def TL (n : ℕ) : Mat n ≃L[ℝ] (Op n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma TL_apply (M : Mat n) (v : Vec n) : TL n M v = Matrix.toEuclideanLin M v := rfl

end HCWK

end HD_b

section HD_c

/-! Sup-norm gap estimate for the nondegenerate asymptotic operator `-J₀ ∂ₜ - S∞`. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HCWK

variable {n : ℕ}

/-- `J₀` as an operator. -/
noncomputable abbrev Jop (n : ℕ) : Op n := TL n (J₀ n)

end HCWK

end HD_c

section HD_d

/-! Partial derivatives on the half-cylinder `Ω = (0, ∞) × ℝ`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HCWK

/-- The open half-cylinder (as a strip). -/
def Ω : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

lemma isOpen_Ω : IsOpen Ω := isOpen_Ioi.prod isOpen_univ

lemma mem_Ω {s t : ℝ} (hs : 0 < s) : (s, t) ∈ Ω := ⟨hs, trivial⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `∂ₛu`. -/
noncomputable def pS (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (1, 0)
/-- `∂ₜu`. -/
noncomputable def pT (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (0, 1)

/-- Smooth on `Ω`. -/
abbrev Sm (u : ℝ × ℝ → F) : Prop := ContDiffOn ℝ ∞ u Ω

lemma Sm.dS {u : ℝ × ℝ → F} (hu : Sm u) : Sm (pS u) :=
  (hu.fderiv_of_isOpen isOpen_Ω (by simp)).clm_apply contDiffOn_const

lemma Sm.dT {u : ℝ × ℝ → F} (hu : Sm u) : Sm (pT u) :=
  (hu.fderiv_of_isOpen isOpen_Ω (by simp)).clm_apply contDiffOn_const

lemma Sm.diffAt {u : ℝ × ℝ → F} (hu : Sm u) {x : ℝ × ℝ} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x :=
  (hu.contDiffAt (isOpen_Ω.mem_nhds hx)).differentiableAt (by simp)

lemma Sm.cont {u : ℝ × ℝ → F} (hu : Sm u) : ContinuousOn u Ω := hu.continuousOn

lemma Sm.hasDerivAt_s {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => u (σ, t)) (pS u (s, t)) s := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  exact h

lemma Sm.hasDerivAt_t {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun τ => u (s, τ)) (pT u (s, t)) t := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  exact h

lemma Sm.add {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) : Sm (u + v) := ContDiffOn.add hu hv
lemma Sm.sub {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) : Sm (u - v) := ContDiffOn.sub hu hv
lemma Sm.neg {u : ℝ × ℝ → F} (hu : Sm u) : Sm (-u) := ContDiffOn.neg hu

lemma pS_add {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (u + v) x = pS u x + pS v x := by
  simp [pS, fderiv_add (hu.diffAt hx) (hv.diffAt hx)]

lemma pS_neg (u : ℝ × ℝ → F) (x) : pS (-u) x = -pS u x := by
  simp [pS, show (-u) = fun y => -u y from rfl]

/-- mixed partials commute -/
lemma pS_pT {u : ℝ × ℝ → F} (hu : Sm u) {x} (hx : x ∈ Ω) : pS (pT u) x = pT (pS u) x := by
  have hc : ContDiffAt ℝ ∞ u x := hu.contDiffAt (isOpen_Ω.mem_nhds hx)
  have hsymm := hc.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) x := by
    have := (hu.fderiv_of_isOpen isOpen_Ω (m := 1) (WithTop.coe_le_coe.2 le_top)).contDiffAt (isOpen_Ω.mem_nhds hx)
    exact this.differentiableAt one_ne_zero
  show fderiv ℝ (fun y => fderiv ℝ u y (0, 1)) x (1, 0) =
    fderiv ℝ (fun y => fderiv ℝ u y (1, 0)) x (0, 1)
  rw [show (fun y => fderiv ℝ u y (0, 1)) = fun y => (fderiv ℝ u y) ((fun _ => ((0:ℝ), (1:ℝ))) y)
    from rfl, fderiv_clm_apply hd2 (differentiableAt_const _),
    show (fun y => fderiv ℝ u y (1, 0)) = fun y => (fderiv ℝ u y) ((fun _ => ((1:ℝ), (0:ℝ))) y)
    from rfl, fderiv_clm_apply hd2 (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm _ _

/-- `t`-periodicity -/
def TPer (u : ℝ × ℝ → F) : Prop := ∀ s t : ℝ, u (s, t + 1) = u (s, t)

lemma TPer.fderiv {u : ℝ × ℝ → F} (hu : TPer u) (s t : ℝ) :
    fderiv ℝ u (s, t + 1) = fderiv ℝ u (s, t) := by
  have : u = fun y => u (y + (0, 1)) := by
    funext y; obtain ⟨a, b⟩ := y; simp [hu a b]
  conv_rhs => rw [this]
  rw [fderiv_comp_add_right]
  simp

lemma TPer.pS {u : ℝ × ℝ → F} (hu : TPer u) : TPer (pS u) := fun s t => by
  simp [HCWK.pS, hu.fderiv s t]

lemma TPer.periodic {u : ℝ × ℝ → F} (hu : TPer u) (s : ℝ) :
    Function.Periodic (fun t => u (s, t)) 1 := fun t => hu s t

/-! ### Operator-valued coefficients -/

variable {n : ℕ}

lemma pS_apply {A : ℝ × ℝ → Op n} {v : ℝ × ℝ → Vec n} (hA : Sm A) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (fun y => A y (v y)) x = pS A x (v x) + A x (pS v x) := by
  simp only [pS]
  rw [fderiv_clm_apply (hA.diffAt hx) (hv.diffAt hx)]
  simp [add_comm]

lemma Sm.apply {A : ℝ × ℝ → Op n} {v : ℝ × ℝ → Vec n} (hA : Sm A) (hv : Sm v) :
    Sm (fun y => A y (v y)) := hA.clm_apply hv

lemma pS_constOp (T : Op n) {v : ℝ × ℝ → Vec n} (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (fun y => T (v y)) x = T (pS v x) := by
  simp only [pS]
  rw [fderiv_clm_apply (differentiableAt_const _) (hv.diffAt hx)]
  simp

lemma pT_constOp (T : Op n) {v : ℝ × ℝ → Vec n} (hv : Sm v) {x} (hx : x ∈ Ω) :
    pT (fun y => T (v y)) x = T (pT v x) := by
  simp only [pT]
  rw [fderiv_clm_apply (differentiableAt_const _) (hv.diffAt hx)]
  simp

/-- matrix fields as operator fields -/
lemma TL_eq_sum (M : Mat n) :
    TL n M = ∑ i, ∑ j, M i j • TL n (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul]
  congr 1
  ext a b
  simp [Matrix.single_apply]

lemma contDiff_TL {k : WithTop ℕ∞} (S : ℝ × ℝ → Mat n)
    (hS : ∀ i j, ContDiff ℝ k (fun p : ℝ × ℝ => S p i j)) :
    ContDiff ℝ k (fun p => TL n (S p)) := by
  have : (fun p => TL n (S p)) = fun p => ∑ i, ∑ j, S p i j • TL n (Matrix.single i j 1) := by
    funext p; exact TL_eq_sum _
  rw [this]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hS i j).smul contDiff_const

lemma norm_TL_le (M : Mat n) :
    ‖TL n M‖ ≤ ∑ i, ∑ j, |M i j| * ‖TL n (Matrix.single i j 1)‖ := by
  rw [TL_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]

end HCWK

end HD_d

section HD_e

/-! `t`-integrals over a period: differentiation in `s` and integration by parts in `t`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HCWK

lemma cont_slice {F : Type*} [TopologicalSpace F] {w : ℝ × ℝ → F} (hw : ContinuousOn w Ω)
    {s : ℝ} (hs : 0 < s) : Continuous fun t => w (s, t) :=
  hw.comp_continuous (continuous_const.prodMk continuous_id) fun _ => mem_Ω hs

/-- differentiation under the integral sign -/
lemma param_deriv (F F' : ℝ × ℝ → ℝ) (hF : ContinuousOn F Ω) (hF' : ContinuousOn F' Ω)
    (hd : ∀ σ t, 0 < σ → HasDerivAt (fun σ => F (σ, t)) (F' (σ, t)) σ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => ∫ t in (0:ℝ)..1, F (σ, t)) (∫ t in (0:ℝ)..1, F' (s, t)) s := by
  have hK : IsCompact (Metric.closedBall s (s / 2) ×ˢ Icc (0:ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKΩ : Metric.closedBall s (s / 2) ×ˢ Icc (0:ℝ) 1 ⊆ Ω := by
    rintro ⟨a, b⟩ ⟨ha, -⟩
    refine ⟨?_, trivial⟩
    rw [Metric.mem_closedBall, Real.dist_eq] at ha
    show 0 < a
    have := neg_abs_le (a - s)
    linarith
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKΩ)
  have hball : Metric.ball s (s / 2) ⊆ Ioi 0 := by
    intro a ha
    rw [Metric.mem_ball, Real.dist_eq] at ha
    show 0 < a
    have := neg_abs_le (a - s)
    linarith
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun σ t => F (σ, t)) (F' := fun σ t => F' (σ, t)) (x₀ := s)
    (bound := fun _ => M) (Metric.ball_mem_nhds s (by linarith : 0 < s / 2))
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact this.2
  · filter_upwards [Ioi_mem_nhds hs] with σ hσ
    exact (cont_slice hF hσ).aestronglyMeasurable
  · exact (cont_slice hF hs).intervalIntegrable _ _
  · exact (cont_slice hF' hs).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht σ hσ => hM (σ, t) ⟨Metric.ball_subset_closedBall hσ, ?_⟩
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · exact Eventually.of_forall fun t _ σ hσ => hd σ t (hball hσ)

variable {n : ℕ}

/-- `∫₀¹ ⟪u(s, t), v(s, t)⟫ dt` -/
noncomputable def Ip (u v : ℝ × ℝ → Vec n) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ⟪u (s, t), v (s, t)⟫

lemma cont_inner {u v : ℝ × ℝ → Vec n} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : Continuous fun t => ⟪u (s, t), v (s, t)⟫ :=
  (cont_slice hu hs).inner (cont_slice hv hs)

lemma Ip_hasDerivAt {u v : ℝ × ℝ → Vec n} (hu : Sm u) (hv : Sm v) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Ip u v) (Ip (pS u) v s + Ip u (pS v) s) s := by
  have h := param_deriv (fun x => ⟪u x, v x⟫) (fun x => ⟪pS u x, v x⟫ + ⟪u x, pS v x⟫)
    (hu.cont.inner hv.cont) ((hu.dS.cont.inner hv.cont).add (hu.cont.inner hv.dS.cont))
    (fun σ t hσ => ((hu.hasDerivAt_s hσ).inner ℝ (hv.hasDerivAt_s hσ)).congr_deriv
      (add_comm _ _)) hs
  refine h.congr_deriv ?_
  simp only [Ip]
  exact intervalIntegral.integral_add ((cont_inner hu.dS.cont hv.cont hs).intervalIntegrable _ _)
    ((cont_inner hu.cont hv.dS.cont hs).intervalIntegrable _ _)

lemma Ip_ibp {u v : ℝ × ℝ → Vec n} (hu : Sm u) (hv : Sm v) (hpu : TPer u) (hpv : TPer v)
    {s : ℝ} (hs : 0 < s) : Ip (pT u) v s = -Ip u (pT v) s := by
  have h1 := cont_inner hu.dT.cont hv.cont hs
  have h2 := cont_inner hu.cont hv.dT.cont hs
  have key : ∫ t in (0:ℝ)..1, (⟪pT u (s, t), v (s, t)⟫ + ⟪u (s, t), pT v (s, t)⟫) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => ⟪u (s, t), v (s, t)⟫)
      (fun t _ => ((hu.hasDerivAt_t hs).inner ℝ (hv.hasDerivAt_t hs)).congr_deriv (add_comm _ _))
      ((h1.add h2).intervalIntegrable _ _)]
    rw [show (1:ℝ) = 0 + 1 by norm_num, hpu, hpv, sub_self]
  rw [intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)] at key
  simp only [Ip]
  linarith

lemma Ip_comm (u v : ℝ × ℝ → Vec n) (s : ℝ) : Ip u v s = Ip v u s := by
  simp only [Ip, real_inner_comm]

lemma Ip_self_nonneg (u : ℝ × ℝ → Vec n) (s : ℝ) : 0 ≤ Ip u u s :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ => real_inner_self_nonneg

end HCWK

end HD_e

section HD_f

/-! Bounds on the coefficient field `S` from its `C^∞` convergence to `S∞`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HCWK

variable {n : ℕ}

lemma pS_le0 (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : |pS g x| ≤ ‖iteratedFDeriv ℝ 1 g x‖ := by
  rw [norm_iteratedFDeriv_one]
  have := (fderiv ℝ g x).le_opNorm (1, 0)
  simpa only [pS, ge_iff_le, Real.norm_eq_abs, Prod.norm_mk, norm_one, norm_zero, zero_le_one,
    sup_of_le_left, mul_one] using this

lemma pS_pS_le (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    |pS (pS g) x| ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable one_ne_zero) x
  have h : pS (pS g) x = fderiv ℝ (fderiv ℝ g) x (1, 0) (1, 0) := by
    show fderiv ℝ (fun y => fderiv ℝ g y (1, 0)) x (1, 0) = _
    rw [show (fun y => fderiv ℝ g y (1, 0)) = fun y => (fderiv ℝ g y) ((fun _ => ((1:ℝ), (0:ℝ))) y)
      from rfl, fderiv_clm_apply hd2 (differentiableAt_const _)]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  rw [h, show fderiv ℝ (fderiv ℝ g) x (1, 0) (1, 0) = iteratedFDeriv ℝ 2 g x ![(1, 0), (1, 0)] by
    rw [iteratedFDeriv_two_apply]; rfl]
  have := (iteratedFDeriv ℝ 2 g x).le_opNorm ![(1, 0), (1, 0)]
  simpa only [ge_iff_le, Real.norm_eq_abs, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Prod.norm_mk, norm_one, norm_zero, zero_le_one, sup_of_le_left, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one] using this

/-- `∂ₛ` of an operator field built from a matrix field. -/
lemma hasFDerivAt_TL (S : ℝ × ℝ → Mat n) (hS : ∀ i j, Differentiable ℝ (fun p => S p i j))
    (x : ℝ × ℝ) : pS (fun p => TL n (S p)) x =
      TL n (Matrix.of fun i j => pS (fun p => S p i j) x) := by
  have hd : HasFDerivAt (fun p => TL n (S p))
      (∑ i, ∑ j, (fderiv ℝ (fun p => S p i j) x).smulRight (TL n (Matrix.single i j 1))) x := by
    have hsum : (fun p => TL n (S p)) = fun p => ∑ i, ∑ j, S p i j • TL n (Matrix.single i j 1) :=
      funext fun p => TL_eq_sum _
    rw [hsum]
    refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
    exact ((hS i j) x).hasFDerivAt.smul_const (TL n (Matrix.single i j (1:ℝ)))
  refine (congrArg (fun L => L (1, 0)) hd.fderiv).trans (Eq.trans ?_ (TL_eq_sum _).symm)
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    Matrix.of_apply, pS]

lemma contDiff_of_pS (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j)) :
    ∀ i j, ContDiff ℝ ∞ (fun p => (Matrix.of fun i j => pS (fun p => S p i j) p) i j) := by
  intro i j
  simp only [Matrix.of_apply, pS]
  exact (hS i j).fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const

/-- entrywise smallness gives operator smallness -/
lemma op_small : ∃ c, 0 < c ∧ ∀ (M : Mat n) (δ : ℝ), 0 ≤ δ → (∀ i j, |M i j| ≤ δ) →
    ‖TL n M‖ ≤ c * δ := by
  set c0 := ∑ i, ∑ j, ‖TL n (Matrix.single i j (1:ℝ))‖
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨1 + c0, by linarith only [hc0], fun M δ hδ hM => (norm_TL_le M).trans ?_⟩
  calc ∑ i, ∑ j, |M i j| * ‖TL n (Matrix.single i j 1)‖
      ≤ ∑ i, ∑ j, δ * ‖TL n (Matrix.single i j (1:ℝ))‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hM i j) (norm_nonneg _)
    _ = δ * c0 := by simp only [c0, Finset.mul_sum]
    _ ≤ (1 + c0) * δ := by nlinarith only [hδ, hc0]

lemma pS_snd (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ × ℝ) : pS (fun p => f p.2) x = 0 := by
  have : HasFDerivAt (fun p : ℝ × ℝ => f p.2) ((fderiv ℝ f x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hf x.2).hasFDerivAt.comp x hasFDerivAt_snd
  simp only [pS, this.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    fderiv_eq_smul_deriv, smul_eq_mul, zero_mul]

lemma pS_entry (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (i j) :
    pS (fun p => S p i j) = pS (fun p => S p i j - Sinf p.2 i j) := by
  funext x
  have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => S p i j) x := ((hS i j).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => Sinf p.2 i j) x :=
    (((hSinf' i j).differentiable (by simp)) x.2).comp x differentiableAt_snd
  have := pS_snd (fun t => Sinf t i j) ((hSinf' i j).differentiable (by simp)) x
  simp only [pS] at this ⊢
  rw [fderiv_fun_sub h1 h2]
  simp only [sub_apply, this, sub_zero]

end HCWK

end HD_f

section HD_g

/-! Second derivative of the energy `∫₀¹ |η(s, t)|² dt`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HCWK

variable {n : ℕ}

lemma inner_TL_left (M : Mat n) (v w : Vec n) :
    ⟪TL n M v, w⟫ = ⟪v, TL n (Matrix.transpose M) w⟫ := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint M
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [TL_apply, TL_apply, h, LinearMap.adjoint_inner_right]

lemma inner_Jop (v w : Vec n) : ⟪v, Jop n w⟫ = -⟪Jop n v, w⟫ := by
  rw [Jop, inner_TL_left, Matrix.J_transpose, map_neg, ContinuousLinearMap.neg_apply, inner_neg_right,
    neg_neg]

lemma inner_symm {M : Mat n} (hM : M.IsSymm) (v w : Vec n) : ⟪TL n M v, w⟫ = ⟪v, TL n M w⟫ := by
  rw [inner_TL_left, hM.eq]

lemma pS_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u v : ℝ × ℝ → F}
    (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) : pS (u - v) x = pS u x - pS v x := by
  rw [sub_eq_add_neg, pS_add hu hv.neg hx, pS_neg, ← sub_eq_add_neg]

lemma ii {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F Ω) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun t => F (s, t)) volume 0 1 :=
  (cont_slice hF hs).intervalIntegrable _ _

section energy

variable (A : ℝ × ℝ → Op n) (η : ℝ × ℝ → Vec n)

/-- residual `∂ₛη + J₀ ∂ₜη + A η` -/
noncomputable def res (x : ℝ × ℝ) : Vec n := pS η x + Jop n (pT η x) + A x (η x)

/-- integrand of the second derivative -/
noncomputable def Qd (x : ℝ × ℝ) : ℝ :=
  2 * ⟪pS η x, pS η x⟫ + ⟪A x (η x), pS η x⟫ - ⟪η x, A x (pS η x)⟫ - ⟪res A η x, pS η x⟫ +
    ⟪η x, pS (res A η) x⟫ - ⟪η x, pS A x (η x)⟫

variable {A η}

lemma Sm.jop {v : ℝ × ℝ → Vec n} (hv : Sm v) : Sm (fun x => Jop n (v x)) :=
  (contDiffOn_const (c := Jop n)).clm_apply hv

lemma Sm.rs (hA : Sm A) (hη : Sm η) : Sm (res A η) :=
  ((hη.dS.add hη.dT.jop).add (hA.apply hη))

theorem energy_d2 (hA : Sm A) (hη : Sm η) (hpA : TPer A) (hpη : TPer η) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Ip η (pS η)) (∫ t in (0:ℝ)..1, Qd A η (s, t)) s := by
  have hξ := hη.dS
  have h := Ip_hasDerivAt hη hξ hs
  refine h.congr_deriv ?_
  set ξ := pS η
  set r := res A η
  have hr : Sm r := Sm.rs hA hη
  -- `pS ξ` in terms of the equation
  have hξeq : ξ = fun x => r x - Jop n (pT η x) - A x (η x) := by
    funext x; simp only [r, res]; abel
  have hpSξ : ∀ x ∈ Ω, pS ξ x = pS r x - Jop n (pT ξ x) - (pS A x (η x) + A x (ξ x)) := by
    intro x hx
    conv_lhs => rw [hξeq]
    have e1 : (fun x => r x - Jop n (pT η x) - A x (η x)) =
        (r - fun x => Jop n (pT η x)) - fun x => A x (η x) := rfl
    rw [e1, pS_sub (hr.sub hη.dT.jop) (hA.apply hη) hx, pS_sub hr hη.dT.jop hx,
      pS_constOp _ hη.dT hx, pS_pT hη hx, pS_apply hA hη hx]
  -- integration by parts for the `J₀ ∂ₜ` term
  have hJ : Sm (fun x => Jop n (η x)) := hη.jop
  have hpJ : TPer (fun x => Jop n (η x)) := fun a b => by simp [hpη a b]
  have hibp := Ip_ibp hJ hξ hpJ hpη.pS hs
  have hpTJ : ∀ x ∈ Ω, pT (fun x => Jop n (η x)) x = r x - ξ x - A x (η x) := by
    intro x hx
    rw [pT_constOp _ hη hx]; simp only [r, res, ξ]; abel
  have hI1 : Ip η (fun x => Jop n (pT ξ x)) s = Ip (fun x => r x - ξ x - A x (η x)) ξ s := by
    have e1 : Ip η (fun x => Jop n (pT ξ x)) s = -Ip (fun x => Jop n (η x)) (pT ξ) s := by
      simp only [Ip, inner_Jop]
      exact intervalIntegral.integral_neg
    rw [e1, ← hibp]
    simp only [Ip]
    exact intervalIntegral.integral_congr fun t _ => by rw [hpTJ (s, t) (mem_Ω hs)]
  -- continuity facts
  have cη := hη.cont
  have cξ := hξ.cont
  have cr := hr.cont
  have cAη := (hA.apply hη).cont
  have cAξ := (hA.apply hξ).cont
  have cpr := hr.dS.cont
  have cpAη := (hA.dS.apply hη).cont
  have cJξ := hξ.dT.jop.cont
  -- rewrite `Ip η (pS ξ)`
  have hI2 : Ip η (pS ξ) s = ∫ t in (0:ℝ)..1, (⟪η (s, t), pS r (s, t)⟫ - ⟪η (s, t), Jop n (pT ξ (s, t))⟫ -
      ⟪η (s, t), pS A (s, t) (η (s, t))⟫ - ⟪η (s, t), A (s, t) (ξ (s, t))⟫) := by
    simp only [Ip]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hpSξ (s, t) (mem_Ω hs), inner_sub_right, inner_sub_right, inner_add_right]
    ring
  rw [hI2]
  simp only [Ip] at hI1 ⊢
  have iA := ii (cη.inner cpr) hs
  have iB := ii (cη.inner cJξ) hs
  have iC := ii (cη.inner cpAη) hs
  have iD := ii (cη.inner cAξ) hs
  have iE := ii (cξ.inner cξ) hs
  have iF := ii (cAη.inner cξ) hs
  have iG := ii (cr.inner cξ) hs
  rw [intervalIntegral.integral_sub ((iA.sub iB).sub iC) iD, intervalIntegral.integral_sub (iA.sub iB) iC,
    intervalIntegral.integral_sub iA iB, hI1]
  have e3 : ∫ t in (0:ℝ)..1, ⟪r (s, t) - ξ (s, t) - A (s, t) (η (s, t)), ξ (s, t)⟫ =
      (∫ t in (0:ℝ)..1, ⟪r (s, t), ξ (s, t)⟫) - (∫ t in (0:ℝ)..1, ⟪ξ (s, t), ξ (s, t)⟫) -
        ∫ t in (0:ℝ)..1, ⟪A (s, t) (η (s, t)), ξ (s, t)⟫ := by
    simp only [inner_sub_left]
    rw [intervalIntegral.integral_sub (iG.sub iE) iF, intervalIntegral.integral_sub iG iE]
  have e4 : ∫ t in (0:ℝ)..1, Qd A η (s, t) = 2 * (∫ t in (0:ℝ)..1, ⟪ξ (s, t), ξ (s, t)⟫) +
      (∫ t in (0:ℝ)..1, ⟪A (s, t) (η (s, t)), ξ (s, t)⟫) - (∫ t in (0:ℝ)..1, ⟪η (s, t), A (s, t) (ξ (s, t))⟫) -
      (∫ t in (0:ℝ)..1, ⟪r (s, t), ξ (s, t)⟫) + (∫ t in (0:ℝ)..1, ⟪η (s, t), pS r (s, t)⟫) -
      ∫ t in (0:ℝ)..1, ⟪η (s, t), pS A (s, t) (η (s, t))⟫ := by
    simp only [Qd]
    rw [intervalIntegral.integral_sub (((((iE.const_mul 2).add iF).sub iD).sub iG).add iA) iC,
      intervalIntegral.integral_add ((((iE.const_mul 2).add iF).sub iD).sub iG) iA,
      intervalIntegral.integral_sub (((iE.const_mul 2).add iF).sub iD) iG,
      intervalIntegral.integral_sub ((iE.const_mul 2).add iF) iD,
      intervalIntegral.integral_add (iE.const_mul 2) iF, intervalIntegral.integral_const_mul]
  rw [e3, e4]
  ring

end energy

end HCWK

end HD_g

section HD_h

/-! Jensen, the `L²` gap estimate, and two one-variable decay lemmas. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HCWK

variable {n : ℕ}

lemma mono_Ici (g g' : ℝ → ℝ) (a : ℝ) (hd : ∀ s ≥ a, HasDerivAt g (g' s) s)
    (hnn : ∀ s ≥ a, 0 ≤ g' s) : MonotoneOn g (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hnn x (interior_subset hx))

lemma anti_Ici (g g' : ℝ → ℝ) (a : ℝ) (hd : ∀ s ≥ a, HasDerivAt g (g' s) s)
    (hnp : ∀ s ≥ a, g' s ≤ 0) : AntitoneOn g (Ici a) := by
  have := mono_Ici (fun x => -g x) (fun x => -g' x) a (fun s hs => (hd s hs).neg)
    (fun s hs => by linarith [hnp s hs])
  intro x hx y hy hxy
  have := this hx hy hxy
  simp only at this
  linarith

end HCWK

end HD_h

section HD_i

/-! Generic lower bounds for the energy's second derivative. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HCWK

variable {n : ℕ}

lemma pS_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u v : ℝ × ℝ → F}
    (h : EqOn u v Ω) {x} (hx : x ∈ Ω) : pS u x = pS v x := by
  have : u =ᶠ[𝓝 x] v := Filter.eventuallyEq_of_mem (isOpen_Ω.mem_nhds hx) h
  simp only [pS, this.fderiv_eq]

lemma Qd_cont {A : ℝ × ℝ → Op n} {η : ℝ × ℝ → Vec n} (hA : Sm A) (hη : Sm η) :
    ContinuousOn (Qd A η) Ω := by
  have hr := Sm.rs hA hη
  have c1 := hη.dS.cont
  unfold Qd
  refine (((((continuousOn_const.mul (c1.inner c1)).add ((hA.apply hη).cont.inner c1)).sub
    (hη.cont.inner (hA.apply hη.dS).cont)).sub (hr.cont.inner c1)).add
    (hη.cont.inner hr.dS.cont)).sub (hη.cont.inner (hA.dS.apply hη).cont)

lemma abs_inner_op (T : Op n) (v w : Vec n) : |⟪T v, w⟫| ≤ ‖T‖ * ‖v‖ * ‖w‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg _))

end HCWK

end HD_i

section AF_g

/-! The quantities `F, D, G, α, q` of a solution and their derivatives. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HCWK

variable {n : ℕ}

section sol

variable (A : ℝ × ℝ → Op n) (ζ : ℝ × ℝ → Vec n)

noncomputable def Fz (s : ℝ) : ℝ := Ip ζ ζ s
noncomputable def Dz (s : ℝ) : ℝ := Ip ζ (pS ζ) s
noncomputable def Gz (s : ℝ) : ℝ := Ip (pS ζ) (pS ζ) s
noncomputable def αz (s : ℝ) : ℝ := Dz ζ s / Fz ζ s
noncomputable def qz (s : ℝ) : ℝ := Gz ζ s / Fz ζ s - (αz ζ s) ^ 2
noncomputable def α1z (s : ℝ) : ℝ := (∫ t in (0:ℝ)..1, Qd A ζ (s, t)) / Fz ζ s - 2 * (αz ζ s) ^ 2

variable {A ζ}

lemma Fz_hasDerivAt (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) : HasDerivAt (Fz ζ) (2 * Dz ζ s) s :=
  (Ip_hasDerivAt hζ hζ hs).congr_deriv (by simp only [Dz]; rw [Ip_comm (pS ζ) ζ]; ring)

lemma Fz_hasDerivAt' (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) :
    HasDerivAt (Fz ζ) (2 * αz ζ s * Fz ζ s) s :=
  (Fz_hasDerivAt hζ hs).congr_deriv (by simp only [αz]; field_simp)

lemma Gz_hasDerivAt (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Gz ζ) (Ip (pS (pS ζ)) (pS ζ) s + Ip (pS ζ) (pS (pS ζ)) s) s :=
  Ip_hasDerivAt hζ.dS hζ.dS hs

lemma αz_hasDerivAt (hA : Sm A) (hζ : Sm ζ) (hpA : TPer A) (hpζ : TPer ζ) {s : ℝ} (hs : 0 < s)
    (hF : 0 < Fz ζ s) : HasDerivAt (αz ζ) (α1z A ζ s) s := by
  have h1 := energy_d2 hA hζ hpA hpζ hs
  have h2 := Fz_hasDerivAt hζ hs
  refine (h1.div h2 hF.ne').congr_deriv ?_
  simp only [α1z, αz, Dz]
  field_simp

lemma Fz_cont (hζ : Sm ζ) : ContinuousOn (Fz ζ) (Ioi 0) := fun s hs =>
  (Fz_hasDerivAt hζ hs).continuousAt.continuousWithinAt

lemma Gz_cont (hζ : Sm ζ) : ContinuousOn (Gz ζ) (Ioi 0) := fun s hs =>
  (Gz_hasDerivAt hζ hs).continuousAt.continuousWithinAt

lemma Dz_cont (hζ : Sm ζ) : ContinuousOn (Dz ζ) (Ioi 0) := fun s hs =>
  (Ip_hasDerivAt hζ hζ.dS hs).continuousAt.continuousWithinAt

end sol

end HCWK

end AF_g

/-! Extra slice lemmas, from the accepted solution of `FiniteEnergyPlane.halfCyl_alpha_eta_bounds` (420c53a6). -/

set_option linter.all false

section AF_b

/-! Cauchy–Schwarz for `Ip` and the differential inequality for `α = ⟨ζ, ∂ₛζ⟩ / |ζ|²`. -/


namespace HCWK

variable {n : ℕ}

lemma cs_real (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b) :
    (∫ t in (0:ℝ)..1, a t * b t) ^ 2 ≤ (∫ t in (0:ℝ)..1, a t ^ 2) * ∫ t in (0:ℝ)..1, b t ^ 2 := by
  have iaa : IntervalIntegrable (fun t => a t ^ 2) volume 0 1 := (ha.pow 2).intervalIntegrable _ _
  have ibb : IntervalIntegrable (fun t => b t ^ 2) volume 0 1 := (hb.pow 2).intervalIntegrable _ _
  have iab : IntervalIntegrable (fun t => a t * b t) volume 0 1 := (ha.mul hb).intervalIntegrable _ _
  have h : ∀ x : ℝ, 0 ≤ (∫ t in (0:ℝ)..1, b t ^ 2) * x * x + 2 * (∫ t in (0:ℝ)..1, a t * b t) * x +
      ∫ t in (0:ℝ)..1, a t ^ 2 := by
    intro x
    have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (a t + x * b t) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
    have e : ∫ t in (0:ℝ)..1, (a t + x * b t) ^ 2 = ∫ t in (0:ℝ)..1,
        (a t ^ 2 + (2 * x) * (a t * b t) + (x * x) * b t ^ 2) := by
      congr 1; funext t; ring
    rw [e, intervalIntegral.integral_add (iaa.add (iab.const_mul _)) (ibb.const_mul _),
      intervalIntegral.integral_add iaa (iab.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h0
    linarith
  set P := ∫ t in (0:ℝ)..1, b t ^ 2
  set Q := ∫ t in (0:ℝ)..1, a t * b t
  set R := ∫ t in (0:ℝ)..1, a t ^ 2
  have h' : ∀ x : ℝ, 0 ≤ P * (x * x) + (2 * Q) * x + R := fun x => by
    have := h x; rw [← mul_assoc]; exact this
  have := discrim_le_zero h'
  simp only [discrim] at this
  nlinarith

/-- `∫ |u| |v| ≤ √(Ip u u) √(Ip v v)` -/
lemma cs_Ip {u v : ℝ × ℝ → Vec n} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : ∫ t in (0:ℝ)..1, ‖u (s, t)‖ * ‖v (s, t)‖ ≤
      Real.sqrt (Ip u u s) * Real.sqrt (Ip v v s) := by
  have hu' := (cont_slice hu hs).norm
  have hv' := (cont_slice hv hs).norm
  have hc := cs_real _ _ hu' hv'
  have e1 : Ip u u s = ∫ t in (0:ℝ)..1, ‖u (s, t)‖ ^ 2 := by
    simp only [Ip, real_inner_self_eq_norm_sq]
  have e2 : Ip v v s = ∫ t in (0:ℝ)..1, ‖v (s, t)‖ ^ 2 := by
    simp only [Ip, real_inner_self_eq_norm_sq]
  rw [← e1, ← e2] at hc
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, ‖u (s, t)‖ * ‖v (s, t)‖ :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity
  rw [← Real.sqrt_mul (Ip_self_nonneg u s)]
  exact Real.le_sqrt_of_sq_le hc

lemma cs_Ip' {u v : ℝ × ℝ → Vec n} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : Ip u v s ^ 2 ≤ Ip u u s * Ip v v s := by
  have h1 : |Ip u v s| ≤ ∫ t in (0:ℝ)..1, ‖u (s, t)‖ * ‖v (s, t)‖ := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    exact intervalIntegral.integral_mono_on zero_le_one
      ((cont_slice (hu.inner hv) hs).abs.intervalIntegrable _ _)
      (((cont_slice hu hs).norm.mul (cont_slice hv hs).norm).intervalIntegrable _ _)
      fun t _ => abs_real_inner_le_norm _ _
  have h2 := (h1.trans (cs_Ip hu hv hs))
  have h3 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
  rw [mul_pow, Real.sq_sqrt (Ip_self_nonneg _ _), Real.sq_sqrt (Ip_self_nonneg _ _)] at h3
  exact h3

/-- the differential inequality for `α = D / F` in abstract form -/
lemma alpha_ineq (F D G D' m1 m2 : ℝ) (hF : 0 < F) (hm1 : 0 ≤ m1) (hCS : D ^ 2 ≤ F * G)
    (hD' : 2 * G - 2 * m1 * Real.sqrt F * Real.sqrt G - m2 * F ≤ D') :
    2 * (G / F - (D / F) ^ 2) - 2 * m1 * (Real.sqrt (G / F - (D / F) ^ 2) + |D / F|) - m2 ≤
      D' / F - 2 * (D / F) ^ 2 := by
  set α := D / F
  set q := G / F - α ^ 2
  have hG : 0 ≤ G := by
    by_contra h; push_neg at h; nlinarith [sq_nonneg D]
  have hq : 0 ≤ q := by
    simp only [q, α]; rw [div_pow, sub_nonneg, div_le_div_iff₀ (by positivity) hF]; nlinarith
  have hsG : Real.sqrt G / Real.sqrt F ≤ Real.sqrt q + |α| := by
    rw [← Real.sqrt_div' _ hF.le]
    have : G / F = q + α ^ 2 := by simp only [q]; ring
    rw [this, Real.sqrt_le_left]
    · nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q, abs_nonneg α, sq_abs α]
    · positivity
  have hsF : 0 < Real.sqrt F := Real.sqrt_pos.2 hF
  have e : D' / F ≥ 2 * (G / F) - 2 * m1 * (Real.sqrt G / Real.sqrt F) - m2 := by
    rw [ge_iff_le, le_div_iff₀ hF]
    have : Real.sqrt G / Real.sqrt F * F = Real.sqrt F * Real.sqrt G := by
      field_simp; rw [Real.sq_sqrt hF.le]
    rw [sub_mul, sub_mul, mul_assoc (2 * m1), this, mul_assoc, div_mul_cancel₀ _ hF.ne']
    linarith
  have : G / F = q + α ^ 2 := by simp only [q]; ring
  nlinarith [mul_le_mul_of_nonneg_left hsG (by linarith : 0 ≤ 2 * m1)]

end HCWK

end AF_b

section AF_c

/-! One-variable lemmas: forward positivity (unique continuation) and barriers. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HCWK

/-- lower barrier: `α' ≥ -M (1 + |α|)` ⇒ `α ≥ -(|α a| + 1) e^{(M + 1) (s - a)}` -/
lemma alpha_lower (α α1 : ℝ → ℝ) (a b M : ℝ) (hM : 0 ≤ M)
    (hα : ∀ s ∈ Icc a b, HasDerivAt α (α1 s) s)
    (hα1 : ∀ s ∈ Icc a b, -M * (1 + |α s|) ≤ α1 s) :
    ∀ s ∈ Icc a b, -((|α a| + 1) * Real.exp ((M + 1) * (s - a))) ≤ α s := by
  intro s hs
  have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => -α s) (f' := fun s => -α1 s)
    (a := a) (b := b) (B := fun s => (|α a| + 1) * Real.exp ((M + 1) * (s - a)) - 1)
    (B' := fun s => (M + 1) * ((|α a| + 1) * Real.exp ((M + 1) * (s - a))))
    (fun x hx => (hα x hx).continuousAt.continuousWithinAt.neg)
    (fun x hx => (hα x (Ico_subset_Icc_self hx)).neg.hasDerivWithinAt)
    (by simp; linarith [neg_abs_le (α a)])
    (by fun_prop)
    (fun x _ => by
      have := ((((hasDerivAt_id x).sub_const a).const_mul (M + 1)).exp.const_mul (|α a| + 1)).sub_const 1
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp; ring)
    (fun x hx hc => by
      have h1 := hα1 x (Ico_subset_Icc_self hx)
      try simp only at hc ⊢
      have hE : 1 ≤ Real.exp ((M + 1) * (x - a)) :=
        Real.one_le_exp (mul_nonneg (by linarith) (by linarith [hx.1]))
      have hneg : α x ≤ 0 := by nlinarith [abs_nonneg (α a)]
      rw [abs_of_nonpos hneg] at h1
      nlinarith [Real.exp_pos ((M + 1) * (x - a)), abs_nonneg (α a)])
    hs
  try simp only at this
  have h0 : 0 ≤ (|α a| + 1) * Real.exp ((M + 1) * (s - a)) := by positivity
  linarith

/-- forward positivity: if `F' = 2 α F` and `α' ≥ -M (1 + |α|)` wherever `F > 0`, then `F > 0`
persists. -/
lemma pos_forward (F α α1 : ℝ → ℝ) (p b M : ℝ) (hM : 0 ≤ M) (hFc : ContinuousOn F (Icc p b))
    (hp : 0 < F p) (hF : ∀ s ∈ Icc p b, 0 < F s → HasDerivAt F (2 * α s * F s) s)
    (hα : ∀ s ∈ Icc p b, 0 < F s → HasDerivAt α (α1 s) s)
    (hα1 : ∀ s ∈ Icc p b, 0 < F s → -M * (1 + |α s|) ≤ α1 s) : ∀ s ∈ Icc p b, 0 < F s := by
  by_contra hcon
  push_neg at hcon
  set T := {s ∈ Icc p b | F s ≤ 0}
  have hTne : T.Nonempty := by obtain ⟨s, hs, hs'⟩ := hcon; exact ⟨s, hs, hs'⟩
  have hTc : IsClosed T := hFc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hTb : BddBelow T := ⟨p, fun x hx => hx.1.1⟩
  set s0 := sInf T
  have hs0T : s0 ∈ T := hTc.csInf_mem hTne hTb
  have hps0 : p < s0 := by
    rcases eq_or_lt_of_le hs0T.1.1 with h | h
    · exfalso; have := hs0T.2; rw [← h] at this; linarith
    · exact h
  have hpos : ∀ s ∈ Ico p s0, 0 < F s := by
    intro s hs
    by_contra h
    push_neg at h
    have : s0 ≤ s := csInf_le hTb ⟨⟨hs.1, hs.2.le.trans hs0T.1.2⟩, h⟩
    linarith [hs.2]
  set Bm := (|α p| + 1) * Real.exp ((M + 1) * (s0 - p))
  have hlow : ∀ s ∈ Ico p s0, -Bm ≤ α s := by
    intro s hs
    have hsub : Icc p s ⊆ Icc p b := Icc_subset_Icc le_rfl (hs.2.le.trans hs0T.1.2)
    have hsub' : ∀ x ∈ Icc p s, x ∈ Ico p s0 := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hs.2⟩
    have := alpha_lower α α1 p s M hM
      (fun x hx => hα x (hsub hx) (hpos x (hsub' x hx)))
      (fun x hx => hα1 x (hsub hx) (hpos x (hsub' x hx))) s ⟨hs.1, le_rfl⟩
    refine le_trans ?_ this
    simp only [Bm, neg_le_neg_iff]
    gcongr
    linarith [hs.2]
  -- `log F + 2 Bm s` is monotone on `[p, s0)`
  have hlog : ∀ s ∈ Ico p s0, Real.log (F p) - 2 * Bm * (s - p) ≤ Real.log (F s) := by
    intro s hs
    have hsub : Icc p s ⊆ Icc p b := Icc_subset_Icc le_rfl (hs.2.le.trans hs0T.1.2)
    have hsub' : ∀ x ∈ Icc p s, x ∈ Ico p s0 := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hs.2⟩
    have hmono : MonotoneOn (fun x => Real.log (F x) + 2 * Bm * x) (Icc p s) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => 2 * α x + 2 * Bm)
        (convex_Icc p s) ?_ ?_ ?_
      · intro x hx
        have h1 := hF x (hsub hx) (hpos x (hsub' x hx))
        exact (h1.continuousAt.log (hpos x (hsub' x hx)).ne').continuousWithinAt.add
          (continuousWithinAt_const.mul continuousWithinAt_id)
      · intro x hx
        have hx' := interior_subset hx
        have h1 := (hF x (hsub hx') (hpos x (hsub' x hx'))).log (hpos x (hsub' x hx')).ne'
        have h2 := (hasDerivAt_id x).const_mul (2 * Bm)
        refine ((h1.add h2).congr_deriv ?_).hasDerivWithinAt
        have := (hpos x (hsub' x hx')).ne'
        field_simp
      · intro x hx
        have hx' := interior_subset hx
        linarith [hlow x (hsub' x hx')]
    have := hmono ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
    simp only at this
    linarith
  set c := F p * Real.exp (-(2 * Bm * (s0 - p)))
  have hc : 0 < c := by positivity
  have hge : ∀ s ∈ Ico p s0, c ≤ F s := by
    intro s hs
    have h1 := hlog s hs
    have h2 : Real.log c ≤ Real.log (F s) := by
      rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]
      have hBm : 0 ≤ Bm := by positivity
      nlinarith [hs.2]
    exact (Real.log_le_log_iff hc (hpos s hs)).1 h2
  -- continuity at `s0`
  have hcw : ContinuousWithinAt F (Ico p s0) s0 :=
    (hFc s0 hs0T.1).mono (fun x hx => ⟨hx.1, hx.2.le.trans hs0T.1.2⟩)
  have hcl : s0 ∈ closure (Ico p s0) := by
    rw [closure_Ico hps0.ne]; exact ⟨hps0.le, le_rfl⟩
  have : c ≤ F s0 := by
    have hne : (𝓝[Ico p s0] s0).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall hge)
  linarith [hs0T.2]

end HCWK

end AF_c

section AF_d2

open scoped Topology
open Set Filter MeasureTheory

namespace HCWK

lemma F_lower (F α : ℝ → ℝ) (a b lam : ℝ) (hab : a ≤ b) (hF : ∀ x ∈ Icc a b, 0 < F x)
    (hFd : ∀ x ∈ Icc a b, HasDerivAt F (2 * α x * F x) x) (hα : ∀ x ∈ Icc a b, lam ≤ α x) :
    F a * Real.exp (2 * lam * (b - a)) ≤ F b := by
  have hmono : MonotoneOn (fun x => Real.log (F x) - 2 * lam * x) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => 2 * α x - 2 * lam)
      (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      exact ((hFd x hx).continuousAt.log (hF x hx).ne').continuousWithinAt.sub
        (continuousWithinAt_const.mul continuousWithinAt_id)
    · intro x hx
      have hx' := interior_subset hx
      have h1 := (hFd x hx').log (hF x hx').ne'
      have h2 := (hasDerivAt_id x).const_mul (2 * lam)
      refine ((h1.sub h2).congr_deriv ?_).hasDerivWithinAt
      have := (hF x hx').ne'
      field_simp
    · intro x hx
      have := hα x (interior_subset hx)
      linarith
  have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only at this
  have hfa := hF a ⟨le_rfl, hab⟩
  have hfb := hF b ⟨hab, le_rfl⟩
  have : Real.log (F a * Real.exp (2 * lam * (b - a))) ≤ Real.log (F b) := by
    rw [Real.log_mul hfa.ne' (Real.exp_pos _).ne', Real.log_exp]; linarith
  exact (Real.log_le_log_iff (by positivity) hfb).1 this

lemma growth_contra (F : ℝ → ℝ) (s2 lam C0 δ0 : ℝ) (hF : 0 < F s2) (hlam : δ0 < lam)
    (h : ∀ x ≥ s2, F s2 * Real.exp (2 * lam * (x - s2)) ≤ C0 * Real.exp (2 * δ0 * x)) : False := by
  have ht : Tendsto (fun x => F s2 * Real.exp (-(2 * lam * s2)) * Real.exp (2 * (lam - δ0) * x))
      atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))).const_mul_atTop
      (by positivity)
  obtain ⟨x, hx2, hx1⟩ := ((ht.eventually_gt_atTop C0).and (eventually_ge_atTop s2)).exists
  have := h x hx1
  have e : F s2 * Real.exp (2 * lam * (x - s2)) =
      F s2 * Real.exp (-(2 * lam * s2)) * Real.exp (2 * (lam - δ0) * x) * Real.exp (2 * δ0 * x) := by
    simp only [mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [e] at this
  have := le_of_mul_le_mul_right this (Real.exp_pos _)
  linarith


end HCWK

end AF_d2

section AF_g2

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HCWK

variable {n : ℕ}

section sol

variable {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n}

lemma Dz_sq_le (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) : Dz ζ s ^ 2 ≤ Fz ζ s * Gz ζ s :=
  cs_Ip' hζ.cont hζ.dS.cont hs

/-- lower bound for `∫ Qd` for a solution (`res A ζ = 0`) -/
lemma Qd_lower_sol (hA : Sm A) (hζ : Sm ζ) (hres : ∀ x ∈ Ω, res A ζ x = 0) {s : ℝ} (hs : 0 < s)
    (m1 m2 : ℝ) (hm1 : 0 ≤ m1)
    (hsym : ∀ t, ∀ v w : Vec n, |⟪A (s, t) v, w⟫ - ⟪v, A (s, t) w⟫| ≤ 2 * m1 * ‖v‖ * ‖w‖)
    (hdA : ∀ t, ‖pS A (s, t)‖ ≤ m2) :
    2 * Gz ζ s - 2 * m1 * Real.sqrt (Fz ζ s) * Real.sqrt (Gz ζ s) - m2 * Fz ζ s ≤
      ∫ t in (0:ℝ)..1, Qd A ζ (s, t) := by
  have hpres : ∀ x ∈ Ω, pS (res A ζ) x = 0 := by
    intro x hx
    rw [pS_congr (v := fun _ => (0 : Vec n)) hres hx]
    simp [pS]
  have hpt : ∀ t, 2 * ‖pS ζ (s, t)‖ ^ 2 - 2 * m1 * (‖ζ (s, t)‖ * ‖pS ζ (s, t)‖) - m2 * ‖ζ (s, t)‖ ^ 2 ≤
      Qd A ζ (s, t) := by
    intro t
    have hx : (s, t) ∈ Ω := mem_Ω hs
    simp only [Qd, hres _ hx, hpres _ hx, inner_zero_left, inner_zero_right, sub_zero, add_zero]
    have h1 := hsym t (ζ (s, t)) (pS ζ (s, t))
    have h2 : |⟪ζ (s, t), pS A (s, t) (ζ (s, t))⟫| ≤ m2 * ‖ζ (s, t)‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have := (pS A (s, t)).le_opNorm (ζ (s, t))
      have := mul_le_mul_of_nonneg_right (hdA t) (norm_nonneg (ζ (s, t)))
      nlinarith [norm_nonneg (ζ (s, t))]
    rw [real_inner_self_eq_norm_sq]
    have := neg_abs_le (⟪A (s, t) (ζ (s, t)), pS ζ (s, t)⟫ - ⟪ζ (s, t), A (s, t) (pS ζ (s, t))⟫)
    have := le_abs_self ⟪ζ (s, t), pS A (s, t) (ζ (s, t))⟫
    nlinarith
  have iξ : IntervalIntegrable (fun t => ‖pS ζ (s, t)‖ ^ 2) volume 0 1 :=
    ((cont_slice hζ.dS.cont hs).norm.pow 2).intervalIntegrable _ _
  have iζ : IntervalIntegrable (fun t => ‖ζ (s, t)‖ ^ 2) volume 0 1 :=
    ((cont_slice hζ.cont hs).norm.pow 2).intervalIntegrable _ _
  have im : IntervalIntegrable (fun t => ‖ζ (s, t)‖ * ‖pS ζ (s, t)‖) volume 0 1 :=
    ((cont_slice hζ.cont hs).norm.mul (cont_slice hζ.dS.cont hs).norm).intervalIntegrable _ _
  have hint := intervalIntegral.integral_mono_on zero_le_one
    (((iξ.const_mul 2).sub (im.const_mul (2 * m1))).sub (iζ.const_mul m2))
    (ii (Qd_cont hA hζ) hs) fun t _ => hpt t
  rw [intervalIntegral.integral_sub ((iξ.const_mul 2).sub (im.const_mul (2 * m1))) (iζ.const_mul m2),
    intervalIntegral.integral_sub (iξ.const_mul 2) (im.const_mul (2 * m1)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  have eG : Gz ζ s = ∫ t in (0:ℝ)..1, ‖pS ζ (s, t)‖ ^ 2 := by
    simp only [Gz, Ip, real_inner_self_eq_norm_sq]
  have eF : Fz ζ s = ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
    simp only [Fz, Ip, real_inner_self_eq_norm_sq]
  have hcs := cs_Ip hζ.cont hζ.dS.cont hs
  rw [← eG, ← eF] at hint
  have : 2 * m1 * (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ * ‖pS ζ (s, t)‖) ≤
      2 * m1 * (Real.sqrt (Fz ζ s) * Real.sqrt (Gz ζ s)) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  simp only [Fz, Gz] at this hint ⊢
  nlinarith

/-- `α' ≥ 2q - 2 m1 (√q + |α|) - m2` -/
lemma α1z_lower (hA : Sm A) (hζ : Sm ζ) (hres : ∀ x ∈ Ω, res A ζ x = 0) {s : ℝ} (hs : 0 < s)
    (hF : 0 < Fz ζ s) (m1 m2 : ℝ) (hm1 : 0 ≤ m1)
    (hsym : ∀ t, ∀ v w : Vec n, |⟪A (s, t) v, w⟫ - ⟪v, A (s, t) w⟫| ≤ 2 * m1 * ‖v‖ * ‖w‖)
    (hdA : ∀ t, ‖pS A (s, t)‖ ≤ m2) :
    2 * qz ζ s - 2 * m1 * (Real.sqrt (qz ζ s) + |αz ζ s|) - m2 ≤ α1z A ζ s := by
  have := alpha_ineq (Fz ζ s) (Dz ζ s) (Gz ζ s) (∫ t in (0:ℝ)..1, Qd A ζ (s, t)) m1 m2 hF hm1
    (Dz_sq_le hζ hs) (Qd_lower_sol hA hζ hres hs m1 m2 hm1 hsym hdA)
  simpa [qz, αz, α1z] using this

lemma qz_nonneg (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) : 0 ≤ qz ζ s := by
  have h := Dz_sq_le hζ hs
  simp only [qz, αz]
  rw [div_pow, sub_nonneg, div_le_div_iff₀ (by positivity) hF]
  nlinarith

/-- the symmetry defect of `A` is controlled by the distance to a symmetric matrix -/
lemma sym_defect (T : Op n) (M : Mat n) (hM : M.IsSymm) (v w : Vec n) :
    |⟪T v, w⟫ - ⟪v, T w⟫| ≤ 2 * ‖T - TL n M‖ * ‖v‖ * ‖w‖ := by
  have e : ⟪T v, w⟫ - ⟪v, T w⟫ = ⟪(T - TL n M) v, w⟫ - ⟪v, (T - TL n M) w⟫ := by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, inner_symm hM]
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have h1 := abs_inner_op (T - TL n M) v w
  have h2 : |⟪v, (T - TL n M) w⟫| ≤ ‖T - TL n M‖ * ‖w‖ * ‖v‖ := by
    rw [real_inner_comm]; exact abs_inner_op _ w v
  nlinarith

lemma sym_defect' (T : Op n) (v w : Vec n) :
    |⟪T v, w⟫ - ⟪v, T w⟫| ≤ 2 * ‖T‖ * ‖v‖ * ‖w‖ := by
  have := sym_defect T 0 (by simp [Matrix.IsSymm]) v w
  simpa using this

end sol

end HCWK

end AF_g2

section AF_h

/-! Unique continuation: `‖ζ(s)‖_{L²} > 0` for all `s ≥ s₀` once it is positive at `s₀`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HCWK

variable {n : ℕ}

lemma per_int_pos (g : ℝ → ℝ) (hg : Continuous g) (hp : Function.Periodic g 1)
    (hnn : ∀ t, 0 ≤ g t) (t0 : ℝ) (h : 0 < g t0) : 0 < ∫ t in (0:ℝ)..1, g t := by
  have e := hp.intervalIntegral_add_eq (t0 - 1 / 2) 0
  rw [zero_add] at e
  rw [← e]
  obtain ⟨δ, hδ, hδg⟩ := Metric.eventually_nhds_iff.1 (hg.continuousAt.eventually (lt_mem_nhds h))
  set δ' := min δ (1 / 2)
  have hδ' : 0 < δ' := by positivity
  have h1 : 0 < ∫ t in (t0 - δ')..(t0 + δ'), g t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable _ _) ?_ (by linarith)
    intro x hx
    apply hδg
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2, min_le_left δ (1 / 2)]
  refine lt_of_lt_of_le h1 (intervalIntegral.integral_mono_interval ?_ (by linarith) ?_
    (Eventually.of_forall hnn) (hg.intervalIntegrable _ _))
  · linarith [min_le_right δ (1 / 2)]
  · linarith [min_le_right δ (1 / 2)]

lemma Fz_pos_of_ne {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (hpζ : TPer ζ) {s t : ℝ} (hs : 0 < s)
    (h : ζ (s, t) ≠ 0) : 0 < Fz ζ s := by
  have e : Fz ζ s = ∫ τ in (0:ℝ)..1, ‖ζ (s, τ)‖ ^ 2 := by
    simp only [Fz, Ip, real_inner_self_eq_norm_sq]
  rw [e]
  exact per_int_pos _ ((cont_slice hζ.cont hs).norm.pow 2) (fun τ => by simp [hpζ s τ])
    (fun _ => by positivity) t (by have := norm_pos_iff.2 h; positivity)

/-- sup bound of a `t`-periodic map continuous on `Ω` over `[a, b] × ℝ` -/
lemma bound_strip {F : Type*} [NormedAddCommGroup F] {u : ℝ × ℝ → F} (hu : ContinuousOn u Ω)
    (hpu : ∀ s t, u (s, t + 1) = u (s, t)) {a b : ℝ} (ha : 0 < a) :
    ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc a b, ∀ t, ‖u (s, t)‖ ≤ M := by
  have hK : IsCompact (Icc a b ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hKΩ : Icc a b ×ˢ Icc (0:ℝ) 1 ⊆ Ω := fun x hx => ⟨lt_of_lt_of_le ha hx.1.1, trivial⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hu.mono hKΩ)
  refine ⟨max M 0, le_max_right _ _, fun s hs t => ?_⟩
  have hper : Function.Periodic (fun t => u (s, t)) 1 := fun t => hpu s t
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico₀ zero_lt_one t
  rw [show u (s, t) = u (s, y) from hyt]
  exact (hM (s, y) ⟨hs, Ico_subset_Icc_self hy⟩).trans (le_max_left _ _)

/-- unique continuation forward in `s` -/
theorem Fz_pos_forward {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ)
    (hpA : TPer A) (hpζ : TPer ζ) (hres : ∀ x ∈ Ω, res A ζ x = 0) {p : ℝ} (hp0 : 0 < p)
    (hp : 0 < Fz ζ p) : ∀ s ≥ p, 0 < Fz ζ s := by
  intro b hb
  obtain ⟨m1, hm1, hm1b⟩ := bound_strip (u := A) hA.cont hpA (a := p) (b := b) hp0
  obtain ⟨m2, hm2, hm2b⟩ := bound_strip (u := pS A) hA.dS.cont hpA.pS (a := p) (b := b) hp0
  have := pos_forward (Fz ζ) (αz ζ) (α1z A ζ) p b (m1 ^ 2 / 2 + m2 + 2 * m1) (by positivity)
    ((Fz_cont hζ).mono (fun x hx => lt_of_lt_of_le hp0 hx.1))
    hp
    (fun s hs hF => Fz_hasDerivAt' hζ (lt_of_lt_of_le hp0 hs.1) hF)
    (fun s hs hF => αz_hasDerivAt hA hζ hpA hpζ (lt_of_lt_of_le hp0 hs.1) hF)
    (fun s hs hF => by
      have hs0 := lt_of_lt_of_le hp0 hs.1
      have h1 := α1z_lower hA hζ hres hs0 hF m1 m2 hm1
        (fun t v w => (sym_defect' _ v w).trans (by
          have := hm1b s hs t
          have h0 : 0 ≤ ‖v‖ * ‖w‖ := by positivity
          nlinarith))
        (fun t => hm2b s hs t)
      have hq := qz_nonneg hζ hs0 hF
      have : 2 * m1 * Real.sqrt (qz ζ s) ≤ 2 * qz ζ s + m1 ^ 2 / 2 := by
        nlinarith [sq_nonneg (2 * Real.sqrt (qz ζ s) - m1), Real.sq_sqrt hq, Real.sqrt_nonneg (qz ζ s)]
      nlinarith [abs_nonneg (αz ζ s)])
    b ⟨hb, le_rfl⟩
  exact this

end HCWK

end AF_h

/-! The differential inequality for the slice Rayleigh quotient without an `|α|` term,
coefficient smallness from `C^∞` convergence, and a one-variable integration lemma. -/

set_option linter.all false


namespace HCWK

variable {n : ℕ}

lemma int_lin3 (f g h : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (x y z : ℝ) : ∫ t in (0:ℝ)..1, (x * f t + y * g t + z * h t) =
      x * (∫ t in (0:ℝ)..1, f t) + y * (∫ t in (0:ℝ)..1, g t) + z * ∫ t in (0:ℝ)..1, h t := by
  rw [intervalIntegral.integral_add (f := fun t => x * f t + y * g t) (g := fun t => z * h t)
    (((continuous_const.mul hf).add (continuous_const.mul hg)).intervalIntegrable _ _)
    ((continuous_const.mul hh).intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun t => x * f t) (g := fun t => y * g t)
    ((continuous_const.mul hf).intervalIntegrable _ _)
    ((continuous_const.mul hg).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul]

/-- `S → S∞` in `C^∞` makes `A - S∞` and `∂ₛA` uniformly small. -/
theorem coeff_small (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : FiniteEnergyPlane.IsCInftyAsymptoticTo S Sinf) :
    ∀ ε > 0, ∃ s1 : ℝ, ∀ s ≥ s1, ∀ t, ‖TL n (S (s, t)) - TL n (Sinf t)‖ ≤ ε ∧
      ‖pS (fun p => TL n (S p)) (s, t)‖ ≤ ε := by
  intro ε hε
  obtain ⟨c, hc, hcM⟩ := op_small (n := n)
  have h : ∀ i j (m : ℕ), ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) (s, t)‖ ≤ ε / c :=
    fun i j m => (hSas i j).2 m (ε / c) (by positivity)
  choose s1f hs1f using h
  set s1 := ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1|)
  have hle : ∀ i j, s1f i j 0 ≤ s1 ∧ s1f i j 1 ≤ s1 := by
    intro i j
    have h1 : |s1f i j 0| + |s1f i j 1| ≤ s1 := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, (|s1f i j 0| + |s1f i j 1|))
        (fun i _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => |s1f i j 0| + |s1f i j 1|)
        (fun j _ => by positivity) (Finset.mem_univ j)
    have := le_abs_self (s1f i j 0); have := le_abs_self (s1f i j 1)
    have := abs_nonneg (s1f i j 0); have := abs_nonneg (s1f i j 1)
    exact ⟨by linarith, by linarith⟩
  have hcε : c * (ε / c) = ε := by field_simp
  refine ⟨s1, fun s hs t => ⟨?_, ?_⟩⟩
  · rw [← map_sub, ← hcε]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 0 s ((hle i j).1.trans hs) t
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    simpa only [Matrix.sub_apply] using this
  · rw [hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)), ← hcε]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 1 s ((hle i j).2.trans hs) t
    simp only [Matrix.of_apply, pS_entry S hS Sinf hSinf']
    exact (pS_le0 _ _).trans this

lemma inner_defect_shift (T : Op n) (v w : Vec n) (a : ℝ) :
    ⟪T v, w⟫ - ⟪v, T w⟫ = ⟪T v, w - a • v⟫ - ⟪v, T (w - a • v)⟫ := by
  have e := real_inner_comm (T v) v
  simp only [inner_sub_right, map_sub, map_smul, real_inner_smul_right]
  rw [e]; ring

lemma norm_sub_smul_sq (ξ ζ : Vec n) (a : ℝ) :
    ‖ξ - a • ζ‖ ^ 2 = ‖ξ‖ ^ 2 - 2 * a * ⟪ζ, ξ⟫ + a ^ 2 * ‖ζ‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_comm]
  ring

section sol

variable {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n}

lemma int_sub_smul_sq (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (a : ℝ) :
    ∫ t in (0:ℝ)..1, ‖pS ζ (s, t) - a • ζ (s, t)‖ ^ 2 =
      Gz ζ s - 2 * a * Dz ζ s + a ^ 2 * Fz ζ s := by
  have c1 := cont_slice hζ.cont hs
  have c2 := cont_slice hζ.dS.cont hs
  have e : (fun t => ‖pS ζ (s, t) - a • ζ (s, t)‖ ^ 2) = fun t =>
      1 * ‖pS ζ (s, t)‖ ^ 2 + (-(2 * a)) * ⟪ζ (s, t), pS ζ (s, t)⟫ + a ^ 2 * ‖ζ (s, t)‖ ^ 2 := by
    funext t; rw [norm_sub_smul_sq]; ring
  have h3 := int_lin3 (fun t => ‖pS ζ (s, t)‖ ^ 2) (fun t => ⟪ζ (s, t), pS ζ (s, t)⟫)
    (fun t => ‖ζ (s, t)‖ ^ 2) (c2.norm.pow 2) (c1.inner c2) (c1.norm.pow 2) 1 (-(2 * a)) (a ^ 2)
  rw [e]
  refine h3.trans ?_
  simp only [Gz, Dz, Fz, Ip, real_inner_self_eq_norm_sq]
  ring

/-- `α' ≥ 2q - 2 m1 √q - m2`, with no `|α|` term. -/
lemma α1z_lower' (hA : Sm A) (hζ : Sm ζ) (hres : ∀ x ∈ Ω, res A ζ x = 0) {s : ℝ} (hs : 0 < s)
    (hF : 0 < Fz ζ s) (m1 m2 : ℝ) (hm1 : 0 ≤ m1)
    (hsym : ∀ t, ∀ v w : Vec n, |⟪A (s, t) v, w⟫ - ⟪v, A (s, t) w⟫| ≤ 2 * m1 * ‖v‖ * ‖w‖)
    (hdA : ∀ t, ‖pS A (s, t)‖ ≤ m2) :
    2 * qz ζ s - 2 * m1 * Real.sqrt (qz ζ s) - m2 ≤ α1z A ζ s := by
  set α := αz ζ s
  have hpres : ∀ x ∈ Ω, pS (res A ζ) x = 0 := by
    intro x hx
    rw [pS_congr (v := fun _ => (0 : Vec n)) hres hx]
    simp [pS]
  have hpt : ∀ t, 2 * ‖pS ζ (s, t)‖ ^ 2 -
      2 * m1 * (‖ζ (s, t)‖ * ‖pS ζ (s, t) - α • ζ (s, t)‖) - m2 * ‖ζ (s, t)‖ ^ 2 ≤
      Qd A ζ (s, t) := by
    intro t
    have hx : (s, t) ∈ Ω := mem_Ω hs
    simp only [Qd, hres _ hx, hpres _ hx, inner_zero_left, inner_zero_right, sub_zero, add_zero]
    have h1 := hsym t (ζ (s, t)) (pS ζ (s, t) - α • ζ (s, t))
    rw [← inner_defect_shift] at h1
    have h2 : |⟪ζ (s, t), pS A (s, t) (ζ (s, t))⟫| ≤ m2 * ‖ζ (s, t)‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have := (pS A (s, t)).le_opNorm (ζ (s, t))
      have := mul_le_mul_of_nonneg_right (hdA t) (norm_nonneg (ζ (s, t)))
      nlinarith [norm_nonneg (ζ (s, t))]
    rw [real_inner_self_eq_norm_sq]
    have := neg_abs_le (⟪A (s, t) (ζ (s, t)), pS ζ (s, t)⟫ - ⟪ζ (s, t), A (s, t) (pS ζ (s, t))⟫)
    have := le_abs_self ⟪ζ (s, t), pS A (s, t) (ζ (s, t))⟫
    nlinarith
  have c1 := cont_slice hζ.cont hs
  have c2 := cont_slice hζ.dS.cont hs
  have c3 : Continuous fun t => pS ζ (s, t) - α • ζ (s, t) := c2.sub (c1.const_smul α)
  have iξ : IntervalIntegrable (fun t => ‖pS ζ (s, t)‖ ^ 2) volume 0 1 :=
    (c2.norm.pow 2).intervalIntegrable _ _
  have iζ : IntervalIntegrable (fun t => ‖ζ (s, t)‖ ^ 2) volume 0 1 :=
    (c1.norm.pow 2).intervalIntegrable _ _
  have im : IntervalIntegrable (fun t => ‖ζ (s, t)‖ * ‖pS ζ (s, t) - α • ζ (s, t)‖) volume 0 1 :=
    (c1.norm.mul c3.norm).intervalIntegrable _ _
  have hint := intervalIntegral.integral_mono_on zero_le_one
    (((iξ.const_mul 2).sub (im.const_mul (2 * m1))).sub (iζ.const_mul m2))
    (ii (Qd_cont hA hζ) hs) fun t _ => hpt t
  rw [intervalIntegral.integral_sub ((iξ.const_mul 2).sub (im.const_mul (2 * m1))) (iζ.const_mul m2),
    intervalIntegral.integral_sub (iξ.const_mul 2) (im.const_mul (2 * m1)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  have eG : Gz ζ s = ∫ t in (0:ℝ)..1, ‖pS ζ (s, t)‖ ^ 2 := by
    simp only [Gz, Ip, real_inner_self_eq_norm_sq]
  have eF : Fz ζ s = ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
    simp only [Fz, Ip, real_inner_self_eq_norm_sq]
  rw [← eG, ← eF] at hint
  -- Cauchy–Schwarz and `∫ |ξ - α ζ|² = q F`
  have hcs := cs_real _ _ c1.norm c3.norm
  have hE := int_sub_smul_sq hζ hs α
  have hqF : Gz ζ s - 2 * α * Dz ζ s + α ^ 2 * Fz ζ s = qz ζ s * Fz ζ s := by
    simp only [qz, α, αz]; field_simp; ring
  rw [hE, hqF, ← eF] at hcs
  have hq := qz_nonneg hζ hs hF
  set X := ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ * ‖pS ζ (s, t) - α • ζ (s, t)‖
  have hX0 : 0 ≤ X := intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity
  have hXle : X ≤ Fz ζ s * Real.sqrt (qz ζ s) := by
    have h0 : 0 ≤ Fz ζ s * Real.sqrt (qz ζ s) := by positivity
    have : X ^ 2 ≤ (Fz ζ s * Real.sqrt (qz ζ s)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hq]; nlinarith
    nlinarith
  have hQ : 2 * Gz ζ s - 2 * m1 * (Fz ζ s * Real.sqrt (qz ζ s)) - m2 * Fz ζ s ≤
      ∫ t in (0:ℝ)..1, Qd A ζ (s, t) := by
    have := mul_le_mul_of_nonneg_left hXle (by linarith : 0 ≤ 2 * m1)
    linarith
  -- divide by `F`
  simp only [α1z]
  rw [le_sub_iff_add_le, le_div_iff₀ hF]
  have eq : (2 * qz ζ s - 2 * m1 * Real.sqrt (qz ζ s) - m2 + 2 * αz ζ s ^ 2) * Fz ζ s =
      2 * Gz ζ s - 2 * m1 * (Fz ζ s * Real.sqrt (qz ζ s)) - m2 * Fz ζ s := by
    simp only [qz]; field_simp; ring
  rw [eq]; exact hQ

end sol

/-- If `α' ≥ q - K` on `[a, ∞)` with `q` continuous there, then `∫ₐ^{a+1} q ≤ α(a+1) - α(a) + K`. -/
lemma integral_le_of_deriv_ge (α α' q : ℝ → ℝ) (a b K : ℝ) (hba : b < a)
    (hd : ∀ x ≥ a, HasDerivAt α (α' x) x)
    (hq : ∀ x ∈ Ioi b, ContinuousAt q x) (hge : ∀ x ≥ a, q x - K ≤ α' x) :
    ∫ x in a..a + 1, q x ≤ α (a + 1) - α a + K := by
  have hqm := ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi hq
  have hqi : ∀ x ≥ a, IntervalIntegrable q volume a x := fun x hx =>
    ContinuousOn.intervalIntegrable fun y hy => by
      rw [uIcc_of_le hx] at hy
      exact (hq y (lt_of_lt_of_le hba hy.1)).continuousWithinAt
  set g : ℝ → ℝ := fun x => α x - (∫ y in a..x, q y) + K * x
  have hg : ∀ x ≥ a, HasDerivAt g (α' x - q x + K) x := by
    intro x hx
    have hxb : x ∈ Ioi b := lt_of_lt_of_le hba hx
    have h1 : HasDerivAt (fun x => ∫ y in a..x, q y) (q x) x :=
      intervalIntegral.integral_hasDerivAt_right (hqi x hx) (hqm x hxb) (hq x hxb)
    exact ((hd x hx).sub h1).add ((hasDerivAt_id' x).const_mul K) |>.congr_deriv (by ring)
  have hm := mono_Ici g _ a hg (fun x hx => by linarith [hge x hx])
  have := hm (Set.mem_Ici.2 le_rfl) (show a ≤ a + 1 by linarith) (by linarith)
  simp only [g, intervalIntegral.integral_same] at this
  linarith

end HCWK

namespace FiniteEnergyPlane

open HCWK

theorem halfCyl_exists_tendsto_rayleigh_aux {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ > 0, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      Tendsto (fun s : ℝ => (∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫) /
        (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)) atTop (𝓝 μ) ∧
      Tendsto (fun s : ℝ => ∫ x in s..s + 1,
        ((∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (x, t) (1, 0)‖ ^ 2) / (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2) -
          ((∫ t in (0:ℝ)..1, ⟪ζ (x, t), fderiv ℝ ζ (x, t) (1, 0)⟫) /
            (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2)) ^ 2)) atTop (𝓝 0) := by
  set A : ℝ × ℝ → Op n := fun p => TL n (S p)
  have hA : Sm A := (contDiff_TL S hS).contDiffOn
  have hpA : TPer A := fun s t => by simp only [A, hSper s t]
  have hζs : Sm ζ := hζ.1
  have hpζ : TPer ζ := hζ.2.1
  have hres0 : ∀ x ∈ Ω, res A ζ x = 0 := by
    rintro ⟨a, b⟩ hx
    exact hζ.2.2 a hx.1 b
  obtain ⟨⟨p1, p2⟩, hp1, hp⟩ := hne
  simp only at hp1
  have hFp := Fz_pos_of_ne hζs hpζ hp1 hp
  have hFpos := Fz_pos_forward hA hζs hpA hpζ hres0 hp1 hFp
  have hsmall := coeff_small S hS Sinf hSinf' hSas
  have hαd : ∀ s ≥ p1, HasDerivAt (αz ζ) (α1z A ζ s) s := fun s hs =>
    αz_hasDerivAt hA hζs hpA hpζ (lt_of_lt_of_le hp1 hs) (hFpos s hs)
  have hqc : ∀ s ≥ p1, ContinuousAt (qz ζ) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hp1 hs
    have hcF := (Fz_cont hζs).continuousAt (isOpen_Ioi.mem_nhds hs0)
    have hcG := (Gz_cont hζs).continuousAt (isOpen_Ioi.mem_nhds hs0)
    have hcD := (Dz_cont hζs).continuousAt (isOpen_Ioi.mem_nhds hs0)
    have hF0 := (hFpos s hs).ne'
    exact (hcG.div hcF hF0).sub ((hcD.div hcF hF0).pow 2)
  -- `α' ≥ 2q - 2ε√q - ε` for large `s`
  have hlow : ∀ ε > 0, ∃ s1 ≥ p1, ∀ s ≥ s1,
      2 * qz ζ s - 2 * ε * Real.sqrt (qz ζ s) - ε ≤ α1z A ζ s := by
    intro ε hε
    obtain ⟨s1, hs1⟩ := hsmall ε hε
    refine ⟨max s1 p1, le_max_right _ _, fun s hs => ?_⟩
    have hsp : p1 ≤ s := (le_max_right _ _).trans hs
    have hs0 : 0 < s := lt_of_lt_of_le hp1 hsp
    have hb := fun t => hs1 s ((le_max_left _ _).trans hs) t
    exact α1z_lower' hA hζs hres0 hs0 (hFpos s hsp) ε ε hε.le
      (fun t v w => (sym_defect _ _ (hSinf.2.2 t) v w).trans (by
        have := mul_le_mul_of_nonneg_right (hb t).1 (by positivity : 0 ≤ ‖v‖ * ‖w‖)
        nlinarith))
      (fun t => (hb t).2)
  -- levels that can only be crossed upward
  have hlev : ∀ δ > 0, ∃ S' : ℝ, ∀ a : ℝ, ∃ l ∈ Set.Icc a (a + δ), ∀ s ≥ S',
      αz ζ s = l → 0 < α1z A ζ s := by
    intro δ hδ
    obtain ⟨c, hc, hgap⟩ := exists_uniform_loop_gap Sinf hSinf δ hδ
    set ε := min 1 (c / 8)
    have hε : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεc : ε ≤ c / 8 := min_le_right _ _
    obtain ⟨s1, hs1⟩ := hsmall ε hε
    obtain ⟨s2, hs2p, hs2⟩ := hlow ε hε
    refine ⟨max s1 s2, fun a => ?_⟩
    obtain ⟨l, hl, hgl⟩ := hgap a
    refine ⟨l, hl, fun s hs hαl => ?_⟩
    have hsp : p1 ≤ s := hs2p.trans ((le_max_right _ _).trans hs)
    have hs0 : 0 < s := lt_of_lt_of_le hp1 hsp
    have hF := hFpos s hsp
    have hq := qz_nonneg hζs hs0 hF
    have cζ := cont_slice hζs.cont hs0
    have cξ := cont_slice hζs.dS.cont hs0
    have cA := cont_slice hA.cont hs0
    have cS : Continuous fun t => TL n (Sinf t) := (TL n).continuous.comp hSinf.1
    have hg := hgl (fun t => ζ (s, t)) (fun t => pT ζ (s, t)) (fun t => hζs.hasDerivAt_t hs0)
      (cont_slice hζs.dT.cont hs0) (fun t => hpζ s t)
    have e : ∀ t, -(Matrix.toEuclideanLin (J₀ n) (pT ζ (s, t))) -
        Matrix.toEuclideanLin (Sinf t) (ζ (s, t)) - l • ζ (s, t) =
        (pS ζ (s, t) - l • ζ (s, t)) + (A (s, t) - TL n (Sinf t)) (ζ (s, t)) := by
      intro t
      have hr := hres0 (s, t) (mem_Ω hs0)
      simp only [res] at hr
      have h1 := eq_neg_of_add_eq_zero_left hr
      have h2 := eq_sub_of_add_eq' h1
      show -(Jop n (pT ζ (s, t))) - TL n (Sinf t) (ζ (s, t)) - l • ζ (s, t) = _
      rw [h2, ContinuousLinearMap.sub_apply]
      abel
    simp only [e] at hg
    have hpt : ∀ t, ‖(pS ζ (s, t) - l • ζ (s, t)) + (A (s, t) - TL n (Sinf t)) (ζ (s, t))‖ ^ 2 ≤
        2 * ‖pS ζ (s, t) - l • ζ (s, t)‖ ^ 2 + (2 * ε ^ 2) * ‖ζ (s, t)‖ ^ 2 := by
      intro t
      have h1 := norm_add_le (pS ζ (s, t) - l • ζ (s, t)) ((A (s, t) - TL n (Sinf t)) (ζ (s, t)))
      have h2 := (A (s, t) - TL n (Sinf t)).le_opNorm (ζ (s, t))
      have h3 := mul_le_mul_of_nonneg_right (hs1 s ((le_max_left _ _).trans hs) t).1
        (norm_nonneg (ζ (s, t)))
      have h4 := norm_nonneg ((A (s, t) - TL n (Sinf t)) (ζ (s, t)))
      have h5 := norm_nonneg (pS ζ (s, t) - l • ζ (s, t))
      have h6 : ‖(A (s, t) - TL n (Sinf t)) (ζ (s, t))‖ ≤ ε * ‖ζ (s, t)‖ := h2.trans h3
      have hN2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hy2 := pow_le_pow_left₀ h4 h6 2
      rw [mul_pow] at hy2
      nlinarith [sq_nonneg (‖pS ζ (s, t) - l • ζ (s, t)‖ - ‖(A (s, t) - TL n (Sinf t)) (ζ (s, t))‖)]
    have c1 : Continuous fun t => ‖(pS ζ (s, t) - l • ζ (s, t)) +
        (A (s, t) - TL n (Sinf t)) (ζ (s, t))‖ ^ 2 :=
      (((cξ.sub (cζ.const_smul l)).add ((cA.sub cS).clm_apply cζ)).norm.pow 2)
    have c2 : Continuous fun t => ‖pS ζ (s, t) - l • ζ (s, t)‖ ^ 2 :=
      ((cξ.sub (cζ.const_smul l)).norm.pow 2)
    have c3 : Continuous fun t => ‖ζ (s, t)‖ ^ 2 := cζ.norm.pow 2
    have hint := intervalIntegral.integral_mono_on zero_le_one (c1.intervalIntegrable (μ := volume) 0 1)
      (((c2.intervalIntegrable 0 1).const_mul 2).add ((c3.intervalIntegrable 0 1).const_mul _))
      fun t _ => hpt t
    rw [intervalIntegral.integral_add ((c2.intervalIntegrable 0 1).const_mul 2)
      ((c3.intervalIntegrable 0 1).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hint
    have eF : Fz ζ s = ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
      simp only [Fz, Ip, real_inner_self_eq_norm_sq]
    rw [← eF] at hint hg
    subst hαl
    rw [int_sub_smul_sq hζs hs0] at hint
    have hqF : Gz ζ s - 2 * αz ζ s * Dz ζ s + αz ζ s ^ 2 * Fz ζ s = qz ζ s * Fz ζ s := by
      simp only [qz, αz]; field_simp; ring
    rw [hqF] at hint
    -- `c ≤ 2 q + 2 ε²`
    have hcq : c ≤ 2 * qz ζ s + 2 * ε ^ 2 := by
      have := hg.trans hint
      have h' : c * Fz ζ s ≤ (2 * qz ζ s + 2 * ε ^ 2) * Fz ζ s := by linarith
      exact le_of_mul_le_mul_right h' hF
    have h1 := hs2 s ((le_max_right _ _).trans hs)
    have h2 : 2 * ε * Real.sqrt (qz ζ s) ≤ qz ζ s + ε ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (qz ζ s) - ε), Real.sq_sqrt hq]
    nlinarith
  -- the growth bound keeps `α` frequently below every level above `δ₀`
  have hFb : ∀ x > 0, Fz ζ x ≤ C ^ 2 * Real.exp (2 * δ₀ * x) := by
    intro s hs0
    have e : Fz ζ s = ∫ τ in (0:ℝ)..1, ‖ζ (s, τ)‖ ^ 2 := by
      simp only [Fz, Ip, real_inner_self_eq_norm_sq]
    rw [e]
    have hb : ∀ τ, ‖ζ (s, τ)‖ ^ 2 ≤ C ^ 2 * Real.exp (2 * δ₀ * s) := by
      intro τ
      have h1 := hgrowth s hs0 τ
      have h2 := norm_nonneg (ζ (s, τ))
      have : C ^ 2 * Real.exp (2 * δ₀ * s) = (C * Real.exp (δ₀ * s)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
      rw [this]
      exact pow_le_pow_left₀ h2 h1 2
    calc ∫ τ in (0:ℝ)..1, ‖ζ (s, τ)‖ ^ 2 ≤ ∫ τ in (0:ℝ)..1, C ^ 2 * Real.exp (2 * δ₀ * s) :=
          intervalIntegral.integral_mono_on zero_le_one
            (((cont_slice hζs.cont hs0).norm.pow 2).intervalIntegrable _ _)
            intervalIntegrable_const fun τ _ => hb τ
      _ = C ^ 2 * Real.exp (2 * δ₀ * s) := by simp
  have hup : ∀ μ > δ₀, ∃ᶠ s in atTop, αz ζ s < μ := by
    intro μ hμ
    by_contra h
    rw [not_frequently] at h
    obtain ⟨s2', hs2'⟩ := eventually_atTop.1 h
    set s2 := max s2' p1
    have hs2p : p1 ≤ s2 := le_max_right _ _
    refine growth_contra (Fz ζ) s2 μ (C ^ 2) δ₀ (hFpos s2 hs2p) hμ fun x hx => ?_
    have hx' : p1 ≤ x := hs2p.trans hx
    refine (F_lower (Fz ζ) (αz ζ) s2 x μ hx (fun y hy => hFpos y (hs2p.trans hy.1))
      (fun y hy => Fz_hasDerivAt' hζs (lt_of_lt_of_le hp1 (hs2p.trans hy.1))
        (hFpos y (hs2p.trans hy.1)))
      (fun y hy => not_lt.1 (hs2' y ((le_max_left _ _).trans hy.1)))).trans ?_
    exact hFb x (lt_of_lt_of_le hp1 hx')
  obtain ⟨μ, hμ, hlim⟩ := exists_tendsto_of_upcrossing_levels (αz ζ) (α1z A ζ) p1 δ₀ hαd hlev hup
  refine ⟨μ, hμ, p1, hp1, fun s hs => ?_, ?_, ?_⟩
  · simpa only [Fz, Ip, real_inner_self_eq_norm_sq] using hFpos s hs
  · have e : (fun s : ℝ => (∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫) /
        (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)) = αz ζ := by
      funext s; simp only [αz, Dz, Fz, Ip, pS, real_inner_self_eq_norm_sq]
    rw [e]; exact hlim
  · -- `∫ₛ^{s+1} q → 0`
    have hq0 : Tendsto (fun s => ∫ x in s..s + 1, qz ζ x) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set ε' := min 1 (ε / 4)
      have hε' : 0 < ε' := by positivity
      have hε'1 : ε' ≤ 1 := min_le_left _ _
      have hε'2 : ε' ≤ ε / 4 := min_le_right _ _
      obtain ⟨s1, hs1p, hs1⟩ := hlow ε' hε'
      have hdiff : Tendsto (fun s => αz ζ (s + 1) - αz ζ s) atTop (𝓝 0) := by
        have := (hlim.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).sub hlim
        simpa using this
      obtain ⟨s3, hs3⟩ := Metric.tendsto_atTop.1 hdiff (ε / 2) (by positivity)
      refine ⟨max (max s1 s3) (p1 + 1), fun s hs => ?_⟩
      have hs1s : s1 ≤ s := (le_max_left _ _).trans ((le_max_left _ _).trans hs)
      have hp1s : p1 < s := by linarith [(le_max_right _ _).trans hs]
      have hps : p1 ≤ s := hs1p.trans hs1s
      have hup' := integral_le_of_deriv_ge (αz ζ) (α1z A ζ) (qz ζ) s p1 (ε' ^ 2 + ε') hp1s
        (fun x hx => hαd x (hps.trans hx)) (fun x hx => hqc x (le_of_lt hx)) (fun x hx => by
          have h1 := hs1 x (hs1s.trans hx)
          have hq := qz_nonneg hζs (lt_of_lt_of_le hp1 (hps.trans hx)) (hFpos x (hps.trans hx))
          have h2 : 2 * ε' * Real.sqrt (qz ζ x) ≤ qz ζ x + ε' ^ 2 := by
            nlinarith [sq_nonneg (Real.sqrt (qz ζ x) - ε'), Real.sq_sqrt hq]
          linarith)
      have hlo : 0 ≤ ∫ x in s..s + 1, qz ζ x :=
        intervalIntegral.integral_nonneg (by linarith) fun x hx =>
          qz_nonneg hζs (lt_of_lt_of_le hp1 (hps.trans hx.1)) (hFpos x (hps.trans hx.1))
      have h3 := hs3 s ((le_max_right _ _).trans ((le_max_left _ _).trans hs))
      rw [Real.dist_eq, sub_zero] at h3 ⊢
      rw [abs_of_nonneg hlo]
      have := (abs_lt.1 h3).2
      have : ε' ^ 2 ≤ ε' := by nlinarith
      linarith
    refine hq0.congr' (Eventually.of_forall fun s => ?_)
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [qz, Gz, αz, Dz, Fz, Ip, pS, real_inner_self_eq_norm_sq]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real RealInnerProductSpace

theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ > 0, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      Tendsto (fun s : ℝ => (∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫) /
        (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)) atTop (𝓝 μ) ∧
      Tendsto (fun s : ℝ => ∫ x in s..s + 1,
        ((∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (x, t) (1, 0)‖ ^ 2) / (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2) -
          ((∫ t in (0:ℝ)..1, ⟪ζ (x, t), fderiv ℝ ζ (x, t) (1, 0)⟫) /
            (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2)) ^ 2)) atTop (𝓝 0) :=
  halfCyl_exists_tendsto_rayleigh_aux S hS hSper Sinf hSinf hSinf' hSas ζ hζ hne C δ₀ hgrowth
