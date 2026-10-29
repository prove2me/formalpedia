-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_slice_deriv_sq_le_of_logDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T22:46:48.483696+00:00
-- url     : https://prove2.me/submissions/213f3425-840c-42cc-9c58-90ada1257335

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_le_exp_mul_of_abs_deriv_le
import Theorems.Thm_FiniteEnergyPlane_le_add_of_deriv_two_ge

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

/-! Slice derivative bound for a linear Cauchy–Riemann solution on a half-cylinder whose
`L²` logarithmic growth rate is bounded. -/


namespace HCWK

variable {n : ℕ}

lemma Jop_Jop (v : Vec n) : Jop n (Jop n v) = -v := by
  show (Matrix.toEuclideanCLM (𝕜 := ℝ) (J₀ n)) ((Matrix.toEuclideanCLM (𝕜 := ℝ) (J₀ n)) v) = -v
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _,
    map_neg, map_one]
  rfl

lemma Qd_ge (A : ℝ × ℝ → Op n) (η : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    2 * ‖pS η x‖ ^ 2 - 2 * (‖A x‖ * ‖η x‖ * ‖pS η x‖) - ‖res A η x‖ * ‖pS η x‖ -
      ‖η x‖ * ‖pS (res A η) x‖ - ‖pS A x‖ * ‖η x‖ * ‖η x‖ ≤ Qd A η x := by
  unfold Qd
  rw [real_inner_self_eq_norm_sq]
  have h1 := abs_inner_op (A x) (η x) (pS η x)
  have h2 := abs_inner_op (A x) (pS η x) (η x)
  rw [real_inner_comm] at h2
  have h3 := abs_real_inner_le_norm (res A η x) (pS η x)
  have h4 := abs_real_inner_le_norm (η x) (pS (res A η) x)
  have h5 := abs_inner_op (pS A x) (η x) (η x)
  rw [real_inner_comm] at h5
  have := neg_abs_le ⟪A x (η x), pS η x⟫
  have := le_abs_self ⟪η x, A x (pS η x)⟫
  have := le_abs_self ⟪res A η x, pS η x⟫
  have := neg_abs_le ⟪η x, pS (res A η) x⟫
  have := le_abs_self ⟪η x, pS A x (η x)⟫
  nlinarith

end HCWK

namespace FiniteEnergyPlane

open HCWK

set_option maxHeartbeats 1000000 in
theorem halfCyl_slice_deriv_sq_le_of_logDeriv_bound_aux {n : ℕ}
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (s₀ c Λ : ℝ) (hs₀ : 0 < s₀)
    (hSb : ∀ s ≥ s₀, ∀ t : ℝ, ∀ i j, |S (s, t) i j| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => S p i j) (s, t) (1, 0)| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => S q i j) p (1, 0)) (s, t) (1, 0)| ≤ c)
    (hα : ∀ s ≥ s₀, |∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫| ≤
      Λ * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) :
    ∃ M s₁ : ℝ, ∀ s ≥ s₁,
      ∫ t in (0:ℝ)..1, ‖deriv (fun x => ζ (s, x)) t‖ ^ 2 ≤
        M * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
  classical
  set A : ℝ × ℝ → Op n := fun p => TL n (S p) with hAdef
  have hA : Sm A := (contDiff_TL S hS).contDiffOn
  have hpA : TPer A := fun s t => by simp only [A, hSper s t]
  have hζs : Sm ζ := hζ.1
  have hpζ : TPer ζ := hζ.2.1
  have hres0 : ∀ x ∈ Ω, res A ζ x = 0 := by
    rintro ⟨a, b⟩ hx
    exact hζ.2.2 a hx.1 b
  -- operator bounds on the coefficient field
  obtain ⟨c0, hc0, hop⟩ := op_small (n := n)
  set a := c0 * |c| with ha_def
  have ha : 0 ≤ a := by positivity
  have hdiffS : ∀ i j, Differentiable ℝ (fun p : ℝ × ℝ => S p i j) :=
    fun i j => (hS i j).differentiable (by simp)
  set S' : ℝ × ℝ → Mat n := fun p => Matrix.of fun i j => pS (fun q => S q i j) p with hS'def
  have hS' : ∀ i j, ContDiff ℝ ∞ (fun p => S' p i j) := contDiff_of_pS S hS
  have hpSA : pS A = fun p => TL n (S' p) := funext fun p => hasFDerivAt_TL S hdiffS p
  have hpSSA : ∀ x, pS (pS A) x = TL n (Matrix.of fun i j => pS (fun p => S' p i j) x) := by
    intro x
    rw [hpSA]
    exact hasFDerivAt_TL S' (fun i j => (hS' i j).differentiable (by simp)) x
  have hbA : ∀ x : ℝ × ℝ, s₀ ≤ x.1 → ‖A x‖ ≤ a ∧ ‖pS A x‖ ≤ a ∧ ‖pS (pS A) x‖ ≤ a := by
    rintro ⟨s, t⟩ hs
    have hb := fun i j => hSb s hs t i j
    refine ⟨hop _ _ (abs_nonneg c) fun i j => (hb i j).1.trans (le_abs_self c), ?_, ?_⟩
    · rw [hpSA]
      exact hop _ _ (abs_nonneg c) fun i j => by
        simpa [S', pS] using (hb i j).2.1.trans (le_abs_self c)
    · rw [hpSSA]
      exact hop _ _ (abs_nonneg c) fun i j => by
        simpa [S', pS] using (hb i j).2.2.trans (le_abs_self c)
  -- the `s`-derivative `w = ∂ₛζ` and its residual
  set w := pS ζ with hwdef
  have hw : Sm w := hζs.dS
  have hpw : TPer w := hpζ.pS
  have hres1 : ∀ x ∈ Ω, res A w x = -(pS A x (ζ x)) := by
    intro x hx
    have h0 : pS (res A ζ) x = 0 := by
      rw [pS_congr (v := fun _ => (0 : Vec n)) hres0 hx]
      simp [pS]
    have e : res A ζ = (pS ζ + fun y => Jop n (pT ζ y)) + fun y => A y (ζ y) := rfl
    rw [e, pS_add (hζs.dS.add hζs.dT.jop) (hA.apply hζs) hx, pS_add hζs.dS hζs.dT.jop hx,
      pS_constOp _ hζs.dT hx, pS_pT hζs hx, pS_apply hA hζs hx] at h0
    show pS w x + Jop n (pT w x) + A x (w x) = _
    rw [eq_neg_iff_add_eq_zero]
    convert h0 using 1
    abel
  have hpres1 : ∀ x ∈ Ω, pS (res A w) x = -(pS (pS A) x (ζ x) + pS A x (w x)) := by
    intro x hx
    rw [pS_congr (v := fun y => -(pS A y (ζ y))) hres1 hx,
      show (fun y => -(pS A y (ζ y))) = -(fun y => pS A y (ζ y)) from rfl, pS_neg,
      pS_apply hA.dS hζs hx]
  -- pointwise lower bounds for the energy integrands
  set k := a ^ 2 + 3 * a with hk
  have hk0 : 0 ≤ k := by positivity
  have qw : ∀ x : ℝ × ℝ, 0 < x.1 → s₀ ≤ x.1 →
      (-k) * ‖w x‖ ^ 2 + (-k) * ‖ζ x‖ ^ 2 ≤ Qd A w x := by
    intro x hx0 hx
    have hxΩ : x ∈ Ω := ⟨hx0, trivial⟩
    obtain ⟨b1, b2, b3⟩ := hbA x hx
    have hq := Qd_ge A w x
    rw [hres1 x hxΩ, hpres1 x hxΩ, norm_neg, norm_neg] at hq
    set X := ‖pS w x‖
    set W := ‖w x‖
    set Z := ‖ζ x‖
    have hX : 0 ≤ X := norm_nonneg _
    have hW : 0 ≤ W := norm_nonneg _
    have hZ : 0 ≤ Z := norm_nonneg _
    have r1 : ‖pS A x (ζ x)‖ ≤ a * Z :=
      ((pS A x).le_opNorm _).trans (mul_le_mul_of_nonneg_right b2 hZ)
    have r2 : ‖pS (pS A) x (ζ x) + pS A x (w x)‖ ≤ a * Z + a * W :=
      (norm_add_le _ _).trans (add_le_add
        (((pS (pS A) x).le_opNorm _).trans (mul_le_mul_of_nonneg_right b3 hZ))
        (((pS A x).le_opNorm _).trans (mul_le_mul_of_nonneg_right b2 hW)))
    have t1 : ‖A x‖ * W * X ≤ a * W * X := by gcongr
    have t2 : ‖pS A x (ζ x)‖ * X ≤ a * Z * X := mul_le_mul_of_nonneg_right r1 hX
    have t3 : W * ‖pS (pS A) x (ζ x) + pS A x (w x)‖ ≤ W * (a * Z + a * W) :=
      mul_le_mul_of_nonneg_left r2 hW
    have t4 : ‖pS A x‖ * W * W ≤ a * W * W := by gcongr
    nlinarith [sq_nonneg (X - a * W), sq_nonneg (X - a * Z / 2), mul_nonneg ha (sq_nonneg (W - Z)),
      mul_nonneg ha (sq_nonneg W), mul_nonneg ha (sq_nonneg Z)]
  have qz : ∀ x : ℝ × ℝ, 0 < x.1 → s₀ ≤ x.1 →
      ‖w x‖ ^ 2 + (-(a ^ 2 + a)) * ‖ζ x‖ ^ 2 ≤ Qd A ζ x := by
    intro x hx0 hx
    have hxΩ : x ∈ Ω := ⟨hx0, trivial⟩
    obtain ⟨b1, b2, b3⟩ := hbA x hx
    have hq := Qd_ge A ζ x
    have h0 : pS (res A ζ) x = 0 := by
      rw [pS_congr (v := fun _ => (0 : Vec n)) hres0 hxΩ]
      simp [pS]
    rw [hres0 x hxΩ, h0, norm_zero] at hq
    set W := ‖w x‖
    set Z := ‖ζ x‖
    have hW : 0 ≤ W := norm_nonneg _
    have hZ : 0 ≤ Z := norm_nonneg _
    have t1 : ‖A x‖ * Z * W ≤ a * Z * W := by gcongr
    have t4 : ‖pS A x‖ * Z * Z ≤ a * Z * Z := by gcongr
    nlinarith [sq_nonneg (W - a * Z)]
  -- slice integrals
  have sw : ∀ σ, 0 < σ → Gz ζ σ = ∫ t in (0:ℝ)..1, ‖w (σ, t)‖ ^ 2 := fun σ _ => by
    simp only [Gz, Ip, real_inner_self_eq_norm_sq, w]
  have sz : ∀ σ, Fz ζ σ = ∫ t in (0:ℝ)..1, ‖ζ (σ, t)‖ ^ 2 := fun σ => by
    simp only [Fz, Ip, real_inner_self_eq_norm_sq]
  have iw : ∀ σ, 0 < σ → IntervalIntegrable (fun t => ‖w (σ, t)‖ ^ 2) volume 0 1 :=
    fun σ hσ => ((cont_slice hw.cont hσ).norm.pow 2).intervalIntegrable _ _
  have iz : ∀ σ, 0 < σ → IntervalIntegrable (fun t => ‖ζ (σ, t)‖ ^ 2) volume 0 1 :=
    fun σ hσ => ((cont_slice hζs.cont hσ).norm.pow 2).intervalIntegrable _ _
  have hIw : ∀ σ ≥ s₀, (-k) * Gz ζ σ + (-k) * Fz ζ σ ≤ ∫ t in (0:ℝ)..1, Qd A w (σ, t) := by
    intro σ hσ
    have hσ0 : 0 < σ := hs₀.trans_le hσ
    have := intervalIntegral.integral_mono_on zero_le_one
      (((iw σ hσ0).const_mul (-k)).add ((iz σ hσ0).const_mul (-k))) (ii (Qd_cont hA hw) hσ0)
      fun t _ => qw (σ, t) hσ0 hσ
    rwa [intervalIntegral.integral_add ((iw σ hσ0).const_mul (-k)) ((iz σ hσ0).const_mul (-k)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← sw σ hσ0,
      ← sz σ] at this
  have hIz : ∀ σ ≥ s₀, Gz ζ σ + (-(a ^ 2 + a)) * Fz ζ σ ≤ ∫ t in (0:ℝ)..1, Qd A ζ (σ, t) := by
    intro σ hσ
    have hσ0 : 0 < σ := hs₀.trans_le hσ
    have := intervalIntegral.integral_mono_on zero_le_one
      ((iw σ hσ0).add ((iz σ hσ0).const_mul (-(a ^ 2 + a)))) (ii (Qd_cont hA hζs) hσ0)
      fun t _ => qz (σ, t) hσ0 hσ
    rwa [intervalIntegral.integral_add (iw σ hσ0) ((iz σ hσ0).const_mul (-(a ^ 2 + a))),
      intervalIntegral.integral_const_mul, ← sw σ hσ0, ← sz σ] at this
  -- derivatives
  set H : ℝ → ℝ := fun σ => Gz ζ σ + k * Fz ζ σ with hH
  set H1 : ℝ → ℝ := fun σ => 2 * Ip w (pS w) σ + k * (2 * Dz ζ σ) with hH1
  set Dd : ℝ → ℝ := fun σ => ∫ t in (0:ℝ)..1, Qd A ζ (σ, t) with hDd
  set H2 : ℝ → ℝ := fun σ => 2 * (∫ t in (0:ℝ)..1, Qd A w (σ, t)) + k * (2 * Dd σ) with hH2
  have dH : ∀ σ, 0 < σ → HasDerivAt H (H1 σ) σ := fun σ hσ =>
    ((Gz_hasDerivAt hζs hσ).add ((Fz_hasDerivAt hζs hσ).const_mul k)).congr_deriv (by
      simp only [H1]; rw [Ip_comm (pS w) w]; ring)
  have dD : ∀ σ, 0 < σ → HasDerivAt (Dz ζ) (Dd σ) σ := fun σ hσ => energy_d2 hA hζs hpA hpζ hσ
  have dH1 : ∀ σ, 0 < σ → HasDerivAt H1 (H2 σ) σ := fun σ hσ =>
    ((energy_d2 hA hw hpA hpw hσ).const_mul 2).add (((dD σ hσ).const_mul 2).const_mul k)
  set κ := 2 * k * (1 + a ^ 2 + a) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hH2lo : ∀ σ ≥ s₀, -κ * Fz ζ σ ≤ H2 σ := by
    intro σ hσ
    have h1 := hIw σ hσ
    have h2 := mul_le_mul_of_nonneg_left (hIz σ hσ) (by positivity : (0:ℝ) ≤ 2 * k)
    simp only [H2, Dd]
    nlinarith
  have hDdlo : ∀ σ ≥ s₀, H σ - (k + a ^ 2 + a) * Fz ζ σ ≤ Dd σ := by
    intro σ hσ
    have := hIz σ hσ
    simp only [H, Dd] at this ⊢
    linarith
  -- doubling of `F`
  set Λ' := |Λ|
  have hD : ∀ x ≥ s₀, |Dz ζ x| ≤ Λ' * Fz ζ x := by
    intro x hx
    have h := hα x hx
    rw [← sz x] at h
    have hF := Ip_self_nonneg ζ x
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self Λ) hF)
  have hdF : ∀ x ≥ s₀, HasDerivAt (Fz ζ) (2 * Dz ζ x) x := fun x hx =>
    Fz_hasDerivAt hζs (hs₀.trans_le hx)
  set E := Real.exp (2 * Λ')
  have hE : 0 ≤ E := (Real.exp_pos _).le
  set j := ‖Jop n‖
  set M := 2 * j ^ 2 * (Λ' * E + κ * E / 2 + (k + a ^ 2 + a) * E) + 2 * j ^ 2 * a ^ 2
  refine ⟨M, s₀ + 1, fun s hs => ?_⟩
  have hs0 : s₀ ≤ s := by linarith
  have hspos : 0 < s := hs₀.trans_le hs0
  set Fs := Fz ζ s
  have hFs : 0 ≤ Fs := Ip_self_nonneg ζ s
  have mem : ∀ x ∈ Icc (s - 1) (s + 1), s₀ ≤ x := fun x hx => by linarith [hx.1]
  have memp : ∀ x ∈ Icc (s - 1) (s + 1), 0 < x := fun x hx => hs₀.trans_le (mem x hx)
  have hFw : ∀ x ∈ Icc (s - 1) (s + 1), Fz ζ x ≤ E * Fs := fun x hx =>
    le_exp_mul_of_abs_deriv_le (Fz ζ) (Dz ζ) s₀ Λ' (abs_nonneg Λ) hdF hD (fun y _ => Ip_self_nonneg ζ y) hs0
      (mem x hx) (abs_sub_le_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hHs := le_add_of_deriv_two_ge H H1 H2 (Dz ζ) Dd s (κ * (E * Fs)) ((k + a ^ 2 + a) * (E * Fs))
    (Λ' * (E * Fs)) (by positivity)
    (fun x hx => dH x (memp x hx)) (fun x hx => dH1 x (memp x hx))
    (fun x hx => by
      have := hH2lo x (mem x hx)
      have := mul_le_mul_of_nonneg_left (hFw x hx) hκ0
      linarith)
    (fun x hx => dD x (memp x hx))
    (fun x hx => by
      have := hDdlo x (mem x hx)
      have := mul_le_mul_of_nonneg_left (hFw x hx) (by positivity : (0:ℝ) ≤ k + a ^ 2 + a)
      linarith)
    (fun x hx => (hD x (mem x hx)).trans
      (mul_le_mul_of_nonneg_left (hFw x hx) (abs_nonneg Λ)))
  have hG : Gz ζ s ≤ Λ' * (E * Fs) + κ * (E * Fs) / 2 + (k + a ^ 2 + a) * (E * Fs) := by
    have : 0 ≤ k * Fs := mul_nonneg hk0 hFs
    simp only [H] at hHs
    linarith
  -- `∂ₜζ = J₀ (∂ₛζ + S ζ)`
  have hpt : ∀ t : ℝ, ‖deriv (fun x => ζ (s, x)) t‖ ^ 2 ≤
      (2 * j ^ 2) * ‖w (s, t)‖ ^ 2 + (2 * j ^ 2 * a ^ 2) * ‖ζ (s, t)‖ ^ 2 := by
    intro t
    have hxΩ : (s, t) ∈ Ω := mem_Ω hspos
    rw [(hζs.hasDerivAt_t hspos).deriv]
    have h0 := hres0 (s, t) hxΩ
    have e : pT ζ (s, t) = Jop n (w (s, t) + A (s, t) (ζ (s, t))) := by
      have h1 : Jop n (pT ζ (s, t)) = -(w (s, t) + A (s, t) (ζ (s, t))) := by
        rw [eq_neg_iff_add_eq_zero]
        convert h0 using 1
        simp only [res, w]; abel
      calc pT ζ (s, t) = -(Jop n (Jop n (pT ζ (s, t)))) := by rw [Jop_Jop, neg_neg]
        _ = Jop n (w (s, t) + A (s, t) (ζ (s, t))) := by rw [h1, map_neg, neg_neg]
    obtain ⟨b1, -, -⟩ := hbA (s, t) hs0
    have hA1 : ‖A (s, t) (ζ (s, t))‖ ≤ a * ‖ζ (s, t)‖ :=
      ((A (s, t)).le_opNorm _).trans (mul_le_mul_of_nonneg_right b1 (norm_nonneg _))
    have hsum : ‖w (s, t) + A (s, t) (ζ (s, t))‖ ≤ ‖w (s, t)‖ + a * ‖ζ (s, t)‖ :=
      (norm_add_le _ _).trans (by linarith)
    have hn : ‖pT ζ (s, t)‖ ≤ j * (‖w (s, t)‖ + a * ‖ζ (s, t)‖) :=
      calc ‖pT ζ (s, t)‖ = ‖Jop n (w (s, t) + A (s, t) (ζ (s, t)))‖ := by rw [e]
        _ ≤ j * ‖w (s, t) + A (s, t) (ζ (s, t))‖ := (Jop n).le_opNorm _
        _ ≤ j * (‖w (s, t)‖ + a * ‖ζ (s, t)‖) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    have hj : 0 ≤ j := norm_nonneg _
    have hW := norm_nonneg (w (s, t))
    have hZ := norm_nonneg (ζ (s, t))
    have hn0 := norm_nonneg (pT ζ (s, t))
    have := mul_le_mul hn hn hn0 (by positivity)
    nlinarith [sq_nonneg (‖w (s, t)‖ - a * ‖ζ (s, t)‖), sq_nonneg j]
  have hder : (fun t => ‖deriv (fun x => ζ (s, x)) t‖ ^ 2) = fun t => ‖pT ζ (s, t)‖ ^ 2 := by
    funext t; rw [(hζs.hasDerivAt_t hspos).deriv]
  have iT : IntervalIntegrable (fun t => ‖deriv (fun x => ζ (s, x)) t‖ ^ 2) volume 0 1 := by
    rw [hder]; exact ((cont_slice hζs.dT.cont hspos).norm.pow 2).intervalIntegrable 0 1
  have hint := intervalIntegral.integral_mono_on zero_le_one iT
    (((iw s hspos).const_mul (2 * j ^ 2)).add ((iz s hspos).const_mul (2 * j ^ 2 * a ^ 2)))
    fun t _ => hpt t
  rw [intervalIntegral.integral_add ((iw s hspos).const_mul _) ((iz s hspos).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← sw s hspos,
    ← sz s] at hint
  refine hint.trans ?_
  have hj2 : 0 ≤ 2 * j ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hG hj2
  have e3 : M * Fs = 2 * j ^ 2 * (Λ' * (E * Fs) + κ * (E * Fs) / 2 + (k + a ^ 2 + a) * (E * Fs)) +
      2 * j ^ 2 * a ^ 2 * Fs := by simp only [M]; ring
  rw [← sz s]
  change _ ≤ M * Fs
  rw [e3]
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real RealInnerProductSpace

theorem solution {n : ℕ}
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (s₀ c Λ : ℝ) (hs₀ : 0 < s₀)
    (hSb : ∀ s ≥ s₀, ∀ t : ℝ, ∀ i j, |S (s, t) i j| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => S p i j) (s, t) (1, 0)| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => S q i j) p (1, 0)) (s, t) (1, 0)| ≤ c)
    (hα : ∀ s ≥ s₀, |∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫| ≤
      Λ * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) :
    ∃ M s₁ : ℝ, ∀ s ≥ s₁,
      ∫ t in (0:ℝ)..1, ‖deriv (fun x => ζ (s, x)) t‖ ^ 2 ≤
        M * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 :=
  FiniteEnergyPlane.halfCyl_slice_deriv_sq_le_of_logDeriv_bound_aux S hS hSper ζ hζ s₀ c Λ hs₀ hSb hα
