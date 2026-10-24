-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_eta_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:53:57.462423+00:00
-- url     : https://prove2.me/submissions/434d2ab1-55b7-4d59-a49b-c80347456c53

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics

set_option linter.all false

section HD_a

/-! Global existence for linear ODEs `x' = L t (x t)` with bounded coefficients (Picard series). -/

open scoped Topology
open Set Filter

namespace HDecay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end HDecay

end HD_a

section HD_b

/-! Fundamental solution of `Ψ' = J₀ S∞ Ψ`, its inverse, and the sup-norm gap estimate. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

/-- matrices as operators -/
noncomputable def TL (n : ℕ) : Mat n ≃L[ℝ] (Op n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma TL_apply (M : Mat n) (v : Vec n) : TL n M v = Matrix.toEuclideanLin M v := rfl

end HDecay

end HD_b

section HD_c

/-! Sup-norm gap estimate for the nondegenerate asymptotic operator `-J₀ ∂ₜ - S∞`. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

/-- `J₀` as an operator. -/
noncomputable abbrev Jop (n : ℕ) : Op n := TL n (J₀ n)

end HDecay

end HD_c

section HD_d

/-! Partial derivatives on the half-cylinder `Ω = (0, ∞) × ℝ`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

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

lemma pT_add {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pT (u + v) x = pT u x + pT v x := by
  simp [pT, fderiv_add (hu.diffAt hx) (hv.diffAt hx)]

lemma pS_neg (u : ℝ × ℝ → F) (x) : pS (-u) x = -pS u x := by
  simp [pS, show (-u) = fun y => -u y from rfl]

lemma pT_neg (u : ℝ × ℝ → F) (x) : pT (-u) x = -pT u x := by
  simp [pT, show (-u) = fun y => -u y from rfl]

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
  simp [HDecay.pS, hu.fderiv s t]

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

end HDecay

end HD_d

section HD_e

/-! `t`-integrals over a period: differentiation in `s` and integration by parts in `t`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

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

end HDecay

end HD_e

section HD_f

/-! Bounds on the coefficient field `S` from its `C^∞` convergence to `S∞`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

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

end HDecay

end HD_f

section HD_g

/-! Second derivative of the energy `∫₀¹ |η(s, t)|² dt`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

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

end HDecay

end HD_g

section HD_h

/-! Jensen, the `L²` gap estimate, and two one-variable decay lemmas. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_h

section HD_i

/-! Generic lower bounds for the energy's second derivative. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

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

end HDecay

end HD_i

section HD_j

/-! One-variable lemmas used to pass from energy inequalities to decay. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

end HDecay

end HD_j

section AF_a

/-! Gap estimate with kernel: periodic loops are sup-close to periodic solutions. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_a

section AF_b

/-! Cauchy–Schwarz for `Ip` and the differential inequality for `α = ⟨ζ, ∂ₛζ⟩ / |ζ|²`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

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

end HDecay

end AF_b

section AF_c

/-! One-variable lemmas: forward positivity (unique continuation) and barriers. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

end HDecay

end AF_c

section AF_d

/-! Convergence of `α` under an integrable (exponentially small) defect. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

section

variable (α α1 q F ε : ℝ → ℝ) (s1 K d C0 δ0 : ℝ)

variable {α α1 q F ε s1 K d C0 δ0}

end

end HDecay

end AF_d

section AF_e

/-! Exponential rate for `α → μ` given a spectral gap inequality. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

variable {α α1 q F ε : ℝ → ℝ} {s1 K d C0 δ0 : ℝ}

end HDecay

end AF_e

section AF_f

/-! Exponentially small coefficients from `IsExpAsymptoticTo`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

theorem coeff_exp (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (d : ℝ)
    (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d) :
    ∃ K > 0, ∃ s1 > 0, ∀ s ≥ s1, ∀ t, ‖TL n (S (s, t)) - TL n (Sinf t)‖ ≤ K * Real.exp (-(d * s)) ∧
      ‖pS (fun p => TL n (S p)) (s, t)‖ ≤ K * Real.exp (-(d * s)) ∧
      ‖pS (pS (fun p => TL n (S p))) (s, t)‖ ≤ K * Real.exp (-(d * s)) := by
  obtain ⟨c, hc, hcM⟩ := op_small (n := n)
  have h := fun i j (m : ℕ) => (hSas i j).2 m
  choose Cf s1f hs1f using h
  set Cm := ∑ i, ∑ j, (|Cf i j 0| + |Cf i j 1| + |Cf i j 2|) + 1
  set s1 := ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1| + |s1f i j 2|) + 1
  have hsum : ∀ (g : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℕ → ℝ) i j,
      |g i j 0| + |g i j 1| + |g i j 2| ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) := by
    intro g i j
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, (|g i j 0| + |g i j 1| +
      |g i j 2|)) (fun i _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => |g i j 0| + |g i j 1| + |g i j 2|)
      (fun j _ => by positivity) (Finset.mem_univ j)
  have hle : ∀ (g : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℕ → ℝ) i j, g i j 0 ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) + 1 ∧
      g i j 1 ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) + 1 ∧
      g i j 2 ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) + 1 := by
    intro g i j
    have := hsum g i j
    have := le_abs_self (g i j 0); have := le_abs_self (g i j 1)
    have := le_abs_self (g i j 2); have := abs_nonneg (g i j 0)
    have := abs_nonneg (g i j 1); have := abs_nonneg (g i j 2)
    refine ⟨by linarith, by linarith, by linarith⟩
  have hs1pos : 0 < s1 := by
    have : 0 ≤ ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1| + |s1f i j 2|) := by positivity
    linarith
  have hCm : 0 < Cm := by
    have : 0 ≤ ∑ i, ∑ j, (|Cf i j 0| + |Cf i j 1| + |Cf i j 2|) := by positivity
    linarith
  refine ⟨c * Cm, by positivity, s1, hs1pos, fun s hs t => ⟨?_, ?_, ?_⟩⟩
  · rw [← map_sub, mul_assoc]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 0 s ((hle s1f i j).1.trans hs) t
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    simp only [Matrix.sub_apply]
    exact this.trans (mul_le_mul_of_nonneg_right (hle Cf i j).1 (Real.exp_pos _).le)
  · rw [hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)), mul_assoc]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 1 s ((hle s1f i j).2.1.trans hs) t
    simp only [Matrix.of_apply, pS_entry S hS Sinf hSinf']
    exact ((pS_le0 _ _).trans this).trans
      (mul_le_mul_of_nonneg_right (hle Cf i j).2.1 (Real.exp_pos _).le)
  · have hfun : pS (fun p => TL n (S p)) = fun p => TL n (Matrix.of fun i j => pS (fun p => S p i j) p) :=
      funext (hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)))
    rw [hfun, hasFDerivAt_TL _ (fun i j => (contDiff_of_pS S hS i j).differentiable (by simp)),
      mul_assoc]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 2 s ((hle s1f i j).2.2.trans hs) t
    simp only [Matrix.of_apply, pS_entry S hS Sinf hSinf']
    have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) :=
      (hS i j).sub ((hSinf' i j).comp contDiff_snd)
    exact ((pS_pS_le _ hg _).trans this).trans
      (mul_le_mul_of_nonneg_right (hle Cf i j).2.2 (Real.exp_pos _).le)

end HDecay

end AF_f

section AF_g

/-! The quantities `F, D, G, α, q` of a solution and their derivatives. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

section sol

variable (A : ℝ × ℝ → Op n) (ζ : ℝ × ℝ → Vec n)

noncomputable def Fz (s : ℝ) : ℝ := Ip ζ ζ s
noncomputable def Dz (s : ℝ) : ℝ := Ip ζ (pS ζ) s
noncomputable def Gz (s : ℝ) : ℝ := Ip (pS ζ) (pS ζ) s
noncomputable def αz (s : ℝ) : ℝ := Dz ζ s / Fz ζ s
noncomputable def qz (s : ℝ) : ℝ := Gz ζ s / Fz ζ s - (αz ζ s) ^ 2
variable {A ζ}

lemma Fz_hasDerivAt (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) : HasDerivAt (Fz ζ) (2 * Dz ζ s) s :=
  (Ip_hasDerivAt hζ hζ hs).congr_deriv (by simp only [Dz]; rw [Ip_comm (pS ζ) ζ]; ring)

lemma Fz_hasDerivAt' (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) :
    HasDerivAt (Fz ζ) (2 * αz ζ s * Fz ζ s) s :=
  (Fz_hasDerivAt hζ hs).congr_deriv (by simp only [αz]; field_simp)

lemma Gz_hasDerivAt (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Gz ζ) (Ip (pS (pS ζ)) (pS ζ) s + Ip (pS ζ) (pS (pS ζ)) s) s :=
  Ip_hasDerivAt hζ.dS hζ.dS hs

lemma Fz_cont (hζ : Sm ζ) : ContinuousOn (Fz ζ) (Ioi 0) := fun s hs =>
  (Fz_hasDerivAt hζ hs).continuousAt.continuousWithinAt

lemma Gz_cont (hζ : Sm ζ) : ContinuousOn (Gz ζ) (Ioi 0) := fun s hs =>
  (Gz_hasDerivAt hζ hs).continuousAt.continuousWithinAt

lemma Dz_cont (hζ : Sm ζ) : ContinuousOn (Dz ζ) (Ioi 0) := fun s hs =>
  (Ip_hasDerivAt hζ hζ.dS hs).continuousAt.continuousWithinAt

lemma Dz_sq_le (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) : Dz ζ s ^ 2 ≤ Fz ζ s * Gz ζ s :=
  cs_Ip' hζ.cont hζ.dS.cont hs

lemma qz_nonneg (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) : 0 ≤ qz ζ s := by
  have h := Dz_sq_le hζ hs
  simp only [qz, αz]
  rw [div_pow, sub_nonneg, div_le_div_iff₀ (by positivity) hF]
  nlinarith

end sol

end HDecay

end AF_g

section AF_h

/-! Unique continuation: `‖ζ(s)‖_{L²} > 0` for all `s ≥ s₀` once it is positive at `s₀`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_h

section AF_i

/-! The `α`-hypotheses for a solution of the linear Cauchy–Riemann equation. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_i

section AF_j

/-! Spectral gap inequality for `A∞ - μ`, valid for every `μ ∈ ℝ`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_j

section AF_k

/-! The gap inequality `|α - μ| ≤ κ (q + ε)` near `μ`, for a solution of the linear CR equation. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

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

end HDecay

end AF_k

section AF_l

/-! Exponential convergence of `α` to a limit `μ ≤ δ₀` for a solution. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_l

section AF_m

/-! A one-dimensional mean value inequality: `f'' ≥ -g`, `f ≥ 0` ⇒ `f(a) ≤ ∫ f + ∫ g`. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

lemma le_of_deriv_nonneg_Icc (f f' : ℝ → ℝ) {x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z) (h : ∀ z ∈ Icc x y, 0 ≤ f' z) : f x ≤ f y := by
  have hc : ContinuousOn f (Icc x y) := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y) hc
    (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
    (fun z hz => h z (interior_subset hz)) ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

lemma exists_le_integral (f : ℝ → ℝ) (b : ℝ) (hf : ContinuousOn f (Icc b (b + 1))) :
    ∃ σ ∈ Icc b (b + 1), f σ ≤ ∫ x in b..(b + 1), f x := by
  obtain ⟨σ, hσ, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith)) hf
  refine ⟨σ, hσ, ?_⟩
  have := intervalIntegral.integral_mono_on (by linarith : b ≤ b + 1) (intervalIntegrable_const (μ := volume))
    (hf.intervalIntegrable_of_Icc (by linarith)) fun x hx => hmin hx
  simpa using this

theorem mean_value (f f1 f2 g : ℝ → ℝ) (a : ℝ) (ha : 1 < a) (hg : ContinuousOn g (Ioi 0))
    (hf : ∀ x ∈ Icc (a - 1) (a + 1), HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Icc (a - 1) (a + 1), HasDerivAt f1 (f2 x) x)
    (hg0 : ∀ x ∈ Icc (a - 1) (a + 1), 0 ≤ g x) (h2 : ∀ x ∈ Icc (a - 1) (a + 1), -g x ≤ f2 x)
    (hf0 : ∀ x ∈ Icc (a - 1) (a + 1), 0 ≤ f x) :
    f a ≤ (∫ x in (a - 1)..(a + 1), f x) + ∫ x in (a - 1)..(a + 1), g x := by
  have hsub : Icc (a - 1) (a + 1) ⊆ Ioi 0 := fun x hx => by simp only [mem_Ioi]; linarith [hx.1]
  have hfc : ContinuousOn f (Icc (a - 1) (a + 1)) :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  set Gt := ∫ x in (a - 1)..(a + 1), g x
  set Γ : ℝ → ℝ := fun x => ∫ y in (a - 1)..x, g y
  have hΓ : ∀ x ∈ Icc (a - 1) (a + 1), HasDerivAt Γ (g x) x := by
    intro x hx
    have hx0 : 0 < x := hsub hx
    refine intervalIntegral.integral_hasDerivAt_right ?_
      (hg.stronglyMeasurableAtFilter isOpen_Ioi x hx0) (hg.continuousAt (isOpen_Ioi.mem_nhds hx0))
    refine (hg.mono ?_).intervalIntegrable
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    exact hsub ⟨hy.1, hy.2.trans hx.2⟩
  have hΓmono : ∀ x ∈ Icc (a - 1) (a + 1), ∀ y ∈ Icc (a - 1) (a + 1), x ≤ y → Γ y - Γ x ≤ Gt := by
    intro x hx y hy hxy
    have hint : IntervalIntegrable g volume (a - 1) (a + 1) :=
      (hg.mono hsub).intervalIntegrable_of_Icc (by linarith)
    have e1 : Γ y - Γ x = ∫ z in x..y, g z := by
      simp only [Γ]
      rw [intervalIntegral.integral_interval_sub_left]
      · exact hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hy.1 hy.2))
      · exact hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hx.1 hx.2))
    have e2 : ∫ z in x..y, g z ≤ Gt := by
      refine intervalIntegral.integral_mono_interval hx.1 hxy hy.2 ?_ hint
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      exact hg0 z ⟨le_of_lt hz.1, hz.2⟩
    linarith
  -- `f1 + Γ` is monotone on the interval
  have hm : ∀ x ∈ Icc (a - 1) (a + 1), ∀ y ∈ Icc (a - 1) (a + 1), x ≤ y →
      f1 x + Γ x ≤ f1 y + Γ y := by
    intro x hx y hy hxy
    refine le_of_deriv_nonneg_Icc (fun z => f1 z + Γ z) (fun z => f2 z + g z) hxy
      (fun z hz => (hf1 z ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩).add
        (hΓ z ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩))
      (fun z hz => by have := h2 z ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩; linarith)
  have ha' : a ∈ Icc (a - 1) (a + 1) := ⟨by linarith, by linarith⟩
  obtain ⟨σ1, hσ1, hfσ1⟩ := exists_le_integral f (a - 1)
    (hfc.mono (Icc_subset_Icc le_rfl (by linarith)))
  obtain ⟨σ2, hσ2, hfσ2⟩ := exists_le_integral f a
    (hfc.mono (Icc_subset_Icc (by linarith) le_rfl))
  rw [show a - 1 + 1 = a by ring] at hσ1 hfσ1
  have hσ1' : σ1 ∈ Icc (a - 1) (a + 1) := ⟨hσ1.1, hσ1.2.trans (by linarith)⟩
  have hσ2' : σ2 ∈ Icc (a - 1) (a + 1) := ⟨by linarith [hσ2.1], hσ2.2⟩
  have hIf : IntervalIntegrable f volume (a - 1) (a + 1) := hfc.intervalIntegrable_of_Icc (by linarith)
  have hsplit : (∫ x in (a - 1)..(a + 1), f x) =
      (∫ x in (a - 1)..a, f x) + ∫ x in a..(a + 1), f x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hIf.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le ha'.1 ha'.2)))
      (hIf.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le ha'.1 ha'.2) right_mem_uIcc))).symm
  have hI1 : 0 ≤ ∫ x in (a - 1)..a, f x :=
    intervalIntegral.integral_nonneg (by linarith) fun x hx => hf0 x ⟨hx.1, hx.2.trans (by linarith)⟩
  have hI2 : 0 ≤ ∫ x in a..(a + 1), f x :=
    intervalIntegral.integral_nonneg (by linarith) fun x hx => hf0 x ⟨by linarith [hx.1], hx.2⟩
  have hGt : 0 ≤ Gt := intervalIntegral.integral_nonneg (by linarith) fun x hx => hg0 x hx
  rcases le_or_gt 0 (f1 a) with hpos | hneg
  · -- `f` almost increasing on `[a, σ2]`
    have key : f a + Gt * a ≤ f σ2 + Gt * σ2 := by
      refine le_of_deriv_nonneg_Icc (fun z => f z + Gt * z) (fun z => f1 z + Gt) hσ2.1
        (fun z hz => (hf z ⟨by linarith [hz.1], hz.2.trans hσ2'.2⟩).add
          ((hasDerivAt_id z).const_mul Gt |>.congr_deriv (by ring)))
        (fun z hz => ?_)
      have hz' : z ∈ Icc (a - 1) (a + 1) := ⟨by linarith [hz.1], hz.2.trans hσ2'.2⟩
      have h1 := hm a ha' z hz' hz.1
      have h3 := hΓmono a ha' z hz' hz.1
      linarith
    have : Gt * (σ2 - a) ≤ Gt := by
      have : σ2 - a ≤ 1 := by linarith [hσ2.2]
      nlinarith
    linarith
  · -- `f` almost decreasing on `[σ1, a]`
    have key : -f σ1 + Gt * σ1 ≤ -f a + Gt * a := by
      have := le_of_deriv_nonneg_Icc (fun z => -f z + Gt * z) (fun z => -f1 z + Gt) hσ1.2
        (fun z hz => ((hf z ⟨hσ1'.1.trans hz.1, hz.2.trans (by linarith)⟩).neg).add
          ((hasDerivAt_id z).const_mul Gt |>.congr_deriv (by ring)))
        (fun z hz => by
          have hz' : z ∈ Icc (a - 1) (a + 1) := ⟨hσ1'.1.trans hz.1, hz.2.trans (by linarith)⟩
          have h1 := hm z hz' a ha' hz.2
          have h3 := hΓmono z hz' a ha' hz.2
          linarith)
      skip
      linarith
    have : Gt * (a - σ1) ≤ Gt := by
      have : a - σ1 ≤ 1 := by linarith [hσ1.1]
      nlinarith
    linarith

end HDecay

end AF_m

section AF_n

/-! Pointwise decay of `‖∂ₛζ - μζ‖²_{L²}` relative to `‖ζ‖²_{L²}`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

/-- `∂ₛζ - μζ` -/
noncomputable def ηm (ζ : ℝ × ℝ → Vec n) (μ : ℝ) : ℝ × ℝ → Vec n := fun x => pS ζ x - μ • ζ x

lemma pS_smul' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) {u : ℝ × ℝ → F}
    (hu : Sm u) {x} (hx : x ∈ Ω) : pS (fun y => c • u y) x = c • pS u x := by
  simp only [pS]
  rw [show (fun y => c • u y) = c • u from rfl, fderiv_const_smul (hu.diffAt hx)]
  rfl

lemma pT_smul' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) {u : ℝ × ℝ → F}
    (hu : Sm u) {x} (hx : x ∈ Ω) : pT (fun y => c • u y) x = c • pT u x := by
  simp only [pT]
  rw [show (fun y => c • u y) = c • u from rfl, fderiv_const_smul (hu.diffAt hx)]
  rfl

lemma pT_sub' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u v : ℝ × ℝ → F}
    (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) : pT (u - v) x = pT u x - pT v x := by
  rw [sub_eq_add_neg, pT_add hu hv.neg hx, pT_neg, ← sub_eq_add_neg]

lemma Sm.ηm {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) : Sm (ηm ζ μ) :=
  hζ.dS.sub (hζ.const_smul μ)

lemma TPer.ηm {ζ : ℝ × ℝ → Vec n} (hζ : TPer ζ) (μ : ℝ) : TPer (ηm ζ μ) := fun s t => by
  simp only [HDecay.ηm, hζ.pS s t, hζ s t]

lemma res_ηm {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (μ : ℝ) :
    ∀ x ∈ Ω, res A (ηm ζ μ) x = -(pS A x (ζ x)) := by
  intro x hx
  have hpres0 : pS (res A ζ) x = 0 := by
    rw [pS_congr (v := fun _ => (0 : Vec n)) hres0 hx]
    simp [pS]
  have e : res A ζ = (pS ζ + fun y => Jop n (pT ζ y)) + fun y => A y (ζ y) := rfl
  rw [e, pS_add (hζ.dS.add hζ.dT.jop) (hA.apply hζ) hx, pS_add hζ.dS hζ.dT.jop hx,
    pS_constOp _ hζ.dT hx, pS_pT hζ hx, pS_apply hA hζ hx] at hpres0
  have h0 := hres0 x hx
  have e2 : ηm ζ μ = pS ζ - fun y => μ • ζ y := rfl
  have hsm : Sm fun y => μ • ζ y := hζ.const_smul μ
  simp only [res] at h0 ⊢
  rw [e2, pS_sub hζ.dS hsm hx, pT_sub' hζ.dS hsm hx, pS_smul' μ hζ hx, pT_smul' μ hζ hx]
  have : pS (pS ζ) x - μ • pS ζ x + Jop n (pT (pS ζ) x - μ • pT ζ x) +
      A x (pS ζ x - μ • ζ x) = (pS (pS ζ) x + Jop n (pT (pS ζ) x) + (pS A x (ζ x) + A x (pS ζ x)))
        - μ • (pS ζ x + Jop n (pT ζ x) + A x (ζ x)) - pS A x (ζ x) := by
    simp only [map_sub, map_smul, smul_add]; abel
  simp only [Pi.sub_apply]
  rw [this, hpres0, h0]; simp

lemma pres_ηm {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (μ : ℝ) :
    ∀ x ∈ Ω, pS (res A (ηm ζ μ)) x = -(pS (pS A) x (ζ x) + pS A x (pS ζ x)) := by
  intro x hx
  rw [pS_congr (v := fun y => -(pS A y (ζ y))) (res_ηm hA hζ hres0 μ) hx,
    show (fun y => -(pS A y (ζ y))) = -(fun y => pS A y (ζ y)) from rfl, pS_neg,
    pS_apply hA.dS hζ hx]

/-- the second half of `energy_lower`, which does not need a gap estimate -/
theorem energy_lower2 (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    {A : ℝ × ℝ → Op n} (hA : Sm A) {η w : ℝ × ℝ → Vec n} (hη : Sm η)
    (hw : Sm w) {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hA1 : ∀ t, ‖A (s, t) - TL n (Sinf t)‖ ≤ ε) (hA2 : ∀ t, ‖pS A (s, t)‖ ≤ ε)
    (hr : ∀ t, ‖res A η (s, t)‖ ≤ ε * ‖w (s, t)‖)
    (hr' : ∀ t, ‖pS (res A η) (s, t)‖ ≤ ε * (‖w (s, t)‖ + ‖η (s, t)‖)) :
    Ip (pS η) (pS η) s - 4 * ε * Ip η η s - ε * Ip w w s ≤ ∫ t in (0:ℝ)..1, Qd A η (s, t) := by
  have hξ := hη.dS
  have iξ := ii (hξ.cont.inner hξ.cont) hs
  have iη := ii (hη.cont.inner hη.cont) hs
  have iw := ii (hw.cont.inner hw.cont) hs
  have hpt : ∀ t, ⟪pS η (s, t), pS η (s, t)⟫ - 4 * ε * ⟪η (s, t), η (s, t)⟫ -
      ε * ⟪w (s, t), w (s, t)⟫ ≤ Qd A η (s, t) := by
    intro t
    set ξv := pS η (s, t)
    set ηv := η (s, t)
    set wv := w (s, t)
    set D := A (s, t) - TL n (Sinf t)
    have hsym : ⟪A (s, t) ηv, ξv⟫ - ⟪ηv, A (s, t) ξv⟫ = ⟪D ηv, ξv⟫ - ⟪ηv, D ξv⟫ := by
      have := inner_symm (hS.2.2 t) ηv ξv
      simp only [D, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
      linarith only [this]
    have b1 := abs_inner_op D ηv ξv
    have b2 : |⟪ηv, D ξv⟫| ≤ ‖ηv‖ * (‖D‖ * ‖ξv‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _))
    have b3 : |⟪res A η (s, t), ξv⟫| ≤ ε * ‖wv‖ * ‖ξv‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hr t) (norm_nonneg _))
    have b4 : |⟪ηv, pS (res A η) (s, t)⟫| ≤ ‖ηv‖ * (ε * (‖wv‖ + ‖ηv‖)) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hr' t) (norm_nonneg _))
    have b5 : |⟪ηv, pS A (s, t) ηv⟫| ≤ ‖ηv‖ * (‖pS A (s, t)‖ * ‖ηv‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ((pS A (s, t)).le_opNorm _) (norm_nonneg _))
    have hD := hA1 t
    have hAs := hA2 t
    have q : Qd A η (s, t) = 2 * ⟪ξv, ξv⟫ + (⟪D ηv, ξv⟫ - ⟪ηv, D ξv⟫) - ⟪res A η (s, t), ξv⟫ +
        ⟪ηv, pS (res A η) (s, t)⟫ - ⟪ηv, pS A (s, t) ηv⟫ := by
      rw [← hsym]; simp only [Qd]; ring
    rw [q]
    simp only [real_inner_self_eq_norm_sq]
    have na := norm_nonneg ξv
    have nb := norm_nonneg ηv
    have nc := norm_nonneg wv
    have e1 : ‖D‖ * ‖ηv‖ * ‖ξv‖ ≤ ε * ‖ηv‖ * ‖ξv‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD nb) na
    have e2 : ‖ηv‖ * (‖D‖ * ‖ξv‖) ≤ ‖ηv‖ * (ε * ‖ξv‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD na) nb
    have e5 : ‖ηv‖ * (‖pS A (s, t)‖ * ‖ηv‖) ≤ ‖ηv‖ * (ε * ‖ηv‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAs nb) nb
    have a1 := neg_abs_le ⟪D ηv, ξv⟫
    have a2 := le_abs_self ⟪ηv, D ξv⟫
    have a3 := le_abs_self ⟪res A η (s, t), ξv⟫
    have a4 := neg_abs_le ⟪ηv, pS (res A η) (s, t)⟫
    have a5 := le_abs_self ⟪ηv, pS A (s, t) ηv⟫
    have h1 := mul_nonneg hε0 (sq_nonneg (‖ξv‖ - ‖ηv‖))
    have h2 := mul_nonneg hε0 (sq_nonneg (‖ξv‖ - ‖wv‖))
    have h3 := mul_nonneg hε0 (sq_nonneg (‖ηv‖ - ‖wv‖))
    have h4 := mul_nonneg (sub_nonneg.2 hε) (sq_nonneg ‖ξv‖)
    have h5 := mul_nonneg hε0 (sq_nonneg ‖ξv‖)
    have h6 := mul_nonneg hε0 (sq_nonneg ‖ηv‖)
    linear_combination a1 + b1 + e1 + a2 + b2 + e2 + a3 + b3 + a4 + b4 + a5 + b5 + e5 + h1 +
      h2 / 2 + h3 / 2 + 2 * h4 + h5 / 2 + h6 / 2
  have hQ := ii (Qd_cont hA hη) hs
  have hint := intervalIntegral.integral_mono_on zero_le_one
    ((iξ.sub (iη.const_mul _)).sub (iw.const_mul _)) hQ fun t _ => hpt t
  rw [intervalIntegral.integral_sub (iξ.sub (iη.const_mul _)) (iw.const_mul _),
    intervalIntegral.integral_sub iξ (iη.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  exact hint

/-- `‖ζ_s - μζ‖² = F (q + (α - μ)²)` -/
lemma Ip_ηm {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) (μ : ℝ) :
    Ip (ηm ζ μ) (ηm ζ μ) s = Fz ζ s * (qz ζ s + (αz ζ s - μ) ^ 2) := by
  have ha := cont_slice hζ.dS.cont hs
  have hb := cont_slice hζ.cont hs
  have e : (fun t => ⟪ηm ζ μ (s, t), ηm ζ μ (s, t)⟫) = fun t =>
      1 * ⟪pS ζ (s, t), pS ζ (s, t)⟫ + (-2 * μ) * ⟪ζ (s, t), pS ζ (s, t)⟫ +
        μ ^ 2 * ⟪ζ (s, t), ζ (s, t)⟫ := by
    funext t
    simp only [ηm, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (ζ (s, t)) (pS ζ (s, t))]
    ring
  have : Ip (ηm ζ μ) (ηm ζ μ) s = Gz ζ s - 2 * μ * Dz ζ s + μ ^ 2 * Fz ζ s := by
    simp only [Ip]
    rw [e, int_lin3 _ _ _ (ha.inner ha) (hb.inner ha) (hb.inner hb)]
    simp only [Gz, Dz, Fz, Ip]; ring
  rw [this]
  have hD : Dz ζ s = αz ζ s * Fz ζ s := by simp only [αz]; rw [div_mul_cancel₀ _ hF.ne']
  have hG : Gz ζ s = (qz ζ s + αz ζ s ^ 2) * Fz ζ s := by
    simp only [qz]; rw [sub_add_cancel, div_mul_cancel₀ _ hF.ne']
  rw [hD, hG]; ring

end HDecay

end AF_n

section AF_o

/-! `‖∂ₛζ - μζ‖²_{L²}(s) ≤ C e^{-a s} ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma F_compare (F α : ℝ → ℝ) (s3 B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ s ≥ s3, HasDerivAt F (2 * α s * F s) s) (hpos : ∀ s ≥ s3, 0 < F s)
    (hα : ∀ s ≥ s3, |α s| ≤ B) : ∀ x ≥ s3, ∀ y ≥ s3, |x - y| ≤ 2 →
      F x ≤ F y * Real.exp (4 * B) := by
  intro x hx y hy hxy
  rcases le_total x y with h | h
  · have key := le_of_deriv_nonneg_Icc (fun z => F z * Real.exp (2 * B * z))
      (fun z => (2 * α z + 2 * B) * F z * Real.exp (2 * B * z)) h
      (fun z hz => ((hd z (hx.trans hz.1)).mul
        (((hasDerivAt_id z).const_mul (2 * B)).exp)).congr_deriv (by simp; ring))
      (fun z hz => by
        have h1 := hα z (hx.trans hz.1)
        have h2 := hpos z (hx.trans hz.1)
        have : 0 ≤ 2 * α z + 2 * B := by linarith only [neg_abs_le (α z), h1]
        exact mul_nonneg (mul_nonneg this h2.le) (Real.exp_pos _).le)
    have e : F x = F x * Real.exp (2 * B * x) * Real.exp (-(2 * B * x)) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc F x * Real.exp (2 * B * x) * Real.exp (-(2 * B * x))
        ≤ F y * Real.exp (2 * B * y) * Real.exp (-(2 * B * x)) :=
          mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
      _ = F y * Real.exp (2 * B * (y - x)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ F y * Real.exp (4 * B) := by
          have := (hpos y hy).le
          have : y - x ≤ 2 := by rw [abs_le] at hxy; linarith only [hxy.1]
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by linarith only [mul_nonneg hB (sub_nonneg.2 this)])) (hpos y hy).le
  · have key := le_of_deriv_nonneg_Icc (fun z => -(F z * Real.exp (-(2 * B * z))))
      (fun z => -((2 * α z - 2 * B) * F z * Real.exp (-(2 * B * z)))) h
      (fun z hz => ((hd z (hy.trans hz.1)).mul
        (((hasDerivAt_id z).const_mul (2 * B)).neg.exp)).neg.congr_deriv (by simp; ring))
      (fun z hz => by
        have h1 := hα z (hy.trans hz.1)
        have h2 := hpos z (hy.trans hz.1)
        have : 0 ≤ (2 * B - 2 * α z) * F z * Real.exp (-(2 * B * z)) := by
          have : 0 ≤ 2 * B - 2 * α z := by linarith only [le_abs_self (α z), h1]
          exact mul_nonneg (mul_nonneg this h2.le) (Real.exp_pos _).le
        linarith only [this])
    simp only [neg_le_neg_iff] at key
    have e : F x = F x * Real.exp (-(2 * B * x)) * Real.exp (2 * B * x) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc F x * Real.exp (-(2 * B * x)) * Real.exp (2 * B * x)
        ≤ F y * Real.exp (-(2 * B * y)) * Real.exp (2 * B * x) :=
          mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
      _ = F y * Real.exp (2 * B * (x - y)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ F y * Real.exp (4 * B) := by
          have := (hpos y hy).le
          have : x - y ≤ 2 := by rw [abs_le] at hxy; linarith only [hxy.2]
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by linarith only [mul_nonneg hB (sub_nonneg.2 this)])) (hpos y hy).le

/-- The part of `AlphaHyp` used for the `η` estimates. -/
structure EtaHyp (α q F : ℝ → ℝ) (s1 K d : ℝ) : Prop where
  hK : 0 < K
  hd : 0 < d
  hs1 : 0 < s1
  hq : ∀ s ≥ s1, 0 ≤ q s
  hqc : ContinuousOn q (Ici s1)
  hF : ∀ s ≥ s1, 0 < F s
  hFd : ∀ s ≥ s1, HasDerivAt F (2 * α s * F s) s

theorem eta_decay (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) {A : ℝ × ℝ → Op n}
    {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hpA : TPer A) (hζ : Sm ζ) (hpζ : TPer ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) {s1 K d : ℝ}
    (h : EtaHyp (αz ζ) (qz ζ) (Fz ζ) s1 K d)
    (hco : ∀ s ≥ s1, ∀ t, ‖A (s, t) - TL n (Sinf t)‖ ≤ K * Real.exp (-(d * s)) ∧
        ‖pS A (s, t)‖ ≤ K * Real.exp (-(d * s)) ∧
        ‖pS (pS A) (s, t)‖ ≤ K * Real.exp (-(d * s)))
    (μ a Cr s3 : ℝ) (ha : 0 < a) (hs3 : s1 ≤ s3)
    (hrate : ∀ s ≥ s3, |αz ζ s - μ| ≤ Cr * Real.exp (-(a * s)) ∧
        ∀ T ≥ s, ∫ x in s..T, qz ζ x ≤ Cr * Real.exp (-(a * s))) :
    ∃ a' > 0, ∃ C', ∃ s4, ∀ s ≥ s4,
      Ip (ηm ζ μ) (ηm ζ μ) s ≤ C' * Real.exp (-(a' * s)) * Fz ζ s := by
  have hK := h.hK
  have hd := h.hd
  have hs10 := h.hs1
  have hCr : 0 ≤ Cr := by
    have := (hrate s3 le_rfl).1
    have h0 := abs_nonneg (αz ζ s3 - μ)
    by_contra hc; push Not at hc
    have : Cr * Real.exp (-(a * s3)) < 0 := mul_neg_of_neg_of_pos hc (Real.exp_pos _)
    linarith
  set B := |μ| + Cr
  have hB : 0 ≤ B := add_nonneg (abs_nonneg μ) hCr
  have hαB : ∀ s ≥ s3, |αz ζ s| ≤ B := by
    intro s hs
    have h1 := (hrate s hs).1
    have h2 : Cr * Real.exp (-(a * s)) ≤ Cr := by
      have : Real.exp (-(a * s)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha.le (hs10.trans_le (hs3.trans hs)).le))
      exact mul_le_of_le_one_right hCr this
    calc |αz ζ s| = |(αz ζ s - μ) + μ| := by ring_nf
      _ ≤ |αz ζ s - μ| + |μ| := abs_add_le _ _
      _ ≤ B := by show _ ≤ |μ| + Cr; linarith only [h1, h2]
  have hFc := F_compare (Fz ζ) (αz ζ) s3 B hB (fun s hs => h.hFd s (hs3.trans hs))
    (fun s hs => h.hF s (hs3.trans hs)) hαB
  set η := ηm ζ μ
  have hη : Sm η := hζ.ηm μ
  have hpη : TPer η := hpζ.ηm μ
  set c1 := 1 + |μ|
  have hc1 : 1 ≤ c1 := by show 1 ≤ 1 + |μ|; linarith only [abs_nonneg μ]
  set ε' : ℝ → ℝ := fun x => c1 * (K * Real.exp (-(d * x)))
  set s4 := max (s3 + 1) (Real.log (2 * c1 * K) / d + 1)
  have hs4a : s3 + 1 ≤ s4 := le_max_left _ _
  have hs4b : Real.log (2 * c1 * K) / d + 1 ≤ s4 := le_max_right _ _
  have hε'half : ∀ x ≥ s4 - 1, ε' x ≤ 1 / 2 := by
    intro x hx
    have h1 : Real.log (2 * c1 * K) ≤ d * x := by
      have := (div_le_iff₀ hd).1 (show Real.log (2 * c1 * K) / d ≤ x by linarith only [hx, hs4b])
      linarith only [this]
    have h2 : Real.exp (-(d * x)) ≤ Real.exp (-Real.log (2 * c1 * K)) :=
      Real.exp_le_exp.2 (neg_le_neg h1)
    rw [Real.exp_neg (Real.log _),
      Real.exp_log (mul_pos (mul_pos two_pos (by linarith only [hc1])) hK)] at h2
    simp only [ε']
    calc c1 * (K * Real.exp (-(d * x))) ≤ c1 * (K * (2 * c1 * K)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK.le) (by linarith only [hc1])
      _ = 1 / 2 := by field_simp
  have hε'0 : ∀ x, 0 ≤ ε' x := fun x =>
    mul_nonneg (by linarith only [hc1]) (mul_nonneg hK.le (Real.exp_pos _).le)
  have hε'c : Continuous ε' := continuous_const.mul (continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg))
  -- derivatives
  have hfd : ∀ x > 0, HasDerivAt (Ip η η) (2 * Ip η (pS η) x) x := fun x hx =>
    (Ip_hasDerivAt hη hη hx).congr_deriv (by rw [Ip_comm (pS η) η]; ring)
  have hf1d : ∀ x > 0, HasDerivAt (fun x => 2 * Ip η (pS η) x)
      (2 * ∫ t in (0:ℝ)..1, Qd A η (x, t)) x := fun x hx =>
    (energy_d2 hA hη hpA hpη hx).const_mul 2
  have hfc : ContinuousOn (Ip η η) (Ioi 0) := fun x hx =>
    (hfd x hx).continuousAt.continuousWithinAt
  have hFzc := Fz_cont hζ
  refine ⟨min a d, lt_min ha hd, Real.exp (4 * B) * (5 * (Cr + 2 * Cr ^ 2) * Real.exp a +
    4 * c1 * K * Real.exp d), s4, fun s hs => ?_⟩
  have hs1' : 1 < s := by linarith only [hs, hs4a, hs3, hs10]
  have hIcc : ∀ x ∈ Icc (s - 1) (s + 1), s3 ≤ x ∧ 0 < x := fun x hx =>
    ⟨by linarith only [hx.1, hs, hs4a], by linarith only [hx.1, hs, hs4a, hs3, hs10]⟩
  set g : ℝ → ℝ := fun x => 8 * ε' x * Ip η η x + 2 * ε' x * Fz ζ x
  have hgc : ContinuousOn g (Ioi 0) :=
    (((continuous_const.mul hε'c).continuousOn.mul hfc)).add
      ((continuous_const.mul hε'c).continuousOn.mul hFzc)
  have hmv := mean_value (Ip η η) (fun x => 2 * Ip η (pS η) x)
    (fun x => 2 * ∫ t in (0:ℝ)..1, Qd A η (x, t)) g s hs1' hgc
    (fun x hx => hfd x (hIcc x hx).2) (fun x hx => hf1d x (hIcc x hx).2)
    (fun x _ => show 0 ≤ 8 * ε' x * Ip η η x + 2 * ε' x * Fz ζ x from
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hε'0 x)) (Ip_self_nonneg η x))
        (mul_nonneg (mul_nonneg (by norm_num) (hε'0 x)) (Ip_self_nonneg ζ x)))
    (fun x hx => by
      obtain ⟨hx3, hx0⟩ := hIcc x hx
      have hx1 : s1 ≤ x := hs3.trans hx3
      have hεx : ε' x ≤ 1 / 2 := hε'half x (by linarith only [hx.1, hs])
      have hKx : K * Real.exp (-(d * x)) ≤ ε' x :=
        le_mul_of_one_le_left (mul_pos hK (Real.exp_pos _)).le hc1
      have L := energy_lower2 Sinf hSinf hA hη hζ hx0 (hε'0 x) hεx
        (fun t => (hco x hx1 t).1.trans hKx) (fun t => (hco x hx1 t).2.1.trans hKx)
        (fun t => by
          rw [res_ηm hA hζ hres0 μ _ (mem_Ω hx0), norm_neg]
          exact ((pS A (x, t)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right ((hco x hx1 t).2.1.trans hKx) (norm_nonneg _)))
        (fun t => by
          rw [pres_ηm hA hζ hres0 μ _ (mem_Ω hx0), norm_neg]
          have e1 : ‖pS ζ (x, t)‖ ≤ ‖η (x, t)‖ + |μ| * ‖ζ (x, t)‖ := by
            have : pS ζ (x, t) = η (x, t) + μ • ζ (x, t) := by simp [η, ηm]
            rw [this]
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_eq_abs]
          have b1 := ((pS (pS A) (x, t)).le_opNorm (ζ (x, t))).trans
            (mul_le_mul_of_nonneg_right (hco x hx1 t).2.2 (norm_nonneg _))
          have b2 := ((pS A (x, t)).le_opNorm (pS ζ (x, t))).trans
            (mul_le_mul_of_nonneg_right (hco x hx1 t).2.1 (norm_nonneg _))
          have hKe : 0 ≤ K * Real.exp (-(d * x)) := mul_nonneg hK.le (Real.exp_pos _).le
          have b3 : K * Real.exp (-(d * x)) * ‖pS ζ (x, t)‖ ≤
              K * Real.exp (-(d * x)) * (‖η (x, t)‖ + |μ| * ‖ζ (x, t)‖) :=
            mul_le_mul_of_nonneg_left e1 hKe
          refine (norm_add_le _ _).trans ?_
          have : ε' x = (1 + |μ|) * (K * Real.exp (-(d * x))) := rfl
          rw [this]
          linarith only [b1, b2, b3,
            mul_nonneg (mul_nonneg (abs_nonneg μ) hKe) (norm_nonneg (η (x, t)))])
      have := Ip_self_nonneg (pS η) x
      simp only [g, Fz]
      linarith only [L, this])
    (fun x _ => Ip_self_nonneg η x)
  -- bounds on the interval
  set Fs := Fz ζ s
  set E := Real.exp (4 * B)
  set ρ := Real.exp (-(a * (s - 1)))
  have hρ1 : ρ ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha.le (by linarith only [hs1'])))
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hFx : ∀ x ∈ Icc (s - 1) (s + 1), Fz ζ x ≤ Fs * E := fun x hx =>
    hFc x (hIcc x hx).1 s (by linarith only [hs, hs4a])
      (by rw [abs_le]; constructor <;> linarith only [hx.1, hx.2])
  have hFs0 : 0 < Fs := h.hF s (by linarith only [hs, hs4a, hs3])
  have hFE0 : 0 ≤ Fs * E := mul_nonneg hFs0.le (Real.exp_pos _).le
  have hηx : ∀ x ∈ Icc (s - 1) (s + 1), Ip η η x ≤ Fs * E * (qz ζ x + Cr ^ 2 * ρ) := by
    intro x hx
    obtain ⟨hx3, hx0⟩ := hIcc x hx
    have hF0 := h.hF x (hs3.trans hx3)
    rw [Ip_ηm hζ hx0 hF0 μ]
    have hq := h.hq x (hs3.trans hx3)
    have h1 : |αz ζ x - μ| ≤ Cr * ρ := (hrate x hx3).1.trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hx.1 ha.le))) hCr)
    have h2 : (αz ζ x - μ) ^ 2 ≤ Cr ^ 2 * ρ := by
      rw [← sq_abs]
      calc |αz ζ x - μ| ^ 2 ≤ (Cr * ρ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = Cr ^ 2 * ρ * ρ := by ring
        _ ≤ Cr ^ 2 * ρ * 1 := mul_le_mul_of_nonneg_left hρ1 (mul_nonneg (sq_nonneg _) hρ0.le)
        _ = _ := by ring
    have hFxx := hFx x hx
    have hnn : 0 ≤ qz ζ x + (αz ζ x - μ) ^ 2 := add_nonneg hq (sq_nonneg _)
    calc Fz ζ x * (qz ζ x + (αz ζ x - μ) ^ 2) ≤ Fs * E * (qz ζ x + (αz ζ x - μ) ^ 2) :=
          mul_le_mul_of_nonneg_right hFxx hnn
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl h2) hFE0
  have hqi : IntervalIntegrable (qz ζ) volume (s - 1) (s + 1) :=
    (h.hqc.mono fun x hx => (show s1 ≤ x by linarith only [hx.1, hs, hs4a, hs3])).intervalIntegrable_of_Icc
      (by linarith only)
  have hIq : ∫ x in (s - 1)..(s + 1), qz ζ x ≤ Cr * ρ :=
    (hrate (s - 1) (by linarith only [hs, hs4a])).2 _ (by linarith only)
  have hηi : IntervalIntegrable (Ip η η) volume (s - 1) (s + 1) :=
    (hfc.mono fun x hx => (hIcc x hx).2).intervalIntegrable_of_Icc (by linarith only)
  have hI1 : ∫ x in (s - 1)..(s + 1), Ip η η x ≤ Fs * E * (Cr * ρ + 2 * Cr ^ 2 * ρ) := by
    have := intervalIntegral.integral_mono_on (by linarith only : s - 1 ≤ s + 1) hηi
      ((hqi.add intervalIntegrable_const).const_mul (Fs * E)) hηx
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hqi intervalIntegrable_const,
      intervalIntegral.integral_const] at this
    calc _ ≤ _ := this
      _ ≤ Fs * E * (Cr * ρ + 2 * Cr ^ 2 * ρ) := by
          refine mul_le_mul_of_nonneg_left ?_ hFE0
          simp only [smul_eq_mul]
          linarith only [hIq]
  set εs := ε' (s - 1)
  have hεs : ∀ x ∈ Icc (s - 1) (s + 1), ε' x ≤ εs := fun x hx => by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hx.1 hd.le))) hK.le)
      (by linarith only [hc1])
  have hεs2 : εs ≤ 1 / 2 := hε'half _ (by linarith only [hs])
  have hgx : ∀ x ∈ Icc (s - 1) (s + 1), g x ≤ 4 * Ip η η x + 2 * εs * (Fs * E) := by
    intro x hx
    have h1 := hεs x hx
    have h2 := hε'0 x
    have h3 := Ip_self_nonneg η x
    have h4 := hFx x hx
    have h5 : 0 ≤ Fz ζ x := Ip_self_nonneg ζ x
    show 8 * ε' x * Ip η η x + 2 * ε' x * Fz ζ x ≤ 4 * Ip η η x + 2 * εs * (Fs * E)
    have k1 := mul_le_mul_of_nonneg_right (h1.trans hεs2) h3
    have k2 : ε' x * Fz ζ x ≤ εs * (Fs * E) := mul_le_mul h1 h4 h5 (h2.trans h1)
    linarith only [k1, k2]
  have hgi : IntervalIntegrable g volume (s - 1) (s + 1) :=
    (hgc.mono fun x hx => (hIcc x hx).2).intervalIntegrable_of_Icc (by linarith only)
  have hI2 : ∫ x in (s - 1)..(s + 1), g x ≤
      4 * (∫ x in (s - 1)..(s + 1), Ip η η x) + 4 * εs * (Fs * E) := by
    have := intervalIntegral.integral_mono_on (by linarith only : s - 1 ≤ s + 1) hgi
      ((hηi.const_mul 4).add intervalIntegrable_const) hgx
    rw [intervalIntegral.integral_add (hηi.const_mul 4) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at this
    simp only [smul_eq_mul] at this
    linarith only [this]
  -- assemble
  have hfin : Ip η η s ≤ Fs * E * (5 * (Cr + 2 * Cr ^ 2) * ρ + 4 * εs) := by
    linarith only [hmv, hI1, hI2]
  have hexp1 : ρ ≤ Real.exp a * Real.exp (-(min a d * s)) := by
    simp only [ρ]; rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_right (min_le_left a d) (by linarith only [hs1'] : (0:ℝ) ≤ s)
    linarith only [this]
  have hexp2 : εs ≤ c1 * K * Real.exp d * Real.exp (-(min a d * s)) := by
    simp only [εs, ε']
    rw [mul_assoc c1 K, mul_assoc, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK.le)
      (by linarith only [hc1])
    have := mul_le_mul_of_nonneg_right (min_le_right a d) (by linarith only [hs1'] : (0:ℝ) ≤ s)
    linarith only [this]
  have hFE : 0 ≤ Fs * E := hFE0
  have hP : 0 ≤ 5 * (Cr + 2 * Cr ^ 2) :=
    mul_nonneg (by norm_num) (add_nonneg hCr (mul_nonneg (by norm_num) (sq_nonneg _)))
  calc Ip η η s ≤ Fs * E * (5 * (Cr + 2 * Cr ^ 2) * ρ + 4 * εs) := hfin
    _ ≤ Fs * E * (5 * (Cr + 2 * Cr ^ 2) * (Real.exp a * Real.exp (-(min a d * s))) +
          4 * (c1 * K * Real.exp d * Real.exp (-(min a d * s)))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hexp1 hP)
          (mul_le_mul_of_nonneg_left hexp2 (by norm_num))) hFE
    _ = _ := by ring

end HDecay

end AF_o

section AF_p

/-! The rescaled solution `χ = e^{-μs} ζ`: derivatives and two-sided `L²` bounds. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_p

section AF_q

/-! `∫ |χ(s₁) - χ(s₀)| ≤ ∫_{s₀}^{s₁} ‖∂ₛχ‖_{L²}`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_q

section AF_r

/-! Uniform exponential convergence of `χ(s, ·)` to a nonzero periodic solution `Ψ(·) k`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_r

section AF_s

/-! One-dimensional Caccioppoli and Sobolev inequalities. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma hasDerivAt_integral_Ioi {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {a x : ℝ} (ha : 0 < a)
    (hx : a ≤ x) : HasDerivAt (fun x => ∫ y in a..x, g y) (g x) x := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  refine intervalIntegral.integral_hasDerivAt_right ?_
    (hg.stronglyMeasurableAtFilter isOpen_Ioi x hx0) (hg.continuousAt (isOpen_Ioi.mem_nhds hx0))
  refine (hg.mono ?_).intervalIntegrable
  intro y hy
  rw [uIcc_of_le hx] at hy
  exact lt_of_lt_of_le ha hy.1

/-- Caccioppoli: `f'' ≥ 2G - g` ⇒ `∫_{s-1}^{s+1} G ≤ 24 ∫_{s-2}^{s+2} f + 8 ∫_{s-2}^{s+2} g`. -/
theorem caccioppoli (f f1 f2 G g : ℝ → ℝ) (s : ℝ) (hs : 2 < s) (hfc : ContinuousOn f (Ioi 0))
    (hGc : ContinuousOn G (Ioi 0)) (hgc : ContinuousOn g (Ioi 0))
    (hf : ∀ x ∈ Icc (s - 2) (s + 2), HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Icc (s - 2) (s + 2), HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x ∈ Icc (s - 2) (s + 2), 2 * G x - g x ≤ f2 x)
    (hG0 : ∀ x ∈ Icc (s - 2) (s + 2), 0 ≤ G x) (hg0 : ∀ x ∈ Icc (s - 2) (s + 2), 0 ≤ g x)
    (hf0 : ∀ x ∈ Icc (s - 2) (s + 2), 0 ≤ f x) :
    ∫ x in (s - 1)..(s + 1), G x ≤
      24 * (∫ x in (s - 2)..(s + 2), f x) + 8 * ∫ x in (s - 2)..(s + 2), g x := by
  set a := s - 2
  set b := s + 2
  have ha : 0 < a := by simp only [a]; linarith
  have hab : a ≤ b := by simp only [a, b]; linarith
  set u : ℝ → ℝ := fun x => (x - a) * (b - x)
  set φ : ℝ → ℝ := fun x => u x ^ 2
  set φ1 : ℝ → ℝ := fun x => 2 * u x * (a + b - 2 * x)
  set φ2 : ℝ → ℝ := fun x => 2 * (a + b - 2 * x) ^ 2 - 4 * u x
  have hu : ∀ x, HasDerivAt u (a + b - 2 * x) x := fun x =>
    (((hasDerivAt_id' x).sub_const a).mul ((hasDerivAt_id' x).const_sub b)).congr_deriv
      (by ring)
  have hφ : ∀ x, HasDerivAt φ (φ1 x) x := fun x =>
    ((hu x).pow 2).congr_deriv (by simp only [φ1]; ring)
  have hφ1 : ∀ x, HasDerivAt φ1 (φ2 x) x := fun x =>
    (((hu x).const_mul 2).mul (((hasDerivAt_id' x).const_mul 2).const_sub (a + b))).congr_deriv
      (by simp only [φ2]; ring)
  have huc : Continuous u :=
    (continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id)
  have hφc : Continuous φ := huc.pow 2
  have hφ2c : Continuous φ2 := by
    simp only [φ2]; exact (((continuous_const.sub (continuous_const.mul continuous_id)).pow 2).const_mul
      2).sub (huc.const_mul 4)
  have hsub : ∀ x ∈ Icc a b, 0 < x := fun x hx => lt_of_lt_of_le ha hx.1
  have hc1 : ContinuousOn (fun x => φ2 x * f x) (Ioi 0) := hφ2c.continuousOn.mul hfc
  have hc2 : ContinuousOn (fun x => φ x * (2 * G x - g x)) (Ioi 0) :=
    hφc.continuousOn.mul ((hGc.const_smul (2:ℝ)).sub hgc)
  -- monotone quantity
  have key := le_of_deriv_nonneg_Icc
    (fun x => φ x * f1 x - φ1 x * f x + (∫ y in a..x, φ2 y * f y) -
      ∫ y in a..x, φ y * (2 * G y - g y))
    (fun x => φ x * (f2 x - (2 * G x - g x))) hab
    (fun x hx => by
      have := ((((hφ x).mul (hf1 x hx)).sub ((hφ1 x).mul (hf x hx))).add
        (hasDerivAt_integral_Ioi hc1 ha hx.1)).sub (hasDerivAt_integral_Ioi hc2 ha hx.1)
      refine this.congr_deriv ?_
      ring)
    (fun x hx => by
      have := h2 x hx
      exact mul_nonneg (sq_nonneg _) (by linarith only [this]))
  have hua : u a = 0 := by simp [u]
  have hub : u b = 0 := by simp [u]
  simp only [φ, φ1, hua, hub, intervalIntegral.integral_same] at key
  norm_num at key
  -- `key : ∫ φ (2G - g) ≤ ∫ φ2 f`
  have hIi : ∀ {h : ℝ → ℝ}, ContinuousOn h (Ioi 0) → IntervalIntegrable h volume a b :=
    fun hh => (hh.mono fun x hx => hsub x hx).intervalIntegrable_of_Icc hab
  have hφb : ∀ x ∈ Icc a b, φ x ≤ 16 := by
    intro x hx
    have h1 : 0 ≤ u x := mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    have h2 : u x ≤ 4 := by simp only [u, a, b]; linarith only [sq_nonneg (x - s)]
    have := pow_le_pow_left₀ h1 h2 2
    simp only [φ]; linarith only [this]
  have hφ2b : ∀ x ∈ Icc a b, φ2 x ≤ 48 := by
    intro x hx
    have h1 : 0 ≤ u x := mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    have hx1 : s - 2 ≤ x := hx.1
    have hx2 : x ≤ s + 2 := hx.2
    have h3 : (a + b - 2 * x) ^ 2 ≤ 16 := by
      simp only [a, b]; linarith only [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2)]
    simp only [φ2]; linarith only [h1, h3]
  have hI1 : ∫ x in a..b, φ2 x * f x ≤ 48 * ∫ x in a..b, f x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab (hIi hc1) (hIi (hfc.const_smul (48:ℝ)))
      fun x hx => mul_le_mul_of_nonneg_right (hφ2b x hx) (hf0 x hx)
  have hI2 : ∫ x in a..b, φ x * g x ≤ 16 * ∫ x in a..b, g x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab (hIi (hφc.continuousOn.mul hgc))
      (hIi (hgc.const_smul (16:ℝ)))
      fun x hx => mul_le_mul_of_nonneg_right (hφb x hx) (hg0 x hx)
  have hsplit : ∫ x in a..b, φ x * (2 * G x - g x) =
      (∫ x in a..b, 2 * (φ x * G x)) - ∫ x in a..b, φ x * g x := by
    rw [← intervalIntegral.integral_sub (f := fun x => 2 * (φ x * G x)) (g := fun x => φ x * g x) (hIi ((hφc.continuousOn.mul hGc).const_smul (2:ℝ)))
      (hIi (hφc.continuousOn.mul hgc))]
    congr 1; funext x; ring
  -- lower bound of `∫ φ G`
  have hφG : 2 * ∫ x in (s - 1)..(s + 1), G x ≤ ∫ x in a..b, 2 * (φ x * G x) := by
    have hint : IntervalIntegrable (fun x => 2 * (φ x * G x)) volume a b :=
      hIi ((hφc.continuousOn.mul hGc).const_smul (2:ℝ))
    have hm : a ≤ s - 1 := by simp only [a]; linarith
    have hm' : s + 1 ≤ b := by simp only [b]; linarith
    have hmon := intervalIntegral.integral_mono_interval hm (by linarith : s - 1 ≤ s + 1) hm'
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have h1 := hG0 x ⟨le_of_lt hx.1, hx.2⟩
        have h2 : 0 ≤ φ x := sq_nonneg _
        show 0 ≤ 2 * (φ x * G x)
        exact mul_nonneg zero_le_two (mul_nonneg h2 h1)) hint
    refine le_trans ?_ hmon
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      (((hGc.mono fun x hx => (show (0:ℝ) < x by linarith [hx.1])).intervalIntegrable_of_Icc
        (by linarith)).const_mul 2)
      (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hm (by linarith))
        (mem_uIcc_of_le (by linarith) hm'))) fun x hx => ?_
    have hx' : x ∈ Icc a b := ⟨hm.trans hx.1, hx.2.trans hm'⟩
    have hG := hG0 x hx'
    have : 1 ≤ φ x := by
      have : 1 ≤ u x := by
        simp only [u, a, b]; linarith only [mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2)]
      simp only [φ]; exact one_le_pow₀ this
    linarith only [mul_le_mul_of_nonneg_right this hG]
  linarith only [key, hI1, hI2, hsplit, hφG]

end HDecay

end AF_s

section AF_t

/-! The third `s`-derivative of the coefficient decays exponentially. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma pS_iter_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ × ℝ → F)
    (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    pS^[k] g = fun y => iteratedFDeriv ℝ k g y (fun _ => ((1:ℝ), (0:ℝ))) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) x :=
      (hg.differentiable_iteratedFDeriv (mod_cast ENat.coe_lt_top k)) x
    simp only [pS]
    rw [fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
    rfl

lemma pS3_le (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    |pS (pS (pS g)) x| ≤ ‖iteratedFDeriv ℝ 3 g x‖ := by
  have h : pS (pS (pS g)) x = iteratedFDeriv ℝ 3 g x (fun _ => ((1:ℝ), (0:ℝ))) := by
    show pS^[3] g x = _
    rw [pS_iter_eq g hg 3]
  rw [h]
  have := (iteratedFDeriv ℝ 3 g x).le_opNorm (fun _ => ((1:ℝ), (0:ℝ)))
  simpa using this

lemma pS_TL_fun (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j)) :
    pS (fun p => TL n (S p)) = fun p => TL n (Matrix.of fun i j => pS (fun p => S p i j) p) :=
  funext (hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)))

theorem coeff_exp3 (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (d : ℝ)
    (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d) :
    ∃ K > 0, ∃ s1 > 0, ∀ s ≥ s1, ∀ t,
      ‖pS (pS (pS (fun p => TL n (S p)))) (s, t)‖ ≤ K * Real.exp (-(d * s)) := by
  obtain ⟨c, hc, hcM⟩ := op_small (n := n)
  have h := fun i j => (hSas i j).2 3
  choose Cf s1f hs1f using h
  set Cm := ∑ i, ∑ j, |Cf i j| + 1
  set s1 := ∑ i, ∑ j, |s1f i j| + 1
  have hsum : ∀ (g : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) i j, g i j ≤ ∑ i, ∑ j, |g i j| := by
    intro g i j
    refine (le_abs_self _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, |g i j|)
      (fun i _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => |g i j|) (fun j _ => by positivity)
      (Finset.mem_univ j)
  have hs1pos : 0 < s1 := by
    have : 0 ≤ ∑ i, ∑ j, |s1f i j| := by positivity
    linarith
  have hCm : 0 < Cm := by
    have : 0 ≤ ∑ i, ∑ j, |Cf i j| := by positivity
    linarith
  -- three applications of `pS_TL_fun`
  set S1 : ℝ × ℝ → Mat n := fun p => Matrix.of fun i j => pS (fun p => S p i j) p
  have hS1 : ∀ i j, ContDiff ℝ ∞ (fun p => S1 p i j) := contDiff_of_pS S hS
  set S2 : ℝ × ℝ → Mat n := fun p => Matrix.of fun i j => pS (fun p => S1 p i j) p
  have hS2 : ∀ i j, ContDiff ℝ ∞ (fun p => S2 p i j) := contDiff_of_pS S1 hS1
  have e : pS (pS (pS (fun p => TL n (S p)))) = fun p =>
      TL n (Matrix.of fun i j => pS (fun p => S2 p i j) p) := by
    rw [pS_TL_fun S hS, show (fun p => TL n (Matrix.of fun i j => pS (fun p => S p i j) p)) =
      fun p => TL n (S1 p) from rfl, pS_TL_fun S1 hS1,
      show (fun p => TL n (Matrix.of fun i j => pS (fun p => S1 p i j) p)) =
      fun p => TL n (S2 p) from rfl, pS_TL_fun S2 hS2]
  refine ⟨c * Cm, by positivity, s1, hs1pos, fun s hs t => ?_⟩
  rw [e, mul_assoc]
  refine hcM _ _ (by positivity) fun i j => ?_
  have hs' : s1f i j ≤ s := by have := hsum s1f i j; linarith
  have hb := hs1f i j s hs' t
  have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) :=
    (hS i j).sub ((hSinf' i j).comp contDiff_snd)
  have e2 : (fun p => S2 p i j) = pS (pS (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j)) := by
    simp only [S2, S1, Matrix.of_apply]
    rw [pS_entry S hS Sinf hSinf' i j]
  simp only [Matrix.of_apply]
  rw [e2]
  refine ((pS3_le _ hg _).trans hb).trans ?_
  have : Cf i j ≤ Cm := by have := hsum Cf i j; linarith
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

end HDecay

end AF_t

section AF_u

/-! Second energy level: residual identities and an energy inequality with a scalar weight. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma res_pS {A : ℝ × ℝ → Op n} {η : ℝ × ℝ → Vec n} (hA : Sm A) (hη : Sm η) :
    ∀ x ∈ Ω, res A (pS η) x = pS (res A η) x - pS A x (η x) := by
  intro x hx
  have e : res A η = (pS η + fun y => Jop n (pT η y)) + fun y => A y (η y) := rfl
  rw [e, pS_add (hη.dS.add hη.dT.jop) (hA.apply hη) hx, pS_add hη.dS hη.dT.jop hx,
    pS_constOp _ hη.dT hx, pS_pT hη hx, pS_apply hA hη hx]
  simp only [res]; abel

/-- `res A (∂ₛ ηm)` for a solution `ζ` -/
lemma res_η2 {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (μ : ℝ) :
    ∀ x ∈ Ω, res A (pS (ηm ζ μ)) x =
      -(pS (pS A) x (ζ x) + pS A x (pS ζ x)) - pS A x (ηm ζ μ x) := by
  intro x hx
  rw [res_pS hA (hζ.ηm μ) x hx, pres_ηm hA hζ hres0 μ x hx]

lemma pres_η2 {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (μ : ℝ) :
    ∀ x ∈ Ω, pS (res A (pS (ηm ζ μ))) x =
      -(pS (pS (pS A)) x (ζ x) + pS (pS A) x (pS ζ x) + (pS (pS A) x (pS ζ x) +
        pS A x (pS (pS ζ) x))) - (pS (pS A) x (ηm ζ μ x) + pS A x (pS (ηm ζ μ) x)) := by
  intro x hx
  have hη := hζ.ηm μ
  have hf1 : Sm fun y => pS (pS A) y (ζ y) := hA.dS.dS.apply hζ
  have hf2 : Sm fun y => pS A y (pS ζ y) := hA.dS.apply hζ.dS
  have hf3 : Sm fun y => pS A y (ηm ζ μ y) := hA.dS.apply hη
  rw [pS_congr (v := (-((fun y => pS (pS A) y (ζ y)) + fun y => pS A y (pS ζ y))) -
    fun y => pS A y (ηm ζ μ y)) (fun y hy => by
      rw [res_η2 hA hζ hres0 μ y hy]; rfl) hx]
  rw [pS_sub (hf1.add hf2).neg hf3 hx, pS_neg, pS_add hf1 hf2 hx, pS_apply hA.dS.dS hζ hx,
    pS_apply hA.dS hζ.dS hx, pS_apply hA.dS hη hx]

/-- `energy_lower2` with a scalar weight `W` in place of `‖w‖` -/
theorem energy_lower3 (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    {A : ℝ × ℝ → Op n} (hA : Sm A) {η : ℝ × ℝ → Vec n} (hη : Sm η) {W : ℝ × ℝ → ℝ}
    (hW : ContinuousOn W Ω) {s : ℝ} (hs : 0 < s) (hW0 : ∀ t, 0 ≤ W (s, t)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2)
    (hA1 : ∀ t, ‖A (s, t) - TL n (Sinf t)‖ ≤ ε) (hA2 : ∀ t, ‖pS A (s, t)‖ ≤ ε)
    (hr : ∀ t, ‖res A η (s, t)‖ ≤ ε * W (s, t))
    (hr' : ∀ t, ‖pS (res A η) (s, t)‖ ≤ ε * (W (s, t) + ‖η (s, t)‖)) :
    Ip (pS η) (pS η) s - 4 * ε * Ip η η s - ε * ∫ t in (0:ℝ)..1, W (s, t) ^ 2 ≤
      ∫ t in (0:ℝ)..1, Qd A η (s, t) := by
  have hξ := hη.dS
  have iξ := ii (hξ.cont.inner hξ.cont) hs
  have iη := ii (hη.cont.inner hη.cont) hs
  have iw : IntervalIntegrable (fun t => W (s, t) ^ 2) volume 0 1 :=
    ((cont_slice hW hs).pow 2).intervalIntegrable _ _
  have hpt : ∀ t, ⟪pS η (s, t), pS η (s, t)⟫ - 4 * ε * ⟪η (s, t), η (s, t)⟫ -
      ε * W (s, t) ^ 2 ≤ Qd A η (s, t) := by
    intro t
    set ξv := pS η (s, t)
    set ηv := η (s, t)
    set wv := W (s, t)
    set D := A (s, t) - TL n (Sinf t)
    have hsym : ⟪A (s, t) ηv, ξv⟫ - ⟪ηv, A (s, t) ξv⟫ = ⟪D ηv, ξv⟫ - ⟪ηv, D ξv⟫ := by
      have := inner_symm (hS.2.2 t) ηv ξv
      simp only [D, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
      linarith only [this]
    have b1 := abs_inner_op D ηv ξv
    have b2 : |⟪ηv, D ξv⟫| ≤ ‖ηv‖ * (‖D‖ * ‖ξv‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _))
    have b3 : |⟪res A η (s, t), ξv⟫| ≤ ε * wv * ‖ξv‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hr t) (norm_nonneg _))
    have b4 : |⟪ηv, pS (res A η) (s, t)⟫| ≤ ‖ηv‖ * (ε * (wv + ‖ηv‖)) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hr' t) (norm_nonneg _))
    have b5 : |⟪ηv, pS A (s, t) ηv⟫| ≤ ‖ηv‖ * (‖pS A (s, t)‖ * ‖ηv‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ((pS A (s, t)).le_opNorm _) (norm_nonneg _))
    have hD := hA1 t
    have hAs := hA2 t
    have q : Qd A η (s, t) = 2 * ⟪ξv, ξv⟫ + (⟪D ηv, ξv⟫ - ⟪ηv, D ξv⟫) - ⟪res A η (s, t), ξv⟫ +
        ⟪ηv, pS (res A η) (s, t)⟫ - ⟪ηv, pS A (s, t) ηv⟫ := by
      rw [← hsym]; simp only [Qd]; ring
    rw [q]
    simp only [real_inner_self_eq_norm_sq]
    have na := norm_nonneg ξv
    have nb := norm_nonneg ηv
    have nc : 0 ≤ wv := hW0 t
    have e1 : ‖D‖ * ‖ηv‖ * ‖ξv‖ ≤ ε * ‖ηv‖ * ‖ξv‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD nb) na
    have e2 : ‖ηv‖ * (‖D‖ * ‖ξv‖) ≤ ‖ηv‖ * (ε * ‖ξv‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD na) nb
    have e5 : ‖ηv‖ * (‖pS A (s, t)‖ * ‖ηv‖) ≤ ‖ηv‖ * (ε * ‖ηv‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAs nb) nb
    have a1 := neg_abs_le ⟪D ηv, ξv⟫
    have a2 := le_abs_self ⟪ηv, D ξv⟫
    have a3 := le_abs_self ⟪res A η (s, t), ξv⟫
    have a4 := neg_abs_le ⟪ηv, pS (res A η) (s, t)⟫
    have a5 := le_abs_self ⟪ηv, pS A (s, t) ηv⟫
    have h1 := mul_nonneg hε0 (sq_nonneg (‖ξv‖ - ‖ηv‖))
    have h2 := mul_nonneg hε0 (sq_nonneg (‖ξv‖ - wv))
    have h3 := mul_nonneg hε0 (sq_nonneg (‖ηv‖ - wv))
    have h4 := mul_nonneg (sub_nonneg.2 hε) (sq_nonneg ‖ξv‖)
    have h5 := mul_nonneg hε0 (sq_nonneg ‖ξv‖)
    have h6 := mul_nonneg hε0 (sq_nonneg ‖ηv‖)
    linear_combination a1 + b1 + e1 + a2 + b2 + e2 + a3 + b3 + a4 + b4 + a5 + b5 + e5 + h1 +
      h2 / 2 + h3 / 2 + 2 * h4 + h5 / 2 + h6 / 2
  have hQ := ii (Qd_cont hA hη) hs
  have hint := intervalIntegral.integral_mono_on zero_le_one
    ((iξ.sub (iη.const_mul _)).sub (iw.const_mul _)) hQ fun t _ => hpt t
  rw [intervalIntegral.integral_sub (iξ.sub (iη.const_mul _)) (iw.const_mul _),
    intervalIntegral.integral_sub iξ (iη.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  exact hint

end HDecay

end AF_u

section AF_v

/-! `‖∂ₛ(∂ₛζ - μζ)‖²_{L²}(s) ≤ C ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma int_le_of_le {h : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hc : ContinuousOn h (Ioi 0))
    (ha : 0 < a) (hb : ∀ x ∈ Icc a b, h x ≤ M) : ∫ x in a..b, h x ≤ (b - a) * M := by
  have hi : IntervalIntegrable h volume a b :=
    (hc.mono fun x hx => lt_of_lt_of_le ha hx.1).intervalIntegrable_of_Icc hab
  have := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hb
  simpa using this

/-- the two pointwise energy inequalities at a fixed `x`, with `k` bounding the coefficients -/
theorem lev12 (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) {A : ℝ × ℝ → Op n}
    {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ) (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (μ : ℝ)
    {x k : ℝ} (hx0 : 0 < x) (hk0 : 0 ≤ k)
    (hco : ∀ t, ‖A (x, t) - TL n (Sinf t)‖ ≤ k ∧ ‖pS A (x, t)‖ ≤ k ∧ ‖pS (pS A) (x, t)‖ ≤ k ∧
      ‖pS (pS (pS A)) (x, t)‖ ≤ k) (hk : (2 + |μ|) ^ 2 * k ≤ 1 / 2) :
    2 * Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) x - (8 * ((2 + |μ|) ^ 2 * k) * Ip (ηm ζ μ) (ηm ζ μ) x +
      2 * ((2 + |μ|) ^ 2 * k) * Fz ζ x) ≤ 2 * ∫ t in (0:ℝ)..1, Qd A (ηm ζ μ) (x, t) ∧
    -(8 * ((2 + |μ|) ^ 2 * k) * Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) x + 4 * ((2 + |μ|) ^ 2 * k) *
      (Fz ζ x + Ip (ηm ζ μ) (ηm ζ μ) x)) ≤
      2 * ∫ t in (0:ℝ)..1, Qd A (pS (ηm ζ μ)) (x, t) := by
  set η := ηm ζ μ
  have hη : Sm η := hζ.ηm μ
  set η2 := pS η
  have hη2 : Sm η2 := hη.dS
  set cK := (2 + |μ|) ^ 2
  have hm := abs_nonneg μ
  have hcK : 4 ≤ cK := by show 4 ≤ (2 + |μ|) ^ 2; nlinarith only [hm]
  set ε := cK * k
  have hε0 : 0 ≤ ε := mul_nonneg (by linarith only [hcK]) hk0
  have hkε : k ≤ ε := le_mul_of_one_le_left hk0 (by linarith only [hcK])
  have hc1 : k * (1 + |μ|) ≤ ε := by
    show k * (1 + |μ|) ≤ (2 + |μ|) ^ 2 * k
    linarith only [hk0, mul_nonneg hk0 hm, mul_nonneg hk0 (sq_nonneg |μ|)]
  have hc2 : k * 2 ≤ ε := by
    have := mul_le_mul_of_nonneg_right hcK hk0
    show k * 2 ≤ cK * k
    linarith only [this, hk0]
  have hpSζ : ∀ t, ‖pS ζ (x, t)‖ ≤ ‖η (x, t)‖ + |μ| * ‖ζ (x, t)‖ := by
    intro t
    have : pS ζ (x, t) = η (x, t) + μ • ζ (x, t) := by simp [η, ηm]
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  constructor
  · have L := energy_lower2 Sinf hSinf hA hη hζ hx0 hε0 hk
      (fun t => (hco t).1.trans hkε) (fun t => (hco t).2.1.trans hkε)
      (fun t => by
        rw [res_ηm hA hζ hres0 μ _ (mem_Ω hx0), norm_neg]
        exact ((pS A (x, t)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right ((hco t).2.1.trans hkε) (norm_nonneg _)))
      (fun t => by
        rw [pres_ηm hA hζ hres0 μ _ (mem_Ω hx0), norm_neg]
        have b1 := ((pS (pS A) (x, t)).le_opNorm (ζ (x, t))).trans
          (mul_le_mul_of_nonneg_right (hco t).2.2.1 (norm_nonneg _))
        have b2 := ((pS A (x, t)).le_opNorm (pS ζ (x, t))).trans
          (mul_le_mul_of_nonneg_right (hco t).2.1 (norm_nonneg _))
        have b3 := mul_le_mul_of_nonneg_left (hpSζ t) hk0
        refine (norm_add_le _ _).trans ?_
        have hn1 := norm_nonneg (η (x, t)); have hn2 := norm_nonneg (ζ (x, t))
        linarith only [b1, b2, b3, mul_le_mul_of_nonneg_right hc1 hn2,
          mul_le_mul_of_nonneg_right hkε hn1])
    have := Ip_self_nonneg (pS η) x
    change Ip η2 η2 x - 4 * ε * Ip η η x - ε * Ip ζ ζ x ≤ _ at L
    simp only [Fz]
    linarith only [L, this]
  · set W : ℝ × ℝ → ℝ := fun y => ‖ζ y‖ + ‖η y‖
    have hW : ContinuousOn W Ω := hζ.cont.norm.add hη.cont.norm
    have hpSpSζ : ∀ t, ‖pS (pS ζ) (x, t)‖ ≤ ‖η2 (x, t)‖ + |μ| * ‖pS ζ (x, t)‖ := by
      intro t
      have e1 : pS ζ = fun y => η y + μ • ζ y := by funext y; simp [η, ηm]
      have : pS (pS ζ) (x, t) = η2 (x, t) + μ • pS ζ (x, t) := by
        rw [show pS (pS ζ) = pS (η + fun y => μ • ζ y) by rw [e1]; rfl,
          pS_add hη (hζ.const_smul μ) (mem_Ω hx0), pS_smul' μ hζ (mem_Ω hx0)]
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
    have L := energy_lower3 Sinf hSinf hA hη2 hW hx0 (fun t => add_nonneg (norm_nonneg _) (norm_nonneg _)) hε0 hk
      (fun t => (hco t).1.trans hkε) (fun t => (hco t).2.1.trans hkε)
      (fun t => by
        rw [res_η2 hA hζ hres0 μ _ (mem_Ω hx0)]
        have b1 := ((pS (pS A) (x, t)).le_opNorm (ζ (x, t))).trans
          (mul_le_mul_of_nonneg_right (hco t).2.2.1 (norm_nonneg _))
        have b2 := ((pS A (x, t)).le_opNorm (pS ζ (x, t))).trans
          (mul_le_mul_of_nonneg_right (hco t).2.1 (norm_nonneg _))
        have b3 := ((pS A (x, t)).le_opNorm (η (x, t))).trans
          (mul_le_mul_of_nonneg_right (hco t).2.1 (norm_nonneg _))
        have b4 := mul_le_mul_of_nonneg_left (hpSζ t) hk0
        have hn : ‖-(pS (pS A) (x, t) (ζ (x, t)) + pS A (x, t) (pS ζ (x, t))) -
            pS A (x, t) (η (x, t))‖ ≤ k * ((1 + |μ|) * ‖ζ (x, t)‖ + 2 * ‖η (x, t)‖) := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_neg]
          have := norm_add_le (pS (pS A) (x, t) (ζ (x, t))) (pS A (x, t) (pS ζ (x, t)))
          linarith only [this, b1, b2, b3, b4]
        refine hn.trans ?_
        have hn1 := norm_nonneg (η (x, t)); have hn2 := norm_nonneg (ζ (x, t))
        show _ ≤ ε * (‖ζ (x, t)‖ + ‖η (x, t)‖)
        linarith only [mul_le_mul_of_nonneg_right hc1 hn2, mul_le_mul_of_nonneg_right hc2 hn1])
      (fun t => by
        rw [pres_η2 hA hζ hres0 μ _ (mem_Ω hx0)]
        have k1 := hco t
        have a1 := ((pS (pS (pS A)) (x, t)).le_opNorm (ζ (x, t))).trans
          (mul_le_mul_of_nonneg_right k1.2.2.2 (norm_nonneg _))
        have a2 := ((pS (pS A) (x, t)).le_opNorm (pS ζ (x, t))).trans
          (mul_le_mul_of_nonneg_right k1.2.2.1 (norm_nonneg _))
        have a3 := ((pS A (x, t)).le_opNorm (pS (pS ζ) (x, t))).trans
          (mul_le_mul_of_nonneg_right k1.2.1 (norm_nonneg _))
        have a4 := ((pS (pS A) (x, t)).le_opNorm (η (x, t))).trans
          (mul_le_mul_of_nonneg_right k1.2.2.1 (norm_nonneg _))
        have a5 := ((pS A (x, t)).le_opNorm (η2 (x, t))).trans
          (mul_le_mul_of_nonneg_right k1.2.1 (norm_nonneg _))
        have hsum : ‖-(pS (pS (pS A)) (x, t) (ζ (x, t)) + pS (pS A) (x, t) (pS ζ (x, t)) +
            (pS (pS A) (x, t) (pS ζ (x, t)) + pS A (x, t) (pS (pS ζ) (x, t)))) -
            (pS (pS A) (x, t) (η (x, t)) + pS A (x, t) (η2 (x, t)))‖ ≤
            k * ‖ζ (x, t)‖ + k * ‖pS ζ (x, t)‖ + (k * ‖pS ζ (x, t)‖ + k * ‖pS (pS ζ) (x, t)‖) +
              (k * ‖η (x, t)‖ + k * ‖η2 (x, t)‖) := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_neg]
          exact add_le_add ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add a1 a2))
            ((norm_add_le _ _).trans (add_le_add a2 a3))))
            ((norm_add_le _ _).trans (add_le_add a4 a5))
        refine hsum.trans ?_
        show _ ≤ ε * ((‖ζ (x, t)‖ + ‖η (x, t)‖) + ‖η2 (x, t)‖)
        have hps := hpSζ t
        have hpps := hpSpSζ t
        have hz := norm_nonneg (ζ (x, t)); have hy := norm_nonneg (η (x, t))
        have hw := norm_nonneg (η2 (x, t))
        generalize ‖ζ (x, t)‖ = z at *
        generalize ‖η (x, t)‖ = y at *
        generalize ‖η2 (x, t)‖ = w at *
        generalize ‖pS ζ (x, t)‖ = p1 at *
        generalize ‖pS (pS ζ) (x, t)‖ = p2 at *
        have e1 : k * p1 ≤ k * (y + |μ| * z) := mul_le_mul_of_nonneg_left hps hk0
        have e2 : k * p2 ≤ k * (w + |μ| * p1) := mul_le_mul_of_nonneg_left hpps hk0
        have e3 : k * (|μ| * p1) ≤ k * (|μ| * (y + |μ| * z)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hps hm) hk0
        have f1 : 0 ≤ k * ((3 + 2 * |μ|) * z) :=
          mul_nonneg hk0 (mul_nonneg (by linarith only [hm]) hz)
        have f2 : 0 ≤ k * ((1 + 3 * |μ| + |μ| ^ 2) * y) :=
          mul_nonneg hk0 (mul_nonneg (add_nonneg (by linarith only [hm]) (sq_nonneg _)) hy)
        have f3 : 0 ≤ k * ((2 + 4 * |μ| + |μ| ^ 2) * w) :=
          mul_nonneg hk0 (mul_nonneg (add_nonneg (by linarith only [hm]) (sq_nonneg _)) hw)
        simp only [ε, cK]
        linarith only [e1, e2, e3, f1, f2, f3])
    have hW2 : ∫ t in (0:ℝ)..1, W (x, t) ^ 2 ≤ 2 * (Fz ζ x + Ip η η x) := by
      have hc1 := cont_slice hζ.cont hx0
      have hc2 := cont_slice hη.cont hx0
      have := intervalIntegral.integral_mono_on
        (f := fun t => (‖ζ (x, t)‖ + ‖η (x, t)‖) ^ 2)
        (g := fun t => 2 * (⟪ζ (x, t), ζ (x, t)⟫ + ⟪η (x, t), η (x, t)⟫)) zero_le_one
        (((hc1.norm.add hc2.norm).pow 2).intervalIntegrable (μ := volume) 0 1)
        (((hc1.inner hc1).add (hc2.inner hc2)).const_mul 2 |>.intervalIntegrable (μ := volume) 0 1)
        (fun t _ => by
          show (‖ζ (x, t)‖ + ‖η (x, t)‖) ^ 2 ≤ 2 * (⟪ζ (x, t), ζ (x, t)⟫ + ⟪η (x, t), η (x, t)⟫)
          rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
          linarith only [sq_nonneg (‖ζ (x, t)‖ - ‖η (x, t)‖)])
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (f := fun t => ⟪ζ (x, t), ζ (x, t)⟫) (g := fun t => ⟪η (x, t), η (x, t)⟫)
        ((hc1.inner hc1).intervalIntegrable _ _) ((hc2.inner hc2).intervalIntegrable _ _)] at this
      simpa [Fz, Ip] using this
    have := Ip_self_nonneg (pS η2) x
    have hεW := mul_le_mul_of_nonneg_left hW2 hε0
    change Ip (pS η2) (pS η2) x - 4 * ε * Ip η2 η2 x - ε * _ ≤ _ at L
    linarith only [L, this, hεW]

end HDecay

end AF_v

section AF_w

/-! `‖∂ₛ(∂ₛζ - μζ)‖²_{L²}(s) ≤ C ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

set_option maxHeartbeats 800000 in
theorem eta2_bound (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) {A : ℝ × ℝ → Op n}
    {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hpA : TPer A) (hζ : Sm ζ) (hpζ : TPer ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) {s1 K d : ℝ}
    (h : EtaHyp (αz ζ) (qz ζ) (Fz ζ) s1 K d)
    (hco : ∀ s ≥ s1, ∀ t, ‖A (s, t) - TL n (Sinf t)‖ ≤ K * Real.exp (-(d * s)) ∧
        ‖pS A (s, t)‖ ≤ K * Real.exp (-(d * s)) ∧
        ‖pS (pS A) (s, t)‖ ≤ K * Real.exp (-(d * s)))
    {K3 s13 : ℝ} (hco3 : ∀ s ≥ s13, ∀ t, ‖pS (pS (pS A)) (s, t)‖ ≤ K3 * Real.exp (-(d * s)))
    (μ a Cr s3 : ℝ) (ha : 0 < a) (hs3 : s1 ≤ s3)
    (hrate : ∀ s ≥ s3, |αz ζ s - μ| ≤ Cr * Real.exp (-(a * s)) ∧
        ∀ T ≥ s, ∫ x in s..T, qz ζ x ≤ Cr * Real.exp (-(a * s))) :
    ∃ C2 s5, ∀ s ≥ s5, Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) s ≤ C2 * Fz ζ s := by
  obtain ⟨a', ha', C', s4, hC'⟩ := eta_decay Sinf hSinf hA hpA hζ hpζ hres0 h hco μ a Cr s3 ha hs3
    hrate
  have hK := h.hK
  have hd := h.hd
  have hs10 := h.hs1
  -- `F` comparison (as in `eta_decay`)
  have hCr : 0 ≤ Cr := by
    have := (hrate s3 le_rfl).1
    have h0 := abs_nonneg (αz ζ s3 - μ)
    by_contra hc; push Not at hc
    have : Cr * Real.exp (-(a * s3)) < 0 := mul_neg_of_neg_of_pos hc (Real.exp_pos _)
    linarith
  set B := |μ| + Cr
  have hB : 0 ≤ B := add_nonneg (abs_nonneg μ) hCr
  have hαB : ∀ s ≥ s3, |αz ζ s| ≤ B := by
    intro s hs
    have h1 := (hrate s hs).1
    have h2 : Cr * Real.exp (-(a * s)) ≤ Cr := by
      have : Real.exp (-(a * s)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha.le (hs10.trans_le (hs3.trans hs)).le))
      exact mul_le_of_le_one_right hCr this
    calc |αz ζ s| = |(αz ζ s - μ) + μ| := by ring_nf
      _ ≤ |αz ζ s - μ| + |μ| := abs_add_le _ _
      _ ≤ B := by show _ ≤ |μ| + Cr; linarith only [h1, h2]
  have hFc := F_compare (Fz ζ) (αz ζ) s3 B hB (fun s hs => h.hFd s (hs3.trans hs))
    (fun s hs => h.hF s (hs3.trans hs)) hαB
  have hC'0 : 0 ≤ C' := by
    set s' := max s4 s3
    have h1 := hC' s' (le_max_left _ _)
    have h2 := Ip_self_nonneg (ηm ζ μ) s'
    have h3 := h.hF s' (hs3.trans (le_max_right _ _))
    by_contra hc; push Not at hc
    have : C' * Real.exp (-(a' * s')) * Fz ζ s' < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc (Real.exp_pos _)) h3
    linarith
  set η := ηm ζ μ
  have hη : Sm η := hζ.ηm μ
  have hpη : TPer η := hpζ.ηm μ
  set η2 := pS η
  have hη2 : Sm η2 := hη.dS
  have hpη2 : TPer η2 := hpη.pS
  set Kb := max K K3
  have hKb : 0 < Kb := lt_of_lt_of_le hK (le_max_left _ _)
  set cK := (2 + |μ|) ^ 2
  have hcK : 4 ≤ cK := by
    have := abs_nonneg μ; show 4 ≤ (2 + |μ|) ^ 2; nlinarith only [this]
  set ε : ℝ → ℝ := fun x => cK * (Kb * Real.exp (-(d * x)))
  have hε0 : ∀ x, 0 ≤ ε x := fun x =>
    mul_nonneg (by linarith only [hcK]) (mul_nonneg hKb.le (Real.exp_pos _).le)
  have hεc : Continuous ε := continuous_const.mul (continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg))
  set s5 := max (max (s3 + 2) (s13 + 2)) (max (s4 + 2) (Real.log (2 * cK * Kb) / d + 2))
  have h5a : s3 + 2 ≤ s5 := (le_max_left _ _).trans (le_max_left _ _)
  have h5b : s13 + 2 ≤ s5 := (le_max_right _ _).trans (le_max_left _ _)
  have h5c : s4 + 2 ≤ s5 := (le_max_left _ _).trans (le_max_right _ _)
  have h5d : Real.log (2 * cK * Kb) / d + 2 ≤ s5 := (le_max_right _ _).trans (le_max_right _ _)
  have hεhalf : ∀ x ≥ s5 - 2, ε x ≤ 1 / 2 := by
    intro x hx
    have h1 : Real.log (2 * cK * Kb) ≤ d * x := by
      have := (div_le_iff₀ hd).1 (show Real.log (2 * cK * Kb) / d ≤ x by linarith only [hx, h5d])
      linarith only [this]
    have h2 : Real.exp (-(d * x)) ≤ Real.exp (-Real.log (2 * cK * Kb)) :=
      Real.exp_le_exp.2 (neg_le_neg h1)
    rw [Real.exp_neg (Real.log _),
      Real.exp_log (mul_pos (mul_pos two_pos (by linarith only [hcK])) hKb)] at h2
    simp only [ε]
    calc cK * (Kb * Real.exp (-(d * x))) ≤ cK * (Kb * (2 * cK * Kb)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hKb.le) (by linarith only [hcK])
      _ = 1 / 2 := by field_simp
  have hKε : ∀ x, K * Real.exp (-(d * x)) ≤ ε x := fun x => by
    have h1 : K * Real.exp (-(d * x)) ≤ Kb * Real.exp (-(d * x)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have h2 : Kb * Real.exp (-(d * x)) ≤ cK * (Kb * Real.exp (-(d * x))) :=
      le_mul_of_one_le_left (mul_pos hKb (Real.exp_pos (-(d * x)))).le (by linarith only [hcK])
    exact h1.trans h2
  have hK3ε : ∀ x, K3 * Real.exp (-(d * x)) ≤ Kb * Real.exp (-(d * x)) := fun x =>
    mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  -- the energies
  set Fη := Ip η η
  set Gη := Ip η2 η2
  set F := Fz ζ
  have hFηd : ∀ x > 0, HasDerivAt Fη (2 * Ip η η2 x) x := fun x hx =>
    (Ip_hasDerivAt hη hη hx).congr_deriv (by rw [Ip_comm η2 η]; ring)
  have hFη1d : ∀ x > 0, HasDerivAt (fun x => 2 * Ip η η2 x)
      (2 * ∫ t in (0:ℝ)..1, Qd A η (x, t)) x := fun x hx =>
    (energy_d2 hA hη hpA hpη hx).const_mul 2
  have hGηd : ∀ x > 0, HasDerivAt Gη (2 * Ip η2 (pS η2) x) x := fun x hx =>
    (Ip_hasDerivAt hη2 hη2 hx).congr_deriv (by rw [Ip_comm (pS η2) η2]; ring)
  have hGη1d : ∀ x > 0, HasDerivAt (fun x => 2 * Ip η2 (pS η2) x)
      (2 * ∫ t in (0:ℝ)..1, Qd A η2 (x, t)) x := fun x hx =>
    (energy_d2 hA hη2 hpA hpη2 hx).const_mul 2
  have hFηc : ContinuousOn Fη (Ioi 0) := fun x hx => (hFηd x hx).continuousAt.continuousWithinAt
  have hGηc : ContinuousOn Gη (Ioi 0) := fun x hx => (hGηd x hx).continuousAt.continuousWithinAt
  have hFc' : ContinuousOn F (Ioi 0) := Fz_cont hζ
  -- pointwise inequalities for `x ≥ s5 - 2`
  have hlev : ∀ x ≥ s5 - 2,
      2 * Gη x - (8 * ε x * Fη x + 2 * ε x * F x) ≤ 2 * ∫ t in (0:ℝ)..1, Qd A η (x, t) ∧
      -(8 * ε x * Gη x + 4 * ε x * (F x + Fη x)) ≤ 2 * ∫ t in (0:ℝ)..1, Qd A η2 (x, t) := by
    intro x hx
    have hx1 : s1 ≤ x := by linarith only [hx, h5a, hs3]
    have hx13 : s13 ≤ x := by linarith only [hx, h5b]
    have hx0 : 0 < x := by linarith only [hx, h5a, hs3, hs10]
    have hKb1 : K * Real.exp (-(d * x)) ≤ Kb * Real.exp (-(d * x)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have := lev12 Sinf hSinf hA hζ hres0 μ hx0 (mul_nonneg hKb.le (Real.exp_pos _).le)
      (fun t => ⟨(hco x hx1 t).1.trans hKb1, (hco x hx1 t).2.1.trans hKb1,
        (hco x hx1 t).2.2.trans hKb1, (hco3 x hx13 t).trans (hK3ε x)⟩) (hεhalf x hx)
    exact this
  refine ⟨5 * (24 * (4 * C' * Real.exp (4 * B)) + 8 * (4 * ((4 * C' + 1) * Real.exp (4 * B)))) +
    2 * (2 * ((1 + C') * Real.exp (4 * B))), s5, fun s hs => ?_⟩
  have hs2 : 2 < s := by linarith only [hs, h5a, hs3, hs10]
  set E := Real.exp (4 * B)
  have hE : 0 < E := Real.exp_pos _
  have hFs : 0 < F s := h.hF s (by linarith only [hs, h5a, hs3])
  have hIcc : ∀ x ∈ Icc (s - 2) (s + 2), s5 - 2 ≤ x ∧ 0 < x ∧ s3 ≤ x ∧ s4 ≤ x := fun x hx =>
    ⟨by linarith only [hx.1, hs], by linarith only [hx.1, hs, h5a, hs3, hs10],
      by linarith only [hx.1, hs, h5a], by linarith only [hx.1, hs, h5c]⟩
  have hFx : ∀ x ∈ Icc (s - 2) (s + 2), F x ≤ F s * E := fun x hx =>
    hFc x (hIcc x hx).2.2.1 s (by linarith only [hs, h5a])
      (by rw [abs_le]; constructor <;> linarith only [hx.1, hx.2])
  have hFηx : ∀ x ∈ Icc (s - 2) (s + 2), Fη x ≤ C' * (F s * E) := by
    intro x hx
    have h1 := hC' x (hIcc x hx).2.2.2
    have h2 : Real.exp (-(a' * x)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha'.le (hIcc x hx).2.1.le))
    have h3 : 0 ≤ F x := Ip_self_nonneg ζ x
    calc Fη x ≤ C' * Real.exp (-(a' * x)) * F x := h1
      _ ≤ C' * 1 * F x := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC'0) h3
      _ ≤ C' * (F s * E) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (hFx x hx) hC'0
  -- Caccioppoli for level 1
  set g1 : ℝ → ℝ := fun x => 8 * ε x * Fη x + 2 * ε x * F x
  have hg1c : ContinuousOn g1 (Ioi 0) :=
    ((continuous_const.mul hεc).continuousOn.mul hFηc).add
      ((continuous_const.mul hεc).continuousOn.mul hFc')
  have hcac := caccioppoli Fη (fun x => 2 * Ip η η2 x) (fun x => 2 * ∫ t in (0:ℝ)..1, Qd A η (x, t))
    Gη g1 s hs2 hFηc hGηc hg1c (fun x hx => hFηd x (hIcc x hx).2.1)
    (fun x hx => hFη1d x (hIcc x hx).2.1) (fun x hx => (hlev x (hIcc x hx).1).1)
    (fun x _ => Ip_self_nonneg _ _)
    (fun x _ => show 0 ≤ 8 * ε x * Fη x + 2 * ε x * F x from
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hε0 x)) (Ip_self_nonneg η x))
        (mul_nonneg (mul_nonneg (by norm_num) (hε0 x)) (Ip_self_nonneg ζ x)))
    (fun x _ => Ip_self_nonneg _ _)
  -- mean value for level 2
  set g2 : ℝ → ℝ := fun x => 8 * ε x * Gη x + 4 * ε x * (F x + Fη x)
  have hg2c : ContinuousOn g2 (Ioi 0) :=
    ((continuous_const.mul hεc).continuousOn.mul hGηc).add
      ((continuous_const.mul hεc).continuousOn.mul (hFc'.add hFηc))
  have hsub1 : ∀ x ∈ Icc (s - 1) (s + 1), x ∈ Icc (s - 2) (s + 2) := fun x hx =>
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hmv := mean_value Gη (fun x => 2 * Ip η2 (pS η2) x)
    (fun x => 2 * ∫ t in (0:ℝ)..1, Qd A η2 (x, t)) g2 s (by linarith only [hs2]) hg2c
    (fun x hx => hGηd x (hIcc x (hsub1 x hx)).2.1)
    (fun x hx => hGη1d x (hIcc x (hsub1 x hx)).2.1)
    (fun x _ => show 0 ≤ 8 * ε x * Gη x + 4 * ε x * (F x + Fη x) from
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hε0 x)) (Ip_self_nonneg η2 x))
        (mul_nonneg (mul_nonneg (by norm_num) (hε0 x))
          (add_nonneg (Ip_self_nonneg ζ x) (Ip_self_nonneg η x))))
    (fun x hx => (hlev x (hIcc x (hsub1 x hx)).1).2)
    (fun x _ => Ip_self_nonneg _ _)
  -- integral bounds
  have i1 : ∫ x in (s - 2)..(s + 2), Fη x ≤ (s + 2 - (s - 2)) * (C' * (F s * E)) :=
    int_le_of_le (by linarith only) hFηc (by linarith only [hs2]) hFηx
  have i2 : ∫ x in (s - 2)..(s + 2), g1 x ≤ (s + 2 - (s - 2)) * ((4 * C' + 1) * (F s * E)) := by
    refine int_le_of_le (by linarith only) hg1c (by linarith only [hs2]) fun x hx => ?_
    have h1 := hεhalf x (hIcc x hx).1
    have h2 := hε0 x
    have h3 := hFηx x hx
    have h4 := hFx x hx
    have h5 := Ip_self_nonneg η x
    have h6 : 0 ≤ F x := Ip_self_nonneg ζ x
    simp only [g1]
    have k1 := mul_le_mul_of_nonneg_right h1 h5
    have k2 := mul_le_mul_of_nonneg_right h1 h6
    show 8 * ε x * Fη x + 2 * ε x * F x ≤ (4 * C' + 1) * (F s * E)
    linarith only [k1, k2, h3, h4]
  have i3 : ∫ x in (s - 1)..(s + 1), g2 x ≤ 4 * (∫ x in (s - 1)..(s + 1), Gη x) +
      (s + 1 - (s - 1)) * (2 * ((1 + C') * (F s * E))) := by
    have hi : IntervalIntegrable Gη volume (s - 1) (s + 1) :=
      (hGηc.mono fun x hx => (hIcc x (hsub1 x hx)).2.1).intervalIntegrable_of_Icc (by linarith only)
    have hi2 : IntervalIntegrable g2 volume (s - 1) (s + 1) :=
      (hg2c.mono fun x hx => (hIcc x (hsub1 x hx)).2.1).intervalIntegrable_of_Icc (by linarith only)
    have := intervalIntegral.integral_mono_on (f := g2)
      (g := fun x => 4 * Gη x + 2 * ((1 + C') * (F s * E))) (by linarith only : s - 1 ≤ s + 1) hi2
      ((hi.const_mul 4).add (intervalIntegrable_const (c := 2 * ((1 + C') * (F s * E)))))
      (fun x hx => by
        have hx' := hsub1 x hx
        have h1 := hεhalf x (hIcc x hx').1
        have h2 := hε0 x
        have h3 := hFηx x hx'
        have h4 := hFx x hx'
        have h5 := Ip_self_nonneg η x
        have h6 : 0 ≤ F x := Ip_self_nonneg ζ x
        have h7 : 0 ≤ Gη x := Ip_self_nonneg _ _
        simp only [g2]
        have k1 := mul_le_mul_of_nonneg_right h1 h7
        have k2 := mul_le_mul_of_nonneg_right h1 (add_nonneg h6 h5)
        show 8 * ε x * Gη x + 4 * ε x * (F x + Fη x) ≤ 4 * Gη x + 2 * ((1 + C') * (F s * E))
        linarith only [k1, k2, h3, h4])
    rw [intervalIntegral.integral_add (hi.const_mul 4) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at this
    simpa using this
  have hFsE : 0 ≤ F s * E := mul_nonneg hFs.le hE.le
  linarith only [hmv, i3, hcac, i1, i2]

end HDecay

end AF_w

section SP4

/-! Child 3 wrapper: `η` bounds from the exponential rate of `α`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma Ip_self_eq (u : ℝ × ℝ → Vec n) (s : ℝ) : Ip u u s = ∫ t in (0:ℝ)..1, ‖u (s, t)‖ ^ 2 := by
  simp only [Ip, real_inner_self_eq_norm_sq]

theorem eta_bounds (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (μ a Cr s₁ : ℝ) (ha : 0 < a) (hs₁ : 0 < s₁) (hF : ∀ s ≥ s₁, 0 < Fz ζ s)
    (hrate : ∀ s ≥ s₁, |αz ζ s - μ| ≤ Cr * Real.exp (-(a * s)) ∧
        ∀ T ≥ s, ∫ x in s..T, qz ζ x ≤ Cr * Real.exp (-(a * s))) :
    ∃ s₀ : ℝ, ∃ b > 0, ∃ K' : ℝ, ∀ s ≥ s₀,
      Ip (ηm ζ μ) (ηm ζ μ) s ≤ K' * Real.exp (-(b * s)) * Fz ζ s ∧
      Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) s ≤ K' * Fz ζ s := by
  set A : ℝ × ℝ → Op n := fun p => TL n (S p)
  have hA : Sm A := (contDiff_TL S hS).contDiffOn
  have hpA : TPer A := fun s t => by simp only [A, hSper s t]
  have hζs : Sm ζ := hζ.1
  have hres0 : ∀ x ∈ Ω, res A ζ x = 0 := by
    rintro ⟨a, b⟩ hx
    exact hζ.2.2 a hx.1 b
  obtain ⟨K, hK, sc, hsc, hco⟩ := coeff_exp S hS Sinf hSinf' d hSas
  set s1 := max s₁ sc
  have h1 : s₁ ≤ s1 := le_max_left _ _
  have hs10 : 0 < s1 := lt_max_of_lt_left hs₁
  have h : EtaHyp (αz ζ) (qz ζ) (Fz ζ) s1 K d := by
    refine ⟨hK, hd, hs10, fun s hs => ?_, fun s hs => ?_, fun s hs => hF s (h1.trans hs),
      fun s hs => ?_⟩
    · exact qz_nonneg hζs (lt_of_lt_of_le hs10 hs) (hF s (h1.trans hs))
    · have hs0 : 0 < s := lt_of_lt_of_le hs10 hs
      have hcF := (Fz_cont hζs).continuousAt (isOpen_Ioi.mem_nhds hs0)
      have hcG := (Gz_cont hζs).continuousAt (isOpen_Ioi.mem_nhds hs0)
      have hcD := (Dz_cont hζs).continuousAt (isOpen_Ioi.mem_nhds hs0)
      have hF0 := (hF s (h1.trans hs)).ne'
      exact ((hcG.div hcF hF0).sub ((hcD.div hcF hF0).pow 2)).continuousWithinAt
    · exact Fz_hasDerivAt' hζs (lt_of_lt_of_le hs10 hs) (hF s (h1.trans hs))
  have hco' : ∀ s ≥ s1, ∀ t, ‖A (s, t) - TL n (Sinf t)‖ ≤ K * Real.exp (-(d * s)) ∧
      ‖pS A (s, t)‖ ≤ K * Real.exp (-(d * s)) ∧ ‖pS (pS A) (s, t)‖ ≤ K * Real.exp (-(d * s)) :=
    fun s hs => hco s ((le_max_right _ _).trans hs)
  have hrate' : ∀ s ≥ s1, |αz ζ s - μ| ≤ Cr * Real.exp (-(a * s)) ∧
      ∀ T ≥ s, ∫ x in s..T, qz ζ x ≤ Cr * Real.exp (-(a * s)) := fun s hs => hrate s (h1.trans hs)
  obtain ⟨a', ha', C', s4, hC'⟩ := eta_decay Sinf hSinf hA hpA hζs hζ.2.1 hres0 h hco' μ a Cr s1 ha
    le_rfl hrate'
  obtain ⟨K3, -, s13, -, hco3⟩ := coeff_exp3 S hS Sinf hSinf' d hSas
  obtain ⟨C2, s5, hC2⟩ := eta2_bound Sinf hSinf hA hpA hζs hζ.2.1 hres0 h hco' hco3 μ a Cr s1 ha
    le_rfl hrate'
  refine ⟨max (max s4 s5) s1, a', ha', |C'| + |C2|, fun s hs => ⟨?_, ?_⟩⟩
  · have hFs := hF s (h1.trans ((le_max_right _ _).trans hs))
    refine (hC' s ((le_max_left _ _).trans ((le_max_left _ _).trans hs))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) hFs.le)
    linarith only [le_abs_self C', abs_nonneg C2]
  · have hFs := hF s (h1.trans ((le_max_right _ _).trans hs))
    refine (hC2 s ((le_max_right _ _).trans ((le_max_left _ _).trans hs))).trans
      (mul_le_mul_of_nonneg_right ?_ hFs.le)
    linarith only [le_abs_self C2, abs_nonneg C']

end HDecay

open HDecay in
theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (μ a K s₁ : ℝ) (ha : 0 < a) (hs₁ : 0 < s₁)
    (hF : ∀ s ≥ s₁, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)
    (hα : ∀ s ≥ s₁,
      |(∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫) / (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)
        - μ| ≤ K * Real.exp (-(a * s)))
    (hq : ∀ s ≥ s₁, ∀ T ≥ s, ∫ x in s..T,
        ((∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (x, t) (1, 0)‖ ^ 2) / (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2) -
          ((∫ t in (0:ℝ)..1, ⟪ζ (x, t), fderiv ℝ ζ (x, t) (1, 0)⟫) /
            (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2)) ^ 2) ≤ K * Real.exp (-(a * s))) :
    ∃ s₀ : ℝ, ∃ b > 0, ∃ K' : ℝ, ∀ s ≥ s₀,
      ∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (s, t) (1, 0) - μ • ζ (s, t)‖ ^ 2 ≤
        K' * Real.exp (-(b * s)) * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 ∧
      ∫ t in (0:ℝ)..1, ‖fderiv ℝ (fun p => fderiv ℝ ζ p (1, 0) - μ • ζ p) (s, t) (1, 0)‖ ^ 2 ≤
        K' * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
  obtain ⟨s₀, b, hb, K', h⟩ := eta_bounds S hS hSper Sinf hSinf hSinf' d hd hSas ζ hζ μ a K s₁ ha hs₁
    (fun s hs => by simp only [Fz, Ip_self_eq]; exact hF s hs)
    (fun s hs => by
      simp only [qz, αz, Dz, Gz, Fz, Ip_self_eq]
      exact ⟨hα s hs, hq s hs⟩)
  refine ⟨s₀, b, hb, K', fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := h s hs
  simp only [Fz, Ip_self_eq] at h1 h2
  exact ⟨h1, h2⟩

end SP4
