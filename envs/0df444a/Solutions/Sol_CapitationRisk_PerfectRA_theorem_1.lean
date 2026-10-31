-- Prove2me | solution 1 for CapitationRisk.PerfectRA.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:50:48.45318+00:00
-- url     : https://prove2.me/submissions/42d06bea-ba22-4158-ba8e-5717d621619e

import Mathlib
import Definitions.Def_CapitationRisk_PerfectRA_Model

open CapitationRisk.PerfectRA CapitationRisk.PerfectRA.Model

/-- A function differentiable at an interior-or-right-endpoint point `x` of `[a, b]` and
monotone on `[a, b]` has nonnegative derivative at `x`. -/
lemma capRisk_deriv_nonneg_of_monotoneOn {f : ℝ → ℝ} {a b x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hm : MonotoneOn f (Set.Icc a b)) (hax : a < x) (hxb : x ≤ b) : 0 ≤ deriv f x := by
  have hab : a < b := lt_of_lt_of_le hax hxb
  have hu : UniqueDiffWithinAt ℝ (Set.Icc a b) x := uniqueDiffOn_Icc hab x ⟨hax.le, hxb⟩
  rw [← hf.derivWithin hu]
  exact hm.derivWithin_nonneg

theorem solution {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [Nonempty I]
    (M : Model S I) (hM : M.Standing) (hb : M.BlackSwan) :
    ∃ wMA, M.IsMAEquilibrium M.rate wMA ∧
      (∀ w, M.IsMAEquilibrium M.rate w → w = wMA) ∧ wMA ≠ M.wstar := by
  classical
  have hlamS_d : ∀ s i, Differentiable ℝ (M.lamS s i) := fun s i =>
    (hM.lamS_smooth s i).differentiable (by norm_num)
  have hlam_d : ∀ i, Differentiable ℝ (M.lam i) := fun i =>
    (hM.lam_smooth i).differentiable (by norm_num)
  have hCf_d : ∀ s, Differentiable ℝ (M.Cf s) := fun s =>
    (hM.Cf_smooth s).differentiable (by norm_num)
  have hbox : ∀ w : S → ℝ, w ∈ M.box ↔ ∀ s, w s ∈ Set.Icc (M.wl s) 1 := by
    intro w
    show w ∈ Set.pi Set.univ _ ↔ _
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
  have hws : ∀ s, M.wstar s ∈ Set.Icc (M.wl s) 1 := fun s =>
    ⟨(hM.wstar_mem s).1.le, (hM.wstar_mem s).2⟩
  have hwstar_box : M.wstar ∈ M.box := (hbox _).2 hws
  have hconv_box : Convex ℝ M.box := convex_pi (fun s _ => convex_Icc _ _)
  -- derivative signs at the target
  have hdCf : ∀ s, 0 ≤ deriv (M.Cf s) (M.wstar s) := fun s =>
    capRisk_deriv_nonneg_of_monotoneOn (hCf_d s _) (hM.Cf_mono s) (hM.wstar_mem s).1
      (hM.wstar_mem s).2
  have hdl : ∀ s i, 0 ≤ deriv (M.lamS s i) (M.wstar s) := fun s i =>
    capRisk_deriv_nonneg_of_monotoneOn (hlamS_d s i _) (hM.lamS_mono s i) (hM.wstar_mem s).1
      (hM.wstar_mem s).2
  have hPeq : ∀ s, M.dDemand s (M.wstar s) * M.Pstar s =
      M.dDemand s (M.wstar s) * M.c s + deriv (M.Cf s) (M.wstar s) := by
    intro s
    unfold Model.Pstar Model.TMPrice
    rw [← mul_assoc, mul_inv_cancel₀ (hM.dDemand_wstar_pos s).ne', one_mul]
  have hP : ∀ s, 0 ≤ M.Pstar s := by
    intro s
    have h1 := hPeq s
    have h2 := hM.dDemand_wstar_pos s
    have h3 := hM.c_nonneg s
    have h4 := hdCf s
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos h2 (neg_pos.2 hneg), mul_nonneg h2.le h3]
  have hr : ∀ i, 0 ≤ M.rate i := by
    intro i
    unfold Model.rate
    apply Finset.sum_nonneg
    intro s _
    exact mul_nonneg (div_nonneg (hM.lamS_nonneg s i _ (hws s)) (hM.lam_wstar_pos i).le) (hP s)
  -- strict concavity of the profit on the box
  have hconc : ∀ t : Finset I,
      ConcaveOn ℝ M.box (fun w => ∑ i ∈ t, M.rate i * M.lam i w) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using concaveOn_const (0 : ℝ) hconv_box
    | insert j t hj ih =>
      simp only [Finset.sum_insert hj]
      exact ((hM.lam_concave j).smul (hr j)).add ih
  have hstrict : StrictConvexOn ℝ M.box
      (fun w => ∑ s, (M.Cf s (w s) + M.c s * M.totDemand s (w s))) := by
    refine ⟨hconv_box, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    obtain ⟨s0, hs0⟩ : ∃ s0, x s0 ≠ y s0 := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    have hx' := (hbox x).1 hx
    have hy' := (hbox y).1 hy
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro s _
      have := (hM.totalCost_strictConvex s).convexOn.2 (hx' s) (hy' s) ha.le hb.le hab
      simpa [smul_eq_mul] using this
    · refine ⟨s0, Finset.mem_univ _, ?_⟩
      have := (hM.totalCost_strictConvex s0).2 (hx' s0) (hy' s0) hs0 ha hb hab
      simpa [smul_eq_mul] using this
  have hprofit_eq : M.profit M.rate = (fun w => ∑ i, M.rate i * M.lam i w) -
      (fun w => ∑ s, (M.Cf s (w s) + M.c s * M.totDemand s (w s))) := by
    funext w
    simp only [Model.profit, Pi.sub_apply, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (M.lam i w) (M.rate i))]
    ring
  have hsc : StrictConcaveOn ℝ M.box (M.profit M.rate) := by
    rw [hprofit_eq]
    exact (hconc Finset.univ).sub_strictConvexOn hstrict
  -- existence
  have hpc : Continuous (M.profit M.rate) := by
    unfold Model.profit Model.totDemand
    refine ((continuous_finsetSum _ fun i _ => ((hlam_d i).continuous.mul continuous_const)).sub
      (continuous_finsetSum _ fun s _ => (hCf_d s).continuous.comp (continuous_apply s))).sub
      (continuous_finsetSum _ fun s _ => continuous_const.mul
        (continuous_finsetSum _ fun i _ => (hlamS_d s i).continuous.comp (continuous_apply s)))
  have hcompact : IsCompact M.box := isCompact_univ_pi (fun s => isCompact_Icc)
  obtain ⟨w0, hw0, hmax⟩ := hcompact.exists_isMaxOn ⟨M.wstar, hwstar_box⟩ hpc.continuousOn
  refine ⟨w0, ⟨hw0, hmax⟩, fun w hw => hsc.eq_of_isMaxOn hw.2 hmax hw.1 hw0, ?_⟩
  -- the targeted quality is not the equilibrium
  rintro rfl
  obtain ⟨s, hs⟩ := hb
  obtain ⟨e, he⟩ : ∃ e : S → ℝ, e = Pi.single s 1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = M.wstar s - M.wl s := ⟨_, rfl⟩
  have hδpos : 0 < δ := by have := (hM.wstar_mem s).1; simp only [hδ]; linarith
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => M.profit M.rate (M.wstar + t • e) := ⟨_, rfl⟩
  -- derivative of g at 0
  obtain ⟨a, ha⟩ : ∃ a : I → ℝ, a = fun i => fderiv ℝ (M.lam i) M.wstar e := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑ i, a i * M.rate i - deriv (M.Cf s) (M.wstar s) -
      M.c s * M.dDemand s (M.wstar s) := ⟨_, rfl⟩
  have hγ : HasDerivAt (fun t : ℝ => M.wstar + t • e) e (0:ℝ) := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const e).const_add M.wstar
    simpa using this
  have hcoord : ∀ s', HasDerivAt (fun t : ℝ => M.wstar s' + t * e s') (e s') (0:ℝ) := by
    intro s'
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (e s')).const_add (M.wstar s')
  have hgD : HasDerivAt g D (0:ℝ) := by
    have hg' : g = fun t : ℝ => ∑ i, M.lam i (M.wstar + t • e) * M.rate i
        - ∑ s', M.Cf s' (M.wstar s' + t * e s')
        - ∑ s', M.c s' * ∑ i, M.lamS s' i (M.wstar s' + t * e s') := by
      funext t
      simp only [hg, Model.profit, Model.totDemand, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hg']
    have h1 : HasDerivAt (fun t : ℝ => ∑ i, M.lam i (M.wstar + t • e) * M.rate i)
        (∑ i, a i * M.rate i) (0:ℝ) := by
      apply HasDerivAt.fun_sum
      intro i _
      apply HasDerivAt.mul_const
      rw [ha]
      exact (hlam_d i M.wstar).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
    have h2 : HasDerivAt (fun t : ℝ => ∑ s', M.Cf s' (M.wstar s' + t * e s'))
        (∑ s', deriv (M.Cf s') (M.wstar s') * e s') (0:ℝ) := by
      apply HasDerivAt.fun_sum
      intro s' _
      exact (hCf_d s' (M.wstar s')).hasDerivAt.comp_of_eq 0 (hcoord s') (by simp)
    have h3 : HasDerivAt (fun t : ℝ => ∑ s', M.c s' * ∑ i, M.lamS s' i (M.wstar s' + t * e s'))
        (∑ s', M.c s' * ∑ i, deriv (M.lamS s' i) (M.wstar s') * e s') (0:ℝ) := by
      apply HasDerivAt.fun_sum
      intro s' _
      apply HasDerivAt.const_mul
      apply HasDerivAt.fun_sum
      intro i _
      exact (hlamS_d s' i (M.wstar s')).hasDerivAt.comp_of_eq 0 (hcoord s') (by simp)
    have hDv : D = ∑ i, a i * M.rate i - ∑ s', deriv (M.Cf s') (M.wstar s') * e s' -
        ∑ s', M.c s' * ∑ i, deriv (M.lamS s' i) (M.wstar s') * e s' := by
      simp [hD, he, Model.dDemand, Pi.single_apply]
    rw [hDv]
    exact (h1.sub h2).sub h3
  -- D < 0
  have hDneg : D < 0 := by
    set m : ℝ := Finset.univ.sup' Finset.univ_nonempty M.rate with hm
    have hrm : ∀ i, M.rate i ≤ m := fun i => Finset.le_sup' M.rate (Finset.mem_univ i)
    have hmP : m < M.Pstar s := (Finset.sup'_lt_iff _).2 (fun i _ => hs i)
    have hai : ∀ i, a i ≤ deriv (M.lamS s i) (M.wstar s) := by
      intro i
      have := hM.option_demand M.wstar hwstar_box i s
      simpa [ha, he] using this
    have hstep1 : ∑ i, a i * M.rate i ≤ ∑ i, deriv (M.lamS s i) (M.wstar s) * m := by
      apply Finset.sum_le_sum
      intro i _
      calc a i * M.rate i ≤ deriv (M.lamS s i) (M.wstar s) * M.rate i :=
            mul_le_mul_of_nonneg_right (hai i) (hr i)
        _ ≤ deriv (M.lamS s i) (M.wstar s) * m := mul_le_mul_of_nonneg_left (hrm i) (hdl s i)
    have hsumeq : ∑ i, deriv (M.lamS s i) (M.wstar s) * m = M.dDemand s (M.wstar s) * m := by
      rw [← Finset.sum_mul]; rfl
    have hpos := hM.dDemand_wstar_pos s
    have hPe := hPeq s
    have : M.dDemand s (M.wstar s) * m < M.dDemand s (M.wstar s) * M.Pstar s :=
      mul_lt_mul_of_pos_left hmP hpos
    simp only [hD]
    linarith
  -- g attains its max on [-δ, 0] at 0
  have hgmax : IsMaxOn g (Set.Icc (-δ) 0) 0 := by
    intro t ht
    show g t ≤ g 0
    have hmem : M.wstar + t • e ∈ M.box := by
      rw [hbox]
      intro s'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he, Pi.single_apply]
      split_ifs with h
      · subst h
        have := hws s'
        constructor <;> simp only [hδ] at ht <;> nlinarith [ht.1, ht.2, this.1, this.2]
      · simpa using hws s'
    have := hmax hmem
    simpa [hg] using this
  have hy : (-δ) ∈ posTangentConeAt (Set.Icc (-δ) 0) (0:ℝ) := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_symm, segment_eq_Icc (by linarith)]
  have hnp := hgmax.localize.hasFDerivWithinAt_nonpos hgD.hasFDerivAt.hasFDerivWithinAt hy
  simp at hnp
  nlinarith [mul_pos hδpos (neg_pos.2 hDneg)]
