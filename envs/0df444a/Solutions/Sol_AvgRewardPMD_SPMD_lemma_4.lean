-- Prove2me | solution 1 for AvgRewardPMD.SPMD.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:41:48.164204+00:00
-- url     : https://prove2.me/submissions/20ff775f-4579-412e-91dc-77c45b47659d

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Theorems.Thm_AvgRewardPMD_SPMD_three_point
import Theorems.Thm_AvgRewardPMD_SPMD_lemma_2
import Theorems.Thm_AvgRewardPMD_SPMD_kl_uniform_le_log

open FoundationsML.ReinforcementLearning MeasureTheory AvgRewardPMD.SPMD Filter Topology

set_option linter.unusedSectionVars false

namespace SPMDLemma4Aux


lemma mul_log_div (z q : ℝ) (hq : q ≠ 0) : z * Real.log (z / q) = z * Real.log z - z * Real.log q := by
  rcases eq_or_ne z 0 with h | h
  · simp [h]
  · rw [Real.log_div h hq]; ring

lemma kl_eq {A : Type*} [Fintype A] (p q : A → ℝ) (hq : ∀ a, 0 < q a) :
    kl p q = ∑ a, p a * Real.log (p a) - ∑ a, p a * Real.log (q a) := by
  unfold kl
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => mul_log_div _ _ (hq a).ne'

lemma psi_convex (qa x y t : ℝ) (hq : 0 < qa) (hx : 0 ≤ x) (hy : 0 ≤ y) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ((1-t)*x + t*y) * Real.log (((1-t)*x + t*y)/qa)
      ≤ (1-t) * (x * Real.log (x/qa)) + t * (y * Real.log (y/qa)) := by
  rw [mul_log_div _ _ hq.ne', mul_log_div _ _ hq.ne', mul_log_div _ _ hq.ne']
  have h := (Real.convexOn_mul_log).2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy)
    (show 0 ≤ 1 - t by linarith) ht0 (by ring)
  simp only [smul_eq_mul] at h
  nlinarith [h]

lemma kl_nonneg'' {A : Type*} [Fintype A] (p r : A → ℝ) (hp : p ∈ stdSimplex ℝ A)
    (hr : ∀ a, 0 < r a) (hrs : ∑ a, r a = 1) : 0 ≤ kl p r := by
  have key : ∀ a, p a - r a ≤ p a * Real.log (p a / r a) := by
    intro a
    rcases (hp.1 a).eq_or_lt with h0 | hx
    · rw [← h0]; simp; linarith [hr a]
    · have ht : 0 < p a / r a := div_pos hx (hr a)
      have h := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
      rw [Real.log_inv] at h
      have hy' : r a ≠ 0 := (hr a).ne'
      have hx' : p a ≠ 0 := hx.ne'
      calc p a - r a = p a * (1 - (p a / r a)⁻¹) := by field_simp
        _ ≤ p a * Real.log (p a / r a) := mul_le_mul_of_nonneg_left (by linarith) hx.le
  unfold kl
  have : ∑ a, (p a - r a) ≤ ∑ a, p a * Real.log (p a / r a) :=
    Finset.sum_le_sum fun a _ => key a
  rw [Finset.sum_sub_distrib, hp.2, hrs] at this
  linarith

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- the minimizer of the KL prox step is strictly positive -/
lemma qplus_pos (H : (A → ℝ) → ℝ) (ω lam : ℝ)
    (hH : IsKLStrongConvexOn H ω) (hlam : 0 ≤ lam) (Q q qplus : A → ℝ)
    (hq : q ∈ stdSimplex ℝ A) (hqpos : ∀ a, 0 < q a) (hqplus : qplus ∈ stdSimplex ℝ A)
    (hmin : ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * qplus a + H qplus) + kl qplus q ≤ lam * (∑ a, Q a * p a + H p) + kl p q) :
    ∀ a, 0 < qplus a := by
  intro a0
  rcases (hqplus.1 a0).eq_or_lt with h0 | h
  swap; · exact h
  exfalso
  set ψ : A → ℝ → ℝ := fun a x => x * Real.log (x / q a) with hψ
  set C2 := ∑ a ∈ Finset.univ.erase a0, (ψ a (q a) - ψ a (qplus a)) with hC2
  set C := lam * ∑ a, Q a * (q a - qplus a) + lam * (H q - H qplus) + C2 with hC
  have hq0 := hqpos a0
  have bound : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ C + q a0 * Real.log t := by
    intro t ht0 ht1
    set pt : A → ℝ := (1 - t) • qplus + t • q with hpt
    have hpta : ∀ a, pt a = (1 - t) * qplus a + t * q a := fun a => by
      simp [pt, smul_eq_mul]
    have hptS : pt ∈ stdSimplex ℝ A :=
      (convex_stdSimplex ℝ A) hqplus hq (by linarith) ht0.le (by ring)
    have hHc := hH.2.1.2 hqplus hq (show 0 ≤ 1 - t by linarith) ht0.le (by ring)
    simp only [smul_eq_mul] at hHc
    rw [← hpt] at hHc
    have hm := hmin pt hptS
    -- linear part
    have hlin : ∑ a, Q a * pt a = ∑ a, Q a * qplus a + t * ∑ a, Q a * (q a - qplus a) := by
      simp_rw [hpta, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    -- kl part
    have hkl : kl pt q - kl qplus q ≤ t * C2 + t * q a0 * Real.log t := by
      unfold kl
      rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
      have e0 : pt a0 * Real.log (pt a0 / q a0) - qplus a0 * Real.log (qplus a0 / q a0)
          = t * q a0 * Real.log t := by
        rw [hpta, ← h0]
        simp only [mul_zero, zero_add, zero_mul, zero_div, Real.log_zero, sub_zero]
        rw [mul_div_assoc, div_self hq0.ne', mul_one]
      rw [e0, hC2, Finset.mul_sum]
      have : ∑ x ∈ Finset.univ.erase a0, (pt x * Real.log (pt x / q x) - qplus x * Real.log (qplus x / q x))
          ≤ ∑ x ∈ Finset.univ.erase a0, t * (ψ x (q x) - ψ x (qplus x)) := by
        apply Finset.sum_le_sum; intro a _
        simp only [ψ]
        rw [hpta]
        have := psi_convex (q a) (qplus a) (q a) t (hqpos a) (hqplus.1 a) (hq.1 a) ht0.le ht1
        linarith
      linarith
    have hHt := mul_le_mul_of_nonneg_left hHc hlam
    rw [hlin] at hm
    have : 0 ≤ t * (C + q a0 * Real.log t) := by
      simp only [hC]
      nlinarith
    exact (mul_nonneg_iff_of_pos_left ht0).1 this
  set t := Real.exp (-(|C| + 1) / q a0)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by
    apply Real.exp_le_one_iff.2
    apply div_nonpos_of_nonpos_of_nonneg _ hq0.le
    linarith [abs_nonneg C]
  have := bound t ht0 ht1
  rw [Real.log_exp, mul_div_cancel₀ _ hq0.ne'] at this
  linarith [le_abs_self C]


/-! Pinsker's inequality on a finite alphabet (Cauchy–Schwarz proof; the argument follows the
platform proof of `NeuroSymbolicRLHF.klDivFin_pinsker`). -/

noncomputable def pH (x : ℝ) : ℝ := x * Real.log x - 5/2 * x + 7 - 27/2 * (x+2)⁻¹
noncomputable def pG (x : ℝ) : ℝ := Real.log x + 1 - 5/2 + 27/2 * ((x+2)^2)⁻¹

lemma hasDerivAt_pH {x : ℝ} (hx : 0 < x) : HasDerivAt pH (pG x) x := by
  have h2 : x + 2 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log x + 1) x :=
    Real.hasDerivAt_mul_log hx.ne'
  have hid : HasDerivAt (fun y : ℝ => (5/2 : ℝ) * y) (5/2) x := by
    simpa using (hasDerivAt_id x).const_mul (5/2 : ℝ)
  have h4 : HasDerivAt (fun y : ℝ => (y+2)⁻¹) (-(1)/(x+2)^2) x :=
    ((hasDerivAt_id x).add_const 2).inv h2
  have h6 : HasDerivAt (fun y : ℝ => (27/2 : ℝ) * (y+2)⁻¹) ((27/2) * (-(1)/(x+2)^2)) x :=
    h4.const_mul (27/2 : ℝ)
  have h5 : HasDerivAt pH (Real.log x + 1 - 5/2 + 7 * 0 - (27/2) * (-(1)/(x+2)^2)) x := by
    have := ((h1.sub hid).add_const 7).sub h6
    have h5' := this.congr_of_eventuallyEq (f₁ := pH)
      (Filter.Eventually.of_forall fun y => by simp [pH])
    exact h5'.congr_deriv (by ring)
  convert h5 using 1
  unfold pG
  field_simp
  ring

lemma hasDerivAt_pG {x : ℝ} (hx : 0 < x) : HasDerivAt pG (1/x - 27/(x+2)^3) x := by
  have h2 : x + 2 ≠ 0 := by linarith
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h3 : HasDerivAt (fun y : ℝ => (y+2)^2) (2*(x+2)) x := by
    have := ((hasDerivAt_id x).add_const 2).pow 2
    have h5' := this.congr_of_eventuallyEq (f₁ := fun y : ℝ => (y+2)^2)
      (Filter.Eventually.of_forall fun y => by simp)
    exact h5'.congr_deriv (by simp)
  have h4 : HasDerivAt (fun y : ℝ => ((y+2)^2)⁻¹) (-(2*(x+2))/((x+2)^2)^2) x :=
    h3.inv (by positivity)
  have h6 : HasDerivAt (fun y : ℝ => (27/2 : ℝ) * ((y+2)^2)⁻¹)
      ((27/2) * (-(2*(x+2))/((x+2)^2)^2)) x := h4.const_mul (27/2 : ℝ)
  have h5 : HasDerivAt pG (x⁻¹ + 0 - 0 + (27/2) * (-(2*(x+2))/((x+2)^2)^2)) x := by
    have := ((h1.add_const 1).sub_const (5/2 : ℝ)).add h6
    have h5' := this.congr_of_eventuallyEq (f₁ := pG)
      (Filter.Eventually.of_forall fun y => by simp [pG])
    exact h5'.congr_deriv (by ring)
  convert h5 using 1
  field_simp
  ring

lemma pG_one : pG 1 = 0 := by unfold pG; norm_num
lemma pH_one : pH 1 = 0 := by unfold pH; norm_num

lemma pG_deriv_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ 1/x - 27/(x+2)^3 := by
  have h2 : (0:ℝ) < x + 2 := by linarith
  have hkey : 27 * x ≤ (x+2)^3 := by nlinarith [sq_nonneg (x - 1), hx.le]
  rw [sub_nonneg, div_le_div_iff₀ (by positivity : (0:ℝ) < (x+2)^3) hx]
  nlinarith [hkey]

lemma pG_monotone : MonotoneOn pG (Set.Ioi (0:ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro x hx
    exact ((hasDerivAt_pG (Set.mem_Ioi.1 hx)).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact ((hasDerivAt_pG (Set.mem_Ioi.1 hx)).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := Set.mem_Ioi.1 hx
    rw [(hasDerivAt_pG hx0).deriv]
    exact pG_deriv_nonneg hx0

lemma pH_nonneg_of_pos {x : ℝ} (hx : 0 < x) : 0 ≤ pH x := by
  rcases le_total 1 x with h1 | h1
  · have hmono : MonotoneOn pH (Set.Ici (1:ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
      · intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le one_pos (Set.mem_Ici.1 hy)
        exact ((hasDerivAt_pH hy0).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy0 : 0 < y := lt_trans one_pos (Set.mem_Ioi.1 hy)
        exact ((hasDerivAt_pH hy0).differentiableAt).differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy1 : (1:ℝ) < y := Set.mem_Ioi.1 hy
        have hy0 : 0 < y := lt_trans one_pos hy1
        rw [(hasDerivAt_pH hy0).deriv]
        have := pG_monotone (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 hy0) hy1.le
        rw [pG_one] at this
        exact this
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h1) h1
    rwa [pH_one] at this
  · have hanti : AntitoneOn pH (Set.Ioc (0:ℝ) 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) ?_ ?_ ?_
      · intro y hy
        exact ((hasDerivAt_pH (Set.mem_Ioc.1 hy).1).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        exact ((hasDerivAt_pH (Set.mem_Ioo.1 hy).1).differentiableAt).differentiableWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        obtain ⟨hy0, hy1⟩ := Set.mem_Ioo.1 hy
        rw [(hasDerivAt_pH hy0).deriv]
        have := pG_monotone (Set.mem_Ioi.2 hy0) (Set.mem_Ioi.2 one_pos) hy1.le
        rw [pG_one] at this
        exact this
    have := hanti (Set.mem_Ioc.2 ⟨hx, h1⟩) (Set.mem_Ioc.2 ⟨one_pos, le_rfl⟩) h1
    rwa [pH_one] at this

lemma xlogx_sub_ge {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1)^2 / (2 * (x + 2)) ≤ x * Real.log x - x + 1 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; norm_num
  · have hH := pH_nonneg_of_pos h
    have h2 : x + 2 ≠ 0 := by linarith
    have hrw : x * Real.log x - x + 1 - 3 * (x - 1)^2 / (2 * (x + 2)) = pH x := by
      unfold pH
      field_simp
      ring
    linarith [hrw ▸ hH]

lemma kl_term_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    3 * (a - b)^2 / (2 * (a + 2*b)) ≤ a * Real.log (a / b) - a + b := by
  have hx := xlogx_sub_ge (x := a / b) (div_nonneg ha hb.le)
  have hmul := mul_le_mul_of_nonneg_left hx hb.le
  have hlhs : b * (3 * (a/b - 1)^2 / (2 * (a/b + 2))) = 3 * (a - b)^2 / (2 * (a + 2*b)) := by
    have hden : a + 2*b ≠ 0 := by positivity
    field_simp
  have hrhs : b * ((a/b) * Real.log (a/b) - a/b + 1) = a * Real.log (a/b) - a + b := by
    field_simp
  rw [hlhs, hrhs] at hmul
  exact hmul

lemma pinsker {ι : Type*} [Fintype ι] (p q : ι → ℝ) (hp : p ∈ stdSimplex ℝ ι)
    (hq : ∀ i, 0 < q i) (hqs : ∑ i, q i = 1) :
    (∑ i, |p i - q i|)^2 ≤ 2 * kl p q := by
  set w : ι → ℝ := fun i => p i + 2 * q i with hw
  have hwpos : ∀ i, 0 < w i := by
    intro i
    have := hp.1 i
    have := hq i
    simp only [hw]
    linarith
  have hwsum : ∑ i, w i = 3 := by
    simp only [hw]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hqs]
    norm_num
  have hterm : ∀ i : ι, 3 * (p i - q i)^2 / (2 * w i)
      ≤ p i * Real.log (p i / q i) - p i + q i := fun i => kl_term_ge (hp.1 i) (hq i)
  have hsum : ∑ i, 3 * (p i - q i)^2 / (2 * w i) ≤ kl p q := by
    have h1 : ∑ i, (p i * Real.log (p i / q i) - p i + q i) = kl p q := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp.2, hqs]
      simp [kl]
    calc ∑ i, 3 * (p i - q i)^2 / (2 * w i)
        ≤ ∑ i, (p i * Real.log (p i / q i) - p i + q i) := Finset.sum_le_sum fun i _ => hterm i
      _ = kl p q := h1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => |p i - q i| / Real.sqrt (w i)) (fun i => Real.sqrt (w i))
  have hprod : ∀ i : ι, (|p i - q i| / Real.sqrt (w i)) * Real.sqrt (w i) = |p i - q i| := by
    intro i
    have : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hwpos i))
    field_simp
  have hsq1 : ∀ i : ι, (|p i - q i| / Real.sqrt (w i))^2 = (p i - q i)^2 / w i := by
    intro i
    rw [div_pow, Real.sq_sqrt (hwpos i).le, sq_abs]
  have hsq2 : ∀ i : ι, (Real.sqrt (w i))^2 = w i := fun i => Real.sq_sqrt (hwpos i).le
  rw [Finset.sum_congr rfl (fun i _ => hprod i), Finset.sum_congr rfl (fun i _ => hsq1 i),
    Finset.sum_congr rfl (fun i _ => hsq2 i), hwsum] at hcs
  have hfrac : ∑ i, (p i - q i)^2 / w i ≤ (2/3) * kl p q := by
    have h3 : ∑ i, 3 * (p i - q i)^2 / (2 * w i) = (3/2) * ∑ i, (p i - q i)^2 / w i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [h3] at hsum
    linarith
  nlinarith [hcs, hfrac, kl_nonneg'' p q hp hq hqs]

/-- `⟨u, d⟩ ≤ (hi - lo)/2 · ‖d‖₁` when `∑ d = 0` and `lo ≤ u ≤ hi`. -/
lemma inner_le {ι : Type*} [Fintype ι] (u d : ι → ℝ) (lo hi : ℝ)
    (hu : ∀ i, lo ≤ u i ∧ u i ≤ hi) (hd : ∑ i, d i = 0) :
    ∑ i, u i * d i ≤ (hi - lo) / 2 * ∑ i, |d i| := by
  have e : ∑ i, u i * d i = ∑ i, (u i - (hi + lo) / 2) * d i := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hd, mul_zero, sub_zero]
  rw [e, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have h1 : |u i - (hi + lo) / 2| ≤ (hi - lo) / 2 := by
    rw [abs_le]; constructor <;> linarith [(hu i).1, (hu i).2]
  calc (u i - (hi + lo) / 2) * d i ≤ |(u i - (hi + lo) / 2) * d i| := le_abs_self _
    _ = |u i - (hi + lo) / 2| * |d i| := abs_mul _ _
    _ ≤ (hi - lo) / 2 * |d i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

lemma bounds_span {ι : Type*} [Fintype ι] (u : ι → ℝ) (i : ι) :
    (⨅ j, u j) ≤ u i ∧ u i ≤ ⨆ j, u j :=
  ⟨ciInf_le (Set.finite_range u).bddBelow i, le_ciSup (Set.finite_range u).bddAbove i⟩

lemma span_nonneg' {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ) : 0 ≤ span u := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := bounds_span u i
  simp only [span]; linarith [this.1, this.2]

lemma sum_abs_sub_le_two {ι : Type*} [Fintype ι] (p q : ι → ℝ) (hp : p ∈ stdSimplex ℝ ι)
    (hq : q ∈ stdSimplex ℝ ι) : ∑ i, |p i - q i| ≤ 2 := by
  calc ∑ i, |p i - q i| ≤ ∑ i, (p i + q i) := Finset.sum_le_sum fun i _ => by
        rw [abs_le]; constructor <;> linarith [hp.1 i, hq.1 i]
    _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num


end SPMDLemma4Aux

open SPMDLemma4Aux in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ) (ω L : ℝ)
    (hconv : IsKLStrongConvex h ω) (hLip : IsL1Lipschitz h L)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (νstar : S → ℝ)
    (hνstar : MarkovMixing.IsStationary (stateMatrix P πstar) νstar)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (lam : ℕ → ℝ) (k : ℕ) (hlam : ∀ j ≤ k, 0 ≤ lam j) (bias κ : ℝ)
    (hiter : IsSPMDIterates h lam Qhat π)
    (hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
      Qhat π bias κ (k + 1))
    (s₀ : S) :
    ∫ ξ, (lam k * (avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)
          + (1 + lam k * ω) * stationaryKL νstar (π (k + 1) ξ) πstar) ∂μ
      ≤ ∫ ξ, stationaryKL νstar (π k ξ) πstar ∂μ + lam k * bias
          + lam k ^ 2 * (κ ^ 2 / 4 + L ^ 2) := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcrit
  have hνS : νstar ∈ stdSimplex ℝ S := ⟨hνstar.1.1, hνstar.1.2⟩
  have hω : 0 ≤ ω := (hconv s₀).1
  have hAne : (Finset.univ : Finset A).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (s := Finset.univ) (f := πstar s₀)
      (by rw [(hπstar s₀).2]; norm_num)
  obtain ⟨a₀, -⟩ := hAne
  haveI : Nonempty (S × A) := ⟨(s₀, a₀)⟩
  have hlk0 : 0 ≤ lam k := hlam k le_rfl
  have hπS : ∀ s, πstar s ∈ stdSimplex ℝ A := fun s => ⟨(hπstar s).1, (hπstar s).2⟩
  -- the iterates are strictly positive policies up to time k+1
  have hpol : ∀ j ≤ k + 1, ∀ ξ, (∀ s, π j ξ s ∈ stdSimplex ℝ A) ∧ ∀ s a, 0 < π j ξ s a := by
    intro j
    induction j with
    | zero =>
      intro _ ξ
      have h0 := (hiter ξ).1
      have hcardpos : (0 : ℝ) < Fintype.card A := by
        exact_mod_cast Fintype.card_pos_iff.2 ⟨a₀⟩
      refine ⟨fun s => ⟨fun a => by rw [h0]; positivity, ?_⟩, fun s a => by rw [h0]; positivity⟩
      simp_rw [h0]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    | succ j ih =>
      intro hj ξ
      have ih' := ih (by omega) ξ
      have hk := fun s => (hiter ξ).2 j s
      refine ⟨fun s => (hk s).1, fun s a => ?_⟩
      exact qplus_pos (h s) ω (lam j) (hconv s) (hlam j (by omega)) (fun a => Qhat j ξ (s, a))
        (π j ξ s) (π (j+1) ξ s) (ih'.1 s) (ih'.2 s) (hk s).1 (hk s).2 a
  have hklnn : ∀ j ≤ k + 1, ∀ ξ s (p : A → ℝ), p ∈ stdSimplex ℝ A → 0 ≤ kl p (π j ξ s) :=
    fun j hj ξ s p hp => kl_nonneg'' _ _ hp ((hpol j hj ξ).2 s) ((hpol j hj ξ).1 s).2
  -- the three-point inequality at every state
  have hTP : ∀ j ≤ k, ∀ ξ s, lam j * (∑ a, Qhat j ξ (s, a) * (π (j+1) ξ s a - πstar s a)
      + h s (π (j+1) ξ s) - h s (πstar s)) + kl (π (j+1) ξ s) (π j ξ s)
      ≤ kl (πstar s) (π j ξ s) - (1 + lam j * ω) * kl (πstar s) (π (j+1) ξ s) := by
    intro j hj ξ s
    have hpj := hpol j (by omega) ξ
    have hk := (hiter ξ).2 j s
    exact three_point (h s) ω (lam j) (hconv s) (hlam j hj) (fun a => Qhat j ξ (s, a))
      (π j ξ s) (π (j+1) ξ s) (hpj.1 s) (hpj.2 s) hk.1 hk.2 (πstar s) (hπS s)
  set M : ℕ → Ω → ℝ := fun j ξ => ∑ x, |Qhat j ξ x| with hM
  have hMnn : ∀ j ξ, 0 ≤ M j ξ := fun j ξ => Finset.sum_nonneg fun x _ => abs_nonneg _
  have hQM : ∀ j ξ x, |Qhat j ξ x| ≤ M j ξ := fun j ξ x =>
    Finset.single_le_sum (f := fun y => |Qhat j ξ y|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)
  set D : ℕ → Ω → ℝ := fun j ξ => stationaryKL νstar (π j ξ) πstar with hD
  have hDnn : ∀ j ≤ k + 1, ∀ ξ, 0 ≤ D j ξ := fun j hj ξ =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hνstar.1.1 s) (hklnn j hj ξ s _ (hπS s))
  have hDstep : ∀ j ≤ k, ∀ ξ, D (j+1) ξ ≤ D j ξ + lam j * (2 * M j ξ + 2 * |L|) := by
    intro j hj ξ
    have key : ∀ s, kl (πstar s) (π (j+1) ξ s)
        ≤ kl (πstar s) (π j ξ s) + lam j * (2 * M j ξ + 2 * |L|) := by
      intro s
      have t := hTP j hj ξ s
      have hq1 := (hpol (j+1) (by omega) ξ).1 s
      have hkl1 := hklnn (j+1) (by omega) ξ s _ (hπS s)
      have hklq := hklnn j (by omega) ξ s _ hq1
      have hlj := hlam j hj
      have habs : |∑ a, Qhat j ξ (s, a) * (π (j+1) ξ s a - πstar s a)| ≤ 2 * M j ξ := by
        calc |∑ a, Qhat j ξ (s, a) * (π (j+1) ξ s a - πstar s a)|
            ≤ ∑ a, |Qhat j ξ (s, a) * (π (j+1) ξ s a - πstar s a)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a, |Qhat j ξ (s, a)| * |π (j+1) ξ s a - πstar s a| := by simp_rw [abs_mul]
          _ ≤ ∑ a, M j ξ * |π (j+1) ξ s a - πstar s a| := Finset.sum_le_sum fun a _ =>
              mul_le_mul_of_nonneg_right (hQM j ξ (s, a)) (abs_nonneg _)
          _ = M j ξ * ∑ a, |π (j+1) ξ s a - πstar s a| := by rw [Finset.mul_sum]
          _ ≤ M j ξ * 2 :=
              mul_le_mul_of_nonneg_left (sum_abs_sub_le_two _ _ hq1 (hπS s)) (hMnn j ξ)
          _ = 2 * M j ξ := by ring
      have hin := neg_abs_le (∑ a, Qhat j ξ (s, a) * (π (j+1) ξ s a - πstar s a))
      have hL1 := hLip s _ hq1 _ (hπS s)
      have hL2 : L * ∑ a, |π (j+1) ξ s a - πstar s a| ≤ |L| * 2 := by
        calc L * ∑ a, |π (j+1) ξ s a - πstar s a| ≤ |L| * ∑ a, |π (j+1) ξ s a - πstar s a| :=
              mul_le_mul_of_nonneg_right (le_abs_self L)
                (Finset.sum_nonneg fun a _ => abs_nonneg _)
          _ ≤ |L| * 2 := mul_le_mul_of_nonneg_left (sum_abs_sub_le_two _ _ hq1 (hπS s))
              (abs_nonneg L)
      have hH := neg_abs_le (h s (π (j+1) ξ s) - h s (πstar s))
      have e1 : kl (πstar s) (π (j+1) ξ s) ≤ (1 + lam j * ω) * kl (πstar s) (π (j+1) ξ s) := by
        nlinarith [mul_nonneg hlj hω]
      have e2 := mul_le_mul_of_nonneg_left
        (show -(∑ a, Qhat j ξ (s, a) * (π (j+1) ξ s a - πstar s a)
            + h s (π (j+1) ξ s) - h s (πstar s)) ≤ 2 * M j ξ + 2 * |L| by linarith) hlj
      linarith
    calc D (j+1) ξ = ∑ s, νstar s * kl (πstar s) (π (j+1) ξ s) := rfl
      _ ≤ ∑ s, νstar s * (kl (πstar s) (π j ξ s) + lam j * (2 * M j ξ + 2 * |L|)) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (key s) (hνstar.1.1 s)
      _ = D j ξ + lam j * (2 * M j ξ + 2 * |L|) := by
          rw [Finset.sum_congr rfl (fun s _ => mul_add (νstar s) _ _), Finset.sum_add_distrib,
            ← Finset.sum_mul, hνstar.1.2, one_mul]
          rfl
  have hD0 : ∀ ξ, D 0 ξ ≤ Real.log (Fintype.card A) := by
    intro ξ
    have h0 : π 0 ξ = fun _ _ => 1 / (Fintype.card A : ℝ) := by
      funext s a; exact (hiter ξ).1 s a
    simp only [D]; rw [h0]
    exact kl_uniform_le_log νstar hνS πstar hπstar
  have hDbound : ∀ j ≤ k, ∀ ξ, D j ξ ≤ Real.log (Fintype.card A)
      + ∑ i ∈ Finset.range j, lam i * (2 * M i ξ + 2 * |L|) := by
    intro j
    induction j with
    | zero => intro _ ξ; simpa using hD0 ξ
    | succ j ih =>
      intro hj ξ
      rw [Finset.sum_range_succ]
      linarith [ih (by omega) ξ, hDstep j (by omega) ξ]
  -- measurability and integrability
  have hmeasπ : ∀ j ≤ k + 1, ∀ s a, Measurable (fun ξ => π j ξ s a) := fun j hj s a =>
    (hc1 j hj s a).mono (ℱ.le j) le_rfl
  have hMint : ∀ j < k + 1, Integrable (M j) μ := fun j hj =>
    integrable_finsetSum _ fun x _ => (hc2 j hj x).abs
  have hDmeas : ∀ j ≤ k + 1, Measurable (D j) := by
    intro j hj
    simp only [D, stationaryKL, kl]
    refine Finset.measurable_sum _ fun s _ => ?_
    refine Measurable.const_mul (Finset.measurable_sum _ fun a _ => ?_) _
    exact ((measurable_const.div (hmeasπ j hj s a)).log).const_mul _
  have hDkint : Integrable (D k) μ := by
    have hgint : Integrable (fun ξ => Real.log (Fintype.card A)
        + ∑ i ∈ Finset.range k, lam i * (2 * M i ξ + 2 * |L|)) μ := by
      refine (integrable_const _).add (integrable_finsetSum _ fun i hi => ?_)
      have := Finset.mem_range.1 hi
      exact (((hMint i (by omega)).const_mul 2).add (integrable_const _)).const_mul _
    refine Integrable.mono' hgint (hDmeas k (by omega)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn k (by omega) ξ)]
    exact hDbound k le_rfl ξ
  -- bias is nonnegative
  have hbias : 0 ≤ bias := by
    obtain ⟨ξ, hξ⟩ := (hc3 k (by omega)).exists
    exact le_trans (span_nonneg' _) hξ
  -- notation for step k
  set Qt : S × A → Ω → ℝ := fun x ξ => μ[fun ξ' => Qhat k ξ' x | ℱ k] ξ with hQt
  set Qb : Ω → S × A → ℝ := fun ξ => diffQ P (π k ξ) (fun s a => c s a + h s (π k ξ s))
    with hQb
  set dd : S → A → Ω → ℝ := fun s a ξ => π k ξ s a - πstar s a with hdd
  set Z1 : Ω → ℝ := fun ξ => ∑ s, νstar s * ∑ a, (Qhat k ξ (s, a) - Qt (s, a) ξ) * dd s a ξ
    with hZ1
  set Z2 : Ω → ℝ := fun ξ => ∑ s, νstar s * ∑ a, (Qb ξ (s, a) - Qt (s, a) ξ) * dd s a ξ
    with hZ2
  set inn : Ω → ℝ := fun ξ => ∑ s, νstar s * (∑ a, Qhat k ξ (s, a) * dd s a ξ
    + h s (π k ξ s) - h s (πstar s)) with hinn
  set sp : Ω → ℝ := fun ξ => span (Qhat k ξ) with hsp
  -- pathwise one-step inequality
  have hpath : ∀ ξ, lam k * inn ξ + (1 + lam k * ω) * D (k+1) ξ
      ≤ D k ξ + lam k ^ 2 * (sp ξ ^ 2 / 4 + L ^ 2) := by
    intro ξ
    have key : ∀ s, lam k * (∑ a, Qhat k ξ (s, a) * dd s a ξ + h s (π k ξ s) - h s (πstar s))
        + (1 + lam k * ω) * kl (πstar s) (π (k+1) ξ s)
        ≤ kl (πstar s) (π k ξ s) + lam k ^ 2 * (sp ξ ^ 2 / 4 + L ^ 2) := by
      intro s
      have t := hTP k le_rfl ξ s
      have hq := (hpol k (by omega) ξ).1 s
      have hqpos := (hpol k (by omega) ξ).2 s
      have hq1 := (hpol (k+1) le_rfl ξ).1 s
      set x := ∑ a, |π (k+1) ξ s a - π k ξ s a| with hx
      have hx0 : 0 ≤ x := Finset.sum_nonneg fun a _ => abs_nonneg _
      -- (i) linear term
      have hi : ∑ a, Qhat k ξ (s, a) * (π k ξ s a - π (k+1) ξ s a) ≤ sp ξ / 2 * x := by
        have := inner_le (fun a => Qhat k ξ (s, a)) (fun a => π k ξ s a - π (k+1) ξ s a)
          (⨅ y, Qhat k ξ y) (⨆ y, Qhat k ξ y) (fun a => bounds_span (Qhat k ξ) (s, a))
          (by rw [Finset.sum_sub_distrib, hq.2, hq1.2, sub_self])
        have hxx : ∑ a, |π k ξ s a - π (k+1) ξ s a| = x := by
          simp only [hx]; exact Finset.sum_congr rfl fun a _ => abs_sub_comm _ _
        rw [hxx] at this
        simpa [sp, span] using this
      -- (ii) regularizer term
      have hii : h s (π k ξ s) - h s (π (k+1) ξ s) ≤ |L| * x := by
        have h1 := hLip s _ hq1 _ hq
        have h2 : L * x ≤ |L| * x := mul_le_mul_of_nonneg_right (le_abs_self L) hx0
        have h3 := neg_abs_le (h s (π (k+1) ξ s) - h s (π k ξ s))
        linarith
      -- (iii) Pinsker
      have hiii : x ^ 2 ≤ 2 * kl (π (k+1) ξ s) (π k ξ s) := pinsker _ _ hq1 hqpos hq.2
      have hsplit : ∑ a, Qhat k ξ (s, a) * dd s a ξ
          = ∑ a, Qhat k ξ (s, a) * (π (k+1) ξ s a - πstar s a)
            + ∑ a, Qhat k ξ (s, a) * (π k ξ s a - π (k+1) ξ s a) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by simp only [dd]; ring
      have hsp0 : 0 ≤ sp ξ := span_nonneg' _
      have hB2 : (sp ξ / 2 + |L|) ^ 2 ≤ 2 * (sp ξ ^ 2 / 4 + L ^ 2) := by
        nlinarith [sq_nonneg (sp ξ / 2 - |L|), sq_abs L]
      have hq2 := mul_le_mul_of_nonneg_left hB2 (sq_nonneg (lam k))
      have hlin := mul_le_mul_of_nonneg_left hi hlk0
      have hreg := mul_le_mul_of_nonneg_left hii hlk0
      rw [hsplit]
      nlinarith [sq_nonneg (lam k * (sp ξ / 2 + |L|) - x)]
    calc lam k * inn ξ + (1 + lam k * ω) * D (k+1) ξ
        = ∑ s, νstar s * (lam k * (∑ a, Qhat k ξ (s, a) * dd s a ξ + h s (π k ξ s)
            - h s (πstar s)) + (1 + lam k * ω) * kl (πstar s) (π (k+1) ξ s)) := by
          simp only [inn, D, stationaryKL, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ ≤ ∑ s, νstar s * (kl (πstar s) (π k ξ s) + lam k ^ 2 * (sp ξ ^ 2 / 4 + L ^ 2)) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (key s) (hνstar.1.1 s)
      _ = D k ξ + lam k ^ 2 * (sp ξ ^ 2 / 4 + L ^ 2) := by
          rw [Finset.sum_congr rfl (fun s _ => mul_add (νstar s) _ _), Finset.sum_add_distrib,
            ← Finset.sum_mul, hνstar.1.2, one_mul]
          rfl
  -- the gap through the performance difference lemma
  have hgap : ∀ ξ, avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
      - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀ = inn ξ + Z2 ξ - Z1 ξ := by
    intro ξ
    have hpk : IsPolicy (π k ξ) := fun s =>
      ⟨((hpol k (by omega) ξ).1 s).1, ((hpol k (by omega) ξ).1 s).2⟩
    have L2 := lemma_2 P hP hmix c h (π k ξ) πstar hpk hπstar νstar hνstar s₀
    have : avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
        - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀
        = -(avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀
          - avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀) := by ring
    rw [this, L2]
    simp only [inn, Z1, Z2]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hs : ∑ a, Qb ξ (s, a) * (πstar s a - π k ξ s a)
        = -(∑ a, Qhat k ξ (s, a) * dd s a ξ + ∑ a, (Qb ξ (s, a) - Qt (s, a) ξ) * dd s a ξ
          - ∑ a, (Qhat k ξ (s, a) - Qt (s, a) ξ) * dd s a ξ) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun a _ => by simp only [dd]; ring
    simp only [Qb] at hs
    rw [hs]
    ring
  -- the bias term
  have hZ2 : ∀ᵐ ξ ∂μ, Z2 ξ ≤ bias := by
    filter_upwards [hc3 k (by omega)] with ξ hξ
    set w : S × A → ℝ := fun x => Qt x ξ - Qb ξ x with hw
    have hξ' : span w ≤ bias := hξ
    have hspw : 0 ≤ span w := span_nonneg' _
    have key : ∀ s, ∑ a, (Qb ξ (s, a) - Qt (s, a) ξ) * dd s a ξ ≤ span w := by
      intro s
      have hq := (hpol k (by omega) ξ).1 s
      have := inner_le (fun a => w (s, a)) (fun a => -dd s a ξ) (⨅ y, w y) (⨆ y, w y)
        (fun a => bounds_span w (s, a))
        (by simp only [dd]; rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, hq.2,
          (hπS s).2, sub_self, neg_zero])
      have h2 : ∑ a, |-dd s a ξ| ≤ 2 := by
        simp only [abs_neg, dd]; exact sum_abs_sub_le_two _ _ hq (hπS s)
      have e : ∑ a, (Qb ξ (s, a) - Qt (s, a) ξ) * dd s a ξ = ∑ a, w (s, a) * -dd s a ξ :=
        Finset.sum_congr rfl fun a _ => by simp only [w]; ring
      rw [e]
      have : (⨆ y, w y) - (⨅ y, w y) = span w := rfl
      nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ span w / 2 by linarith)]
    calc Z2 ξ ≤ ∑ s, νstar s * span w :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (key s) (hνstar.1.1 s)
      _ = span w := by rw [← Finset.sum_mul, hνstar.1.2, one_mul]
      _ ≤ bias := hξ'
  -- E[Z1] = 0
  have hdd_meas : ∀ s a, StronglyMeasurable[ℱ k] (dd s a) := fun s a =>
    ((hc1 k (by omega) s a).sub_const _).stronglyMeasurable
  have hdd_bd : ∀ s a ξ, ‖dd s a ξ‖ ≤ 1 := by
    intro s a ξ
    have hq := (hpol k (by omega) ξ).1 s
    have h1 : π k ξ s a ≤ 1 := by
      have := Finset.single_le_sum (f := π k ξ s) (fun b _ => hq.1 b) (Finset.mem_univ a)
      rw [hq.2] at this; exact this
    have h2 : πstar s a ≤ 1 := by
      have := Finset.single_le_sum (f := πstar s) (fun b _ => (hπstar s).1 b) (Finset.mem_univ a)
      rw [(hπstar s).2] at this; exact this
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> simp only [dd] <;> linarith [hq.1 a, (hπstar s).1 a]
  have hterm_int : ∀ s a, Integrable (fun ξ => (Qhat k ξ (s, a) - Qt (s, a) ξ) * dd s a ξ) μ :=
    fun s a => ((hc2 k (by omega) (s, a)).sub integrable_condExp).mul_bdd
      ((hdd_meas s a).mono (ℱ.le k)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hdd_bd s a))
  have hterm_zero : ∀ s a, ∫ ξ, (Qhat k ξ (s, a) - Qt (s, a) ξ) * dd s a ξ ∂μ = 0 := by
    intro s a
    set f : Ω → ℝ := fun ξ => Qhat k ξ (s, a) with hf
    set g : Ω → ℝ := dd s a with hg
    have hfi : Integrable f μ := hc2 k (by omega) (s, a)
    have hgae : AEStronglyMeasurable g μ := ((hdd_meas s a).mono (ℱ.le k)).aestronglyMeasurable
    have hgf : Integrable (g * f) μ :=
      hfi.bdd_mul hgae (Filter.Eventually.of_forall (hdd_bd s a))
    have hgQ : Integrable (g * μ[f | ℱ k]) μ :=
      integrable_condExp.bdd_mul hgae (Filter.Eventually.of_forall (hdd_bd s a))
    have hpull := condExp_mul_of_stronglyMeasurable_left (hdd_meas s a) hgf hfi
    have h1 : ∫ ξ, (g * f) ξ ∂μ = ∫ ξ, (g * μ[f | ℱ k]) ξ ∂μ := by
      rw [← integral_condExp (ℱ.le k)]
      exact integral_congr_ae hpull
    have e : (fun ξ => (Qhat k ξ (s, a) - Qt (s, a) ξ) * dd s a ξ)
        = fun ξ => (g * f) ξ - (g * μ[f | ℱ k]) ξ := by
      funext ξ; simp only [Pi.mul_apply, g, f, Qt]; ring
    rw [e, integral_sub hgf hgQ, h1, sub_self]
  have hZ1int : Integrable Z1 μ := by
    simp only [Z1]
    refine integrable_finsetSum _ fun s _ => ?_
    exact (integrable_finsetSum _ fun a _ => hterm_int s a).const_mul _
  have hZ1zero : ∫ ξ, Z1 ξ ∂μ = 0 := by
    simp only [Z1]
    rw [integral_finsetSum _ fun s _ => (integrable_finsetSum _ fun a _ =>
      hterm_int s a).const_mul _]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun a _ => hterm_int s a]
    simp [hterm_zero]
  -- E[sp²] ≤ κ²
  have hspint : Integrable (fun ξ => sp ξ ^ 2) μ := (hc4 k (by omega)).1
  have hsp2 : ∫ ξ, sp ξ ^ 2 ∂μ ≤ κ ^ 2 := by
    calc ∫ ξ, sp ξ ^ 2 ∂μ = ∫ ξ, (μ[fun ξ' => span (Qhat k ξ') ^ 2 | ℱ k]) ξ ∂μ :=
          (integral_condExp (ℱ.le k)).symm
      _ ≤ ∫ _ξ, κ ^ 2 ∂μ :=
          integral_mono_ae integrable_condExp (integrable_const _) (hc4 k (by omega)).2
      _ = κ ^ 2 := by simp
  -- integrate
  set G : Ω → ℝ := fun ξ => D k ξ + lam k ^ 2 / 4 * sp ξ ^ 2
    + (lam k ^ 2 * L ^ 2 + lam k * bias) - lam k * Z1 ξ with hG
  have hGint : Integrable G μ :=
    ((hDkint.add (hspint.const_mul _)).add (integrable_const _)).sub (hZ1int.const_mul _)
  have hGval : ∫ ξ, G ξ ∂μ = ∫ ξ, D k ξ ∂μ + lam k ^ 2 / 4 * ∫ ξ, sp ξ ^ 2 ∂μ
      + (lam k ^ 2 * L ^ 2 + lam k * bias) := by
    have hA1 : Integrable (fun ξ => D k ξ + lam k ^ 2 / 4 * sp ξ ^ 2) μ :=
      hDkint.add (hspint.const_mul _)
    have hA : Integrable (fun ξ => D k ξ + lam k ^ 2 / 4 * sp ξ ^ 2
        + (lam k ^ 2 * L ^ 2 + lam k * bias)) μ := hA1.add (integrable_const _)
    have hB : Integrable (fun ξ => lam k * Z1 ξ) μ := hZ1int.const_mul _
    have hC : Integrable (fun ξ => lam k ^ 2 / 4 * sp ξ ^ 2) μ := hspint.const_mul _
    simp only [G]
    rw [integral_sub hA hB, integral_add hA1 (integrable_const _), integral_add hDkint hC,
      integral_const_mul, integral_const_mul, hZ1zero]
    simp
  have hFG : ∀ᵐ ξ ∂μ, lam k * (avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)
          + (1 + lam k * ω) * stationaryKL νstar (π (k + 1) ξ) πstar ≤ G ξ := by
    filter_upwards [hZ2] with ξ hξ
    rw [hgap ξ]
    have := hpath ξ
    have := mul_le_mul_of_nonneg_left hξ hlk0
    simp only [G, D] at *
    nlinarith
  have hRHS : ∫ ξ, G ξ ∂μ ≤ ∫ ξ, stationaryKL νstar (π k ξ) πstar ∂μ + lam k * bias
      + lam k ^ 2 * (κ ^ 2 / 4 + L ^ 2) := by
    rw [hGval]
    have := mul_le_mul_of_nonneg_left hsp2 (show 0 ≤ lam k ^ 2 / 4 by positivity)
    simp only [D]
    nlinarith
  by_cases hFi : Integrable (fun ξ => lam k * (avgCost P (π k ξ) (fun s a => c s a + h s (π k ξ s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)
          + (1 + lam k * ω) * stationaryKL νstar (π (k + 1) ξ) πstar) μ
  · exact (integral_mono_ae hFi hGint hFG).trans hRHS
  · rw [integral_undef hFi]
    have h1 : 0 ≤ ∫ ξ, stationaryKL νstar (π k ξ) πstar ∂μ :=
      integral_nonneg fun ξ => hDnn k (by omega) ξ
    have h2 : 0 ≤ lam k * bias := mul_nonneg hlk0 hbias
    have h3 : 0 ≤ lam k ^ 2 * (κ ^ 2 / 4 + L ^ 2) := by positivity
    linarith
