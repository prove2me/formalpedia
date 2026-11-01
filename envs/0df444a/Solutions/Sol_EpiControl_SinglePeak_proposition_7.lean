-- Prove2me | solution 1 for EpiControl.SinglePeak.proposition_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:03:14.83186+00:00
-- url     : https://prove2.me/submissions/0b3e91f5-7d2e-4dd3-a2bf-e37d847a24a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model
import Theorems.Thm_EpiControl_SinglePeak_proposition_1
import Theorems.Thm_EpiControl_SinglePeak_lemma_13
import Theorems.Thm_EpiControl_SinglePeak_proposition_2_iii
import Theorems.Thm_EpiControl_SinglePeak_g_strictly_quasiconcave

open MeasureTheory Set Filter Topology

namespace EpiAux

lemma exp_lipschitzOnWith_Iic (M : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp M)) Real.exp (Iic M) := by
  apply (convex_Iic M).lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => Real.differentiableAt_exp)
  intro x hx
  rw [Real.deriv_exp]
  have : ‖Real.exp x‖₊ = Real.toNNReal (Real.exp x) := by
    ext; simp [abs_of_pos (Real.exp_pos x), (Real.exp_pos x).le]
  rw [this]
  exact Real.toNNReal_le_toNNReal (Real.exp_le_exp.mpr hx)

/-- Linear integral equation `x(t) = x0 + ∫₀ᵗ k x` has the exponential solution. -/
theorem lin_eq_exp {T x0 K : ℝ} (hT : 0 ≤ T) {k x : ℝ → ℝ}
    (hk : IntervalIntegrable k volume 0 T) (hkb : ∀ r ∈ Icc 0 T, |k r| ≤ K)
    (hx : ContinuousOn x (Icc 0 T))
    (heq : ∀ t ∈ Icc 0 T, x t = x0 + ∫ r in (0:ℝ)..t, k r * x r) :
    ∀ t ∈ Icc 0 T, x t = x0 * Real.exp (∫ r in (0:ℝ)..t, k r) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hkb 0 ⟨le_rfl, hT⟩)
  have huIcc : uIcc 0 T = Icc 0 T := uIcc_of_le hT
  set A : ℝ → ℝ := fun t => ∫ r in (0:ℝ)..t, k r with hA
  have hkx : IntervalIntegrable (fun r => k r * x r) volume 0 T :=
    hk.mul_continuousOn (by rw [huIcc]; exact hx)
  have hkI : ∀ t ∈ Icc 0 T, IntervalIntegrable k volume 0 t := fun t ht =>
    hk.mono_set (by rw [huIcc, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  -- A is K-Lipschitz on [0,T]
  have hAL : LipschitzOnWith (Real.toNNReal K) A (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
    have : A t - A u = ∫ r in u..t, k r := by
      simp only [hA]; exact intervalIntegral.integral_interval_sub_left (hkI t ht) (hkI u hu)
    rw [this, ← Real.norm_eq_abs]
    calc ‖∫ r in u..t, k r‖ ≤ K * |t - u| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro r hr
          rw [Real.norm_eq_abs]
          apply hkb
          have := uIoc_subset_uIcc hr
          rw [mem_uIcc] at this
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
            linarith [ht.1, ht.2, hu.1, hu.2]
      _ = K * |t - u| := rfl
  have hAb : ∀ t ∈ Icc 0 T, -A t ≤ K * T := by
    intro t ht
    have h0 : A 0 = 0 := by simp [hA]
    have := hAL.dist_le_mul t ht 0 ⟨le_rfl, hT⟩
    rw [Real.dist_eq, Real.dist_eq, h0, Real.coe_toNNReal _ hK, sub_zero, sub_zero,
      abs_of_nonneg ht.1] at this
    have h2 := neg_abs_le (A t)
    nlinarith [ht.2]
  set E : ℝ → ℝ := fun t => Real.exp (-A t) with hE
  have hEL : LipschitzOnWith (Real.toNNReal (Real.exp (K * T)) * Real.toNNReal K) E (Icc 0 T) := by
    have := (exp_lipschitzOnWith_Iic (K * T)).comp hAL.neg (fun t ht => hAb t ht)
    exact this
  set x' : ℝ → ℝ := fun t => x0 + ∫ r in (0:ℝ)..t, k r * x r with hx'
  have hx'AC : AbsolutelyContinuousOnInterval x' 0 T := by
    have h1 := hkx.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
    have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => x0) 0 T :=
      (LipschitzWith.const x0).lipschitzOnWith.absolutelyContinuousOnInterval
    exact h2.fun_add h1
  have hEAC : AbsolutelyContinuousOnInterval E 0 T := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [huIcc]; exact hEL
  have hFAC : AbsolutelyContinuousOnInterval (fun t => x' t * E t) 0 T := hx'AC.fun_mul hEAC
  have hderiv : ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt (fun t => x' t * E t) 0 t := by
    filter_upwards [hkx.ae_hasDerivAt_integral, hk.ae_hasDerivAt_integral] with t h1 h2 ht
    have d1 : HasDerivAt x' (k t * x t) t := (h1 ht 0 (by simp)).const_add x0
    have d2 : HasDerivAt A (k t) t := h2 ht 0 (by simp)
    have d3 : HasDerivAt E (Real.exp (-A t) * -k t) t := (d2.neg).exp
    rw [huIcc] at ht
    have hxx : x t = x' t := heq t ht
    refine (d1.fun_mul d3).congr_deriv ?_
    rw [hxx]; simp only [hE]; ring
  obtain ⟨C, hC⟩ := hFAC.const_of_ae_hasDerivAt_zero hderiv
  intro t ht
  have h0 := hC 0 (by simp)
  have ht' := hC t (by rw [huIcc]; exact ht)
  have hx'0 : x' 0 = x0 := by simp [hx']
  have hE0 : E 0 = 1 := by simp [hE, hA]
  rw [hx'0, hE0, mul_one] at h0
  rw [heq t ht]
  change x' t = x0 * Real.exp (A t)
  have hEt : E t * Real.exp (A t) = 1 := by
    simp only [hE]; rw [← Real.exp_add]; simp
  calc x' t = x' t * E t * Real.exp (A t) := by rw [mul_assoc, hEt, mul_one]
    _ = x0 * Real.exp (A t) := by rw [ht', h0]


/-- The integral of a strictly decreasing function is strictly concave. -/
theorem strictConcaveOn_of_integral {L c : ℝ} {a F : ℝ → ℝ}
    (hI : IntervalIntegrable a volume 0 L) (ha : StrictAntiOn a (Icc 0 L))
    (hF : ∀ t ∈ Icc 0 L, F t = c + ∫ r in (0:ℝ)..t, a r) :
    StrictConcaveOn ℝ (Icc 0 L) F := by
  have hsub : ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L, IntervalIntegrable a volume u v := by
    intro u hu v hv
    apply hI.mono_set
    apply uIcc_subset_uIcc <;> rw [uIcc_of_le (hu.1.trans hu.2)] <;> assumption
  have hdiff : ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L, F v - F u = ∫ r in u..v, a r := by
    intro u hu v hv
    have h0 : (0:ℝ) ∈ Icc 0 L := ⟨le_rfl, hu.1.trans hu.2⟩
    rw [hF v hv, hF u hu]
    rw [show ∀ x y z : ℝ, c + x - (c + y) = x - y from fun x y z => by ring]
    · exact intervalIntegral.integral_interval_sub_left (hsub 0 h0 v hv) (hsub 0 h0 u hu)
    · exact 0
  have key : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, x < y → ∀ p q : ℝ, 0 < p → 0 < q → p + q = 1 →
      p * F x + q * F y < F (p * x + q * y) := by
    intro x hx y hy hxy p q hp hq hpq
    set z := p * x + q * y with hz
    have hp' : p = 1 - q := by linarith
    have hzx : z - x = q * (y - x) := by rw [hz, hp']; ring
    have hyz : y - z = p * (y - x) := by rw [hz, hp']; ring
    have hxz : x < z := by nlinarith [mul_pos hq (sub_pos.2 hxy)]
    have hzy : z < y := by nlinarith [mul_pos hp (sub_pos.2 hxy)]
    set m := (x + z) / 2 with hm
    have hxm : x < m := by rw [hm]; linarith
    have hmz : m < z := by rw [hm]; linarith
    have hzI : z ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hy.2]⟩
    have hmI : m ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hy.2]⟩
    have I1 : (m - x) * a m ≤ ∫ r in x..m, a r := by
      have := intervalIntegral.integral_mono_on hxm.le (intervalIntegrable_const (c := a m))
        (hsub x hx m hmI) (fun r hr => ha.antitoneOn ⟨by linarith [hx.1, hr.1], by
          linarith [hr.2, hmI.2]⟩ hmI hr.2)
      simpa using this
    have I2 : (z - m) * a z ≤ ∫ r in m..z, a r := by
      have := intervalIntegral.integral_mono_on hmz.le (intervalIntegrable_const (c := a z))
        (hsub m hmI z hzI) (fun r hr => ha.antitoneOn ⟨by linarith [hmI.1, hr.1], by
          linarith [hr.2, hzI.2]⟩ hzI hr.2)
      simpa using this
    have I3 : (∫ r in z..y, a r) ≤ (y - z) * a z := by
      have := intervalIntegral.integral_mono_on hzy.le (hsub z hzI y hy)
        (intervalIntegrable_const (c := a z)) (fun r hr => ha.antitoneOn hzI ⟨by
          linarith [hzI.1, hr.1], by linarith [hr.2, hy.2]⟩ hr.1)
      simpa using this
    have hlt : a z < a m := ha hmI hzI hmz
    have hsplit : (∫ r in x..z, a r) = (∫ r in x..m, a r) + ∫ r in m..z, a r :=
      (intervalIntegral.integral_add_adjacent_intervals (hsub x hx m hmI) (hsub m hmI z hzI)).symm
    have e1 := hdiff x hx z hzI
    have e2 := hdiff z hzI y hy
    have hgap : (z - x) * a z < ∫ r in x..z, a r := by
      rw [hsplit]
      have : (m - x) * a z < (m - x) * a m := mul_lt_mul_of_pos_left hlt (by linarith)
      nlinarith
    have A1 : p * ((z - x) * a z) < p * (F z - F x) := by
      rw [e1]; exact mul_lt_mul_of_pos_left hgap hp
    have A2 : q * (F y - F z) ≤ q * ((y - z) * a z) := by
      rw [e2]; exact mul_le_mul_of_nonneg_left I3 hq.le
    have A3 : p * ((z - x) * a z) = q * ((y - z) * a z) := by
      rw [hzx, hyz]; ring
    have : F z = (p + q) * F z := by rw [hpq, one_mul]
    nlinarith
  refine ⟨convex_Icc 0 L, ?_⟩
  intro x hx y hy hne p q hp hq hpq
  simp only [smul_eq_mul]
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x hx y hy h p q hp hq hpq
  · have := key y hy x hx h q p hq hp (by linarith)
    rw [add_comm (p * F x), add_comm (p * x)]
    exact this

open EpiControl.SinglePeak in
theorem costate_congr {P : Params} {β βh s i η : ℝ → ℝ} (hη : P.IsCostate β s i η)
    (hae : βh =ᵐ[volume.restrict (Icc 0 P.T)] β) : P.IsCostate βh s i η := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hη
  refine ⟨h1, h2, ?_, ?_, h5⟩
  · intro t ht
    refine (h3 t ht).trans ?_
    congr 1
    apply intervalIntegral.integral_congr_ae
    have := (ae_restrict_iff' measurableSet_Icc).1 hae
    filter_upwards [this] with r hr hrI
    rw [uIoc_of_le ht.2] at hrI
    rw [hr ⟨by linarith [ht.1, hrI.1], hrI.2⟩]
  · filter_upwards [h4, hae] with r h hr
    rw [hr]; exact h

open EpiControl.SinglePeak in
/-- Exponential representation of the SIR path. -/
theorem path_exp {P : Params} (hP : P.Standing) {β s i : ℝ → ℝ} (hβ : P.Admissible β)
    (hpath : P.IsSIRPath β s i) :
    IntervalIntegrable β volume 0 P.T ∧
    (∀ t ∈ Icc 0 P.T, i t = P.i0 * Real.exp (∫ r in (0:ℝ)..t, (β r * s r - P.γ))) ∧
    (∀ t ∈ Icc 0 P.T, s t = P.s0 * Real.exp (∫ r in (0:ℝ)..t, -(β r * i r))) := by
  have hT : 0 ≤ P.T := hP.T_pos.le
  obtain ⟨hs, hi, heq⟩ := hpath
  have huIcc : uIcc 0 P.T = Icc 0 P.T := uIcc_of_le hT
  have hβb : ∀ r ∈ Icc 0 P.T, |β r| ≤ P.bbar := by
    intro r hr
    have := hβ.2 r hr
    rw [abs_of_pos (lt_of_lt_of_le hP.bl_pos this.1)]; exact this.2
  have hβI : IntervalIntegrable β volume 0 P.T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    refine Measure.integrableOn_of_bounded (M := P.bbar) (by simp) hβ.1.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs]; exact hβb r hr)
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hs
  obtain ⟨I, hI⟩ := isCompact_Icc.exists_bound_of_continuousOn hi
  have hS0 : 0 ≤ S := le_trans (norm_nonneg _) (hS 0 ⟨le_rfl, hT⟩)
  have hI0 : 0 ≤ I := le_trans (norm_nonneg _) (hI 0 ⟨le_rfl, hT⟩)
  have hbb : 0 ≤ P.bbar := (hP.bl_pos.trans hP.bl_lt_bbar).le
  refine ⟨hβI, ?_, ?_⟩
  · apply lin_eq_exp hT (K := P.bbar * S + |P.γ|)
    · exact (hβI.mul_continuousOn (by rw [huIcc]; exact hs)).sub intervalIntegrable_const
    · intro r hr
      calc |β r * s r - P.γ| ≤ |β r * s r| + |P.γ| := abs_sub _ _
        _ ≤ P.bbar * S + |P.γ| := by
          rw [abs_mul]
          have := hS r hr; rw [Real.norm_eq_abs] at this
          gcongr
          · exact hβb r hr
    · exact hi
    · intro t ht
      rw [(heq t ht).2]
      congr 1
      apply intervalIntegral.integral_congr
      intro r _; simp only; ring
  · apply lin_eq_exp hT (K := P.bbar * I)
    · exact (hβI.mul_continuousOn (by rw [huIcc]; exact hi)).neg
    · intro r hr
      rw [abs_neg, abs_mul]
      have := hI r hr; rw [Real.norm_eq_abs] at this
      gcongr
      exact hβb r hr
    · exact hs
    · intro t ht
      rw [(heq t ht).1, sub_eq_add_neg]
      congr 1
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro r _; simp only; ring

end EpiAux

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (dc : ℝ) (hA1 : P.Assumption1 dc)
    (β s i : ℝ → ℝ) (hopt : P.IsOptimal β s i) :
    ∃ tstar ∈ Icc 0 P.T, ∃ βh : ℝ → ℝ,
      P.Admissible βh ∧ βh =ᵐ[volume.restrict (Icc 0 P.T)] β ∧
      AntitoneOn βh (Icc 0 tstar) ∧ MonotoneOn βh (Icc tstar P.T) ∧
      StrictConcaveOn ℝ (Icc 0 tstar) (fun t => Real.log (i t)) ∧
      ∀ t₁ ∈ Icc 0 tstar, ∀ t₂ ∈ Icc 0 tstar,
        IsLocalMaxOn i (Icc 0 tstar) t₁ → IsLocalMaxOn i (Icc 0 tstar) t₂ → t₁ = t₂ := by
  obtain ⟨η, hη⟩ := (proposition_1 P hP).2 β s i hopt
  obtain ⟨βh, hopth, hae, hconv⟩ := lemma_13 P hP β s i hopt η hη
  have hηh : P.IsCostate βh s i η := EpiAux.costate_congr hη hae
  obtain ⟨tstar, htstar, hmono, hanti⟩ :=
    g_strictly_quasiconcave P hP dc hA1 βh s i hopth η hηh hconv
  have hT : 0 ≤ P.T := hP.T_pos.le
  have hsubI : Icc 0 tstar ⊆ Icc 0 P.T := Icc_subset_Icc le_rfl htstar.2
  have hsubI' : Icc tstar P.T ⊆ Icc 0 P.T := Icc_subset_Icc htstar.1 le_rfl
  have hanti_b : AntitoneOn βh (Icc 0 tstar) := by
    intro t ht t' ht' hle
    rcases hle.eq_or_lt with h | h
    · rw [h]
    · exact proposition_2_iii P hP βh s i hopth η hηh hconv t' (hsubI ht') t (hsubI ht)
        (hmono ht ht' h)
  have hmono_b : MonotoneOn βh (Icc tstar P.T) := by
    intro t ht t' ht' hle
    rcases hle.eq_or_lt with h | h
    · rw [h]
    · exact proposition_2_iii P hP βh s i hopth η hηh hconv t (hsubI' ht) t' (hsubI' ht')
        (hanti ht ht' h)
  -- the SIR path of `βh`
  obtain ⟨hβI, hiexp, hsexp⟩ := EpiAux.path_exp hP hopth.1 hopth.2.1
  have hs_cont : ContinuousOn s (Icc 0 P.T) := hopth.2.1.1
  have hi_cont : ContinuousOn i (Icc 0 P.T) := hopth.2.1.2.1
  have hi0 : 0 < P.i0 := hP.i0_mem.1
  have hs0 : 0 < P.s0 := hP.s0_mem.1
  have hipos : ∀ t ∈ Icc 0 P.T, 0 < i t := fun t ht => by
    rw [hiexp t ht]; exact mul_pos hi0 (Real.exp_pos _)
  have hspos : ∀ t ∈ Icc 0 P.T, 0 < s t := fun t ht => by
    rw [hsexp t ht]; exact mul_pos hs0 (Real.exp_pos _)
  have hβpos : ∀ t ∈ Icc 0 P.T, 0 < βh t := fun t ht =>
    lt_of_lt_of_le hP.bl_pos (hopth.1.2 t ht).1
  have huIcc : uIcc 0 P.T = Icc 0 P.T := uIcc_of_le hT
  -- s is strictly decreasing
  have hsanti : StrictAntiOn s (Icc 0 P.T) := by
    intro t ht t' ht' hlt
    rw [hsexp t ht, hsexp t' ht']
    apply mul_lt_mul_of_pos_left _ hs0
    apply Real.exp_lt_exp.mpr
    have hk : IntervalIntegrable (fun r => -(βh r * i r)) volume 0 P.T :=
      (hβI.mul_continuousOn (by rw [huIcc]; exact hi_cont)).neg
    have hsub : ∀ u ∈ Icc 0 P.T, IntervalIntegrable (fun r => -(βh r * i r)) volume 0 u :=
      fun u hu => hk.mono_set (by rw [huIcc, uIcc_of_le hu.1]; exact Icc_subset_Icc le_rfl hu.2)
    have hdiff := intervalIntegral.integral_interval_sub_left (hsub t' ht') (hsub t ht)
    have hpos : 0 < ∫ r in t..t', βh r * i r := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hlt
      · apply (hβI.mul_continuousOn (by rw [huIcc]; exact hi_cont)).mono_set
        rw [huIcc, uIcc_of_le hlt.le]; exact Icc_subset_Icc ht.1 ht'.2
      · intro r hr
        have hrI : r ∈ Icc 0 P.T := ⟨by linarith [ht.1, hr.1], by linarith [ht'.2, hr.2]⟩
        exact mul_pos (hβpos r hrI) (hipos r hrI)
    simp only [intervalIntegral.integral_neg] at hdiff ⊢
    linarith
  -- log-concavity
  set a : ℝ → ℝ := fun r => βh r * s r - P.γ with ha_def
  have haI : IntervalIntegrable a volume 0 tstar := by
    apply ((hβI.mul_continuousOn (by rw [huIcc]; exact hs_cont)).sub
      (intervalIntegrable_const (c := P.γ))).mono_set
    rw [huIcc, uIcc_of_le htstar.1]; exact hsubI
  have ha_anti : StrictAntiOn a (Icc 0 tstar) := by
    intro r1 hr1 r2 hr2 hlt
    simp only [ha_def]
    have h1 : βh r2 ≤ βh r1 := hanti_b hr1 hr2 hlt.le
    have h2 : s r2 < s r1 := hsanti (hsubI hr1) (hsubI hr2) hlt
    have h3 := hβpos r2 (hsubI hr2)
    have h4 := hspos r1 (hsubI hr1)
    have : βh r2 * s r2 < βh r2 * s r1 := mul_lt_mul_of_pos_left h2 h3
    have : βh r2 * s r1 ≤ βh r1 * s r1 := mul_le_mul_of_nonneg_right h1 h4.le
    linarith
  have hconc : StrictConcaveOn ℝ (Icc 0 tstar) (fun t => Real.log (i t)) := by
    apply EpiAux.strictConcaveOn_of_integral (c := Real.log P.i0) haI ha_anti
    intro t ht
    rw [hiexp t (hsubI ht), Real.log_mul hi0.ne' (Real.exp_pos _).ne', Real.log_exp]
  refine ⟨tstar, htstar, βh, hopth.1, hae, hanti_b, hmono_b, hconc, ?_⟩
  intro t₁ ht₁ t₂ ht₂ hmax₁ hmax₂
  have hlog : ∀ t ∈ Icc 0 tstar, IsLocalMaxOn i (Icc 0 tstar) t →
      IsMaxOn (fun t => Real.log (i t)) (Icc 0 tstar) t := by
    intro t ht hmax
    apply IsMaxOn.of_isLocalMaxOn_of_concaveOn ht _ hconc.concaveOn
    have hm : ∀ᶠ y in 𝓝[Icc 0 tstar] t, y ∈ Icc 0 tstar := self_mem_nhdsWithin
    filter_upwards [hmax, hm] with y hy hyI
    exact Real.log_le_log (hipos y (hsubI hyI)) hy
  exact hconc.eq_of_isMaxOn (hlog t₁ ht₁ hmax₁) (hlog t₂ ht₂ hmax₂) ht₁ ht₂
