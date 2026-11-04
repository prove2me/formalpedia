-- Prove2me | solution 1 for FiniteEnergyPlane.windPi_eq_windInf_sub_card
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:40:26.613544+00:00
-- url     : https://prove2.me/submissions/cb47b585-b20f-42b6-9812-81e8da0e80b2

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray
import Theorems.Thm_FiniteEnergyPlane_exists_hasWindPi_of_nondegenerate
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_continuousOn_family
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_eq_sum
import Theorems.Thm_FiniteEnergyPlane_hasWindInfAt_cylInf_of_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_hasWindInfAt_cylEndAt_of_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_continuousOn_piDs

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

lemma c1w_ccwLoop_periodic (R : ℝ) : Function.Periodic (ccwLoop R) 1 := by
  intro t
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma c1w_ccwLoop_continuous (R : ℝ) : Continuous (ccwLoop R) := by
  unfold ccwLoop
  fun_prop

lemma c1w_norm_ccwLoop (R t : ℝ) (hR : 0 ≤ R) : ‖ccwLoop R t‖ = R := by
  simp only [ccwLoop, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

lemma c1w_ccwLoop_pow (R t : ℝ) (m : ℕ) :
    ccwLoop R t ^ m = ((R ^ m : ℝ) : ℂ) * Complex.exp (((2 * π * m * t : ℝ) : ℂ) * Complex.I) := by
  simp only [ccwLoop, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The loop `t ↦ a ρ^m e^{2πimt}` (`a ≠ 0`, `ρ > 0`) has winding number `m`. -/
lemma c1w_hasLoopWind_const_mul_pow (a : ℂ) (ha : a ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) :
    HasLoopWind (fun t => a * ccwLoop ρ t ^ m) m := by
  have hc : Continuous (fun t => a * ccwLoop ρ t ^ m) :=
    continuous_const.mul ((c1w_ccwLoop_continuous ρ).pow m)
  refine ⟨hc, fun t => by simp only [c1w_ccwLoop_periodic ρ t], fun t => ?_, ?_⟩
  · refine mul_ne_zero ha (pow_ne_zero _ ?_)
    intro h
    have := c1w_norm_ccwLoop ρ t hρ.le
    rw [h, norm_zero] at this
    linarith
  · refine ⟨fun t => Complex.arg a + 2 * π * m * t, by fun_prop, fun t => ?_, by push_cast; ring⟩
    have hn : ‖a * ccwLoop ρ t ^ m‖ = ‖a‖ * ρ ^ m := by
      rw [norm_mul, norm_pow, c1w_norm_ccwLoop ρ t hρ.le]
    dsimp only
    rw [hn, c1w_ccwLoop_pow]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
    push_cast
    rw [show ((Complex.arg a : ℂ) + 2 * π * m * t) * Complex.I =
        (Complex.arg a : ℂ) * Complex.I + 2 * π * m * t * Complex.I by ring, Complex.exp_add]
    ring

lemma c1w_alg (w p q : ℂ) : (w.re : ℂ) * p + (w.im : ℂ) * q =
    (p - Complex.I * q) / 2 * w + (p + Complex.I * q) / 2 * starRingEnd ℂ w := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have h2 : starRingEnd ℂ w = (w.re : ℂ) - (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(p - Complex.I * q) / 2) * hw + (-(p + Complex.I * q) / 2) * h2 +
    (q * (w.im : ℂ)) * Complex.I_sq

/-- Let `p, q` be continuous on `B(z₀, R)` with `Im(conj p(z₀) · q(z₀)) > 0` (so that
`w ↦ Re(w) p(z₀) + Im(w) q(z₀)` is an orientation-preserving real-linear isomorphism of `ℂ`), and let
`F(z) = Re((z - z₀)^m) p(z) + Im((z - z₀)^m) q(z)` on `B(z₀, R)`. Then on some smaller disc
`B(z₀, r)`, `F` has no zero other than `z₀`, and `F` has winding number `m` along every
counterclockwise circle `t ↦ z₀ + ρ e^{2πit}`, `0 < ρ < r`. -/
theorem exists_ball_hasLoopWind_re_mul_add_im_mul_aux (F p q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hp : ContinuousOn p (ball z₀ R)) (hq : ContinuousOn q (ball z₀ R))
    (hpq : 0 < (starRingEnd ℂ (p z₀) * q z₀).im)
    (hF : ∀ z ∈ ball z₀ R,
      F z = (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z) :
    ∃ r > (0 : ℝ), r ≤ R ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → F z ≠ 0) ∧
      ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => F (z₀ + ccwLoop ρ t)) m := by
  set A : ℂ → ℂ := fun z => (p z - Complex.I * q z) / 2 with hA
  set B : ℂ → ℂ := fun z => (p z + Complex.I * q z) / 2 with hB
  have hFAB : ∀ z ∈ ball z₀ R, F z = A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) := by
    intro z hz
    rw [hF z hz]
    exact c1w_alg _ _ _
  -- `‖B z₀‖ < ‖A z₀‖`
  have hAB : ‖B z₀‖ < ‖A z₀‖ := by
    have key : Complex.normSq (A z₀) - Complex.normSq (B z₀) =
        (starRingEnd ℂ (p z₀) * q z₀).im := by
      simp only [hA, hB, Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
      norm_num
      ring
    have h2 : ‖B z₀‖ ^ 2 < ‖A z₀‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  set κ := ‖A z₀‖ - ‖B z₀‖ with hκ
  have hκ0 : 0 < κ := by linarith
  have hA0 : A z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hAB; exact absurd hAB (not_lt.2 (norm_nonneg _))
  have hzR : ball z₀ R ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hR)
  have hAc : ContinuousAt A z₀ :=
    ((hp.continuousAt hzR).sub (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hBc : ContinuousAt B z₀ :=
    ((hp.continuousAt hzR).add (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hev : ∀ᶠ z in 𝓝 z₀, ‖A z - A z₀‖ < κ / 2 ∧ ‖B z - B z₀‖ < κ / 2 ∧ z ∈ ball z₀ R := by
    refine ((hAc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and
      (((hBc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and hzR)
    · simp only [Pi.sub_apply, hA, sub_self, norm_zero]; exact half_pos hκ0
    · simp only [Pi.sub_apply, hB, sub_self, norm_zero]; exact half_pos hκ0
  obtain ⟨r, hr, hrs⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r' := min r R
  have hr' : 0 < r' := lt_min hr hR
  -- the key estimate `‖F z - A z₀ w‖ < ‖A z₀‖ ‖w‖` for `w = (z - z₀)^m ≠ 0`
  have hest : ∀ z ∈ ball z₀ r', z ≠ z₀ →
      ‖F z - A z₀ * (z - z₀) ^ m‖ < ‖A z₀ * (z - z₀) ^ m‖ := by
    intro z hz hne
    obtain ⟨h1, h2, h3⟩ := hrs z (ball_subset_ball (min_le_left _ _) hz)
    have hw : 0 < ‖(z - z₀) ^ m‖ := norm_pos_iff.2 (pow_ne_zero _ (sub_ne_zero.2 hne))
    rw [hFAB z h3, show A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) -
        A z₀ * (z - z₀) ^ m = (A z - A z₀) * (z - z₀) ^ m +
          B z * starRingEnd ℂ ((z - z₀) ^ m) by ring]
    have hBz : ‖B z‖ < ‖B z₀‖ + κ / 2 := by
      have := norm_sub_norm_le (B z) (B z₀)
      linarith
    calc _ ≤ ‖(A z - A z₀) * (z - z₀) ^ m‖ + ‖B z * starRingEnd ℂ ((z - z₀) ^ m)‖ :=
          norm_add_le _ _
      _ = (‖A z - A z₀‖ + ‖B z‖) * ‖(z - z₀) ^ m‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]; ring
      _ < ‖A z₀‖ * ‖(z - z₀) ^ m‖ := by
          refine mul_lt_mul_of_pos_right ?_ hw; linarith
      _ = _ := (norm_mul _ _).symm
  refine ⟨r', hr', min_le_right _ _, fun z hz hne h0 => ?_, fun ρ hρ => ?_⟩
  · have := hest z hz hne
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  · obtain ⟨hρ0, hρr⟩ := hρ
    set γ : ℝ → ℂ := fun t => z₀ + ccwLoop ρ t with hγ
    have hγb : ∀ t, γ t ∈ ball z₀ r' := fun t => by
      rw [mem_ball, dist_eq_norm, hγ, add_sub_cancel_left, c1w_norm_ccwLoop ρ t hρ0.le]
      exact hρr
    have hγne : ∀ t, γ t ≠ z₀ := fun t h => by
      have := c1w_norm_ccwLoop ρ t hρ0.le
      rw [show ccwLoop ρ t = γ t - z₀ by simp [hγ], h, sub_self, norm_zero] at this
      linarith
    have hγR : ∀ t, γ t ∈ ball z₀ R := fun t => ball_subset_ball (min_le_right _ _) (hγb t)
    have hγc : Continuous γ := continuous_const.add (c1w_ccwLoop_continuous ρ)
    have hFγ : (fun t => F (γ t)) = fun t => (((γ t - z₀) ^ m).re : ℂ) * p (γ t) +
        (((γ t - z₀) ^ m).im : ℂ) * q (γ t) := funext fun t => hF _ (hγR t)
    have hFc : Continuous (fun t => F (γ t)) := by
      rw [hFγ]
      have hpc : Continuous (fun t => p (γ t)) := hp.comp_continuous hγc hγR
      have hqc : Continuous (fun t => q (γ t)) := hq.comp_continuous hγc hγR
      have hw : Continuous (fun t => (γ t - z₀) ^ m) := (hγc.sub continuous_const).pow m
      exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hw)).mul hpc).add
        ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp hw)).mul hqc)
    set L : ℝ → ℂ := fun t => A z₀ * ccwLoop ρ t ^ m with hL
    have hLw : HasLoopWind L m := c1w_hasLoopWind_const_mul_pow _ hA0 ρ hρ0 m
    have hL0 : ∀ t, L t ≠ 0 := hLw.2.2.1
    have hLγ : ∀ t, L t = A z₀ * (γ t - z₀) ^ m := fun t => by simp [hL, hγ]
    set Q : ℝ → ℂ := fun t => F (γ t) / L t with hQ
    have hQre : ∀ t, 0 < (Q t).re := by
      intro t
      have he := hest (γ t) (hγb t) (hγne t)
      rw [← hLγ] at he
      have hd : ‖Q t - 1‖ < 1 := by
        rw [hQ, show F (γ t) / L t - 1 = (F (γ t) - L t) / L t by field_simp [hL0 t],
          norm_div, div_lt_one (norm_pos_iff.2 (hL0 t))]
        exact he
      have := Complex.abs_re_le_norm (Q t - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      have := abs_le.1 this
      linarith [this.1]
    have hQw : HasLoopWind Q 0 := by
      refine hasLoopWind_zero_of_forall_ne_ray Q (hFc.div (continuous_const.mul
        ((c1w_ccwLoop_continuous ρ).pow m)) hL0) ?_ (-1) (by norm_num) ?_
      · intro t
        simp only [hQ, hL, hγ, c1w_ccwLoop_periodic ρ t]
      · intro t s hs h
        have := hQre t
        rw [h] at this
        simp at this
        linarith
    have hprod := hasLoopWind_mul hLw hQw
    rw [add_zero] at hprod
    have heq : (fun t => L t * Q t) = fun t => F (z₀ + ccwLoop ρ t) := funext fun t => by
      simp only [hQ]
      field_simp [hL0 t]
      try rfl
    rw [heq] at hprod
    exact hprod

end FiniteEnergyPlane

namespace FiniteEnergyPlane

/-- A point outside a finite set is at positive distance from it. -/
lemma wpm_sep (P : Finset ℂ) {p : ℂ} (hp : p ∉ P) : ∃ ε > (0 : ℝ), ∀ q ∈ P, ε ≤ dist q p := by
  have hn : (↑P : Set ℂ)ᶜ ∈ 𝓝 p := P.finite_toSet.isClosed.isOpen_compl.mem_nhds hp
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hn
  refine ⟨ε, hε, fun q hq => ?_⟩
  by_contra h
  push_neg at h
  exact hεs (mem_ball.2 h) hq

/-- Circles of radii `a ≤ b` about `p` inside a set where `g` is continuous and nonzero carry the
same winding number of `g`. -/
lemma wpm_annulus (g : ℂ → ℂ) (S : Set ℂ) (hg : ContinuousOn g S) (hg0 : ∀ z ∈ S, g z ≠ 0)
    (p : ℂ) {a b : ℝ} (hab : a ≤ b) (hS : ∀ l ∈ Set.Icc a b, ∀ t, p + ccwLoop l t ∈ S) (k : ℤ) :
    HasLoopWind (fun t => g (p + ccwLoop a t)) k ↔ HasLoopWind (fun t => g (p + ccwLoop b t)) k := by
  set F : ℝ → ℝ → ℂ := fun l t => g (p + ccwLoop l t) with hF
  have hFc : ContinuousOn (fun q : ℝ × ℝ => F q.1 q.2) (Set.Icc a b ×ˢ Set.univ) := by
    refine hg.comp (Continuous.continuousOn ?_) fun q hq => hS q.1 hq.1 q.2
    unfold ccwLoop; fun_prop
  have hper : ∀ l ∈ Set.Icc a b, Function.Periodic (F l) 1 := fun l _ t => by
    simp only [hF, c1w_ccwLoop_periodic l t]
  have h0 : ∀ l ∈ Set.Icc a b, ∀ t, F l t ≠ 0 := fun l hl t => hg0 _ (hS l hl t)
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  constructor
  · intro h
    exact hasLoopWind_of_continuousOn_family F hFc hper h0 h b hb
  · intro h
    have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    obtain ⟨k', hk'⟩ := exists_hasLoopWind (F a)
      (hFc.comp_continuous (continuous_const.prodMk continuous_id) fun t => ⟨ha, Set.mem_univ _⟩)
      (hper a ha) (h0 a ha)
    have := hasLoopWind_of_continuousOn_family F hFc hper h0 hk' b hb
    rwa [hasLoopWind_unique this h] at hk'

theorem windPi_eq_windInf_sub_card_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) :
    ∃ (kinf : ℤ) (kz : ℂ → ℤ) (kπ : ℤ), HasWindInfAt H u cylInf 1 kinf ∧
      (∀ z ∈ Γ, HasWindInfAt H u (cylEndAt z) (-1) (kz z)) ∧ HasWindPi H u Γ kπ ∧
      kπ = kinf - ∑ z ∈ Γ, kz z - 2 + (Γ.card + 1) := by
  classical
  obtain ⟨-, kπ, -, hWP⟩ := exists_hasWindPi_of_nondegenerate H hH J hJ Γ u hu Pinf hinf hΓ hne
  obtain ⟨huc, hu0, hhol, -⟩ := hu
  obtain ⟨Z, hZ, idx, hidx, hsum⟩ := id hWP
  set U : Set ℂ := (↑Γ)ᶜ with hUdef
  have hU : IsOpen U := Γ.finite_toSet.isClosed.isOpen_compl
  have hpc : ContinuousOn (piDs H u) U := continuousOn_piDs H hH U hU u huc hu0
  have hZΓ : ∀ z ∈ Z, z ∉ Γ := fun z hz => ((hZ z).1 hz).1
  set F : Finset ℂ := Z ∪ Γ with hFdef
  have hFne : ∀ z, z ∉ F → z ∈ U ∧ piDs H u z ≠ 0 := by
    intro z hz
    rw [Finset.mem_union, not_or] at hz
    exact ⟨hz.2, fun h0 => hz.1 ((hZ z).2 ⟨hz.2, h0⟩)⟩
  set S : Set ℂ := (↑F : Set ℂ)ᶜ with hSdef
  have hSU : S ⊆ U := fun z hz => (hFne z hz).1
  have hpcS : ContinuousOn (piDs H u) S := hpc.mono hSU
  have hS0 : ∀ z ∈ S, piDs H u z ≠ 0 := fun z hz => (hFne z hz).2
  -- local windings at the punctures
  have hΓw : ∀ p ∈ Γ, ∃ mp : ℤ, ∃ r > (0 : ℝ), ball p r \ {p} ⊆ U ∧
      ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => piDs H u (p + ccwLoop ρ t)) mp := by
    intro p hp
    obtain ⟨ε, hε, hεF⟩ := wpm_sep (F.erase p) (Finset.notMem_erase p F)
    have hcirc : ∀ ρ ∈ Set.Ioo 0 ε, ∀ t, p + ccwLoop ρ t ∈ S := by
      intro ρ hρ t hmem
      have hd : dist (p + ccwLoop ρ t) p = ρ := by
        rw [dist_eq_norm, add_sub_cancel_left, c1w_norm_ccwLoop ρ t hρ.1.le]
      by_cases hq : p + ccwLoop ρ t = p
      · rw [hq, dist_self] at hd; linarith [hρ.1]
      · have := hεF _ (Finset.mem_erase.2 ⟨hq, hmem⟩)
        linarith [hρ.2]
    have hρ0 : ε / 2 ∈ Set.Ioo 0 ε := ⟨half_pos hε, half_lt_self hε⟩
    obtain ⟨mp, hmp⟩ := exists_hasLoopWind (fun t => piDs H u (p + ccwLoop (ε / 2) t))
      (hpcS.comp_continuous (continuous_const.add (c1w_ccwLoop_continuous _)) (hcirc _ hρ0))
      (fun t => by simp only [c1w_ccwLoop_periodic _ t]) fun t => hS0 _ (hcirc _ hρ0 t)
    refine ⟨mp, ε, hε, fun z hz hzΓ => ?_, fun ρ hρ => ?_⟩
    · have hzp : z ≠ p := hz.2
      have := hεF z (Finset.mem_erase.2 ⟨hzp, Finset.mem_union_right _ hzΓ⟩)
      have := mem_ball.1 hz.1
      linarith
    · have hIcc : ∀ a b, a ∈ Set.Ioo 0 ε → b ∈ Set.Ioo 0 ε →
          ∀ l ∈ Set.Icc a b, ∀ t, p + ccwLoop l t ∈ S := fun a b ha hb l hl =>
        hcirc l ⟨lt_of_lt_of_le ha.1 hl.1, lt_of_le_of_lt hl.2 hb.2⟩
      rcases le_total ρ (ε / 2) with hle | hle
      · exact (wpm_annulus _ S hpcS hS0 p hle (hIcc _ _ hρ hρ0) mp).2 hmp
      · exact (wpm_annulus _ S hpcS hS0 p hle (hIcc _ _ hρ0 hρ) mp).1 hmp
  choose! mΓ rΓ hrΓ hΓU hΓwind using hΓw
  set m : ℂ → ℤ := fun p => if p ∈ Γ then mΓ p else idx p with hmdef
  have hmF : ∀ p ∈ F, ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => piDs H u (p + ccwLoop ρ t)) (m p) := by
    intro p hp
    by_cases hpΓ : p ∈ Γ
    · refine ⟨rΓ p, hrΓ p hpΓ, fun ρ hρ => ?_⟩
      simp only [hmdef, if_pos hpΓ]
      exact hΓwind p hpΓ ρ hρ
    · have hpZ : p ∈ Z := by
        rcases Finset.mem_union.1 hp with h | h
        · exact h
        · exact absurd h hpΓ
      obtain ⟨-, r, hr, -, hw⟩ := hidx p hpZ
      refine ⟨r, hr, fun ρ hρ => ?_⟩
      simp only [hmdef, if_neg hpΓ]
      exact hw ρ hρ
  -- the boundary circle
  set R₁ : ℝ := ∑ p ∈ F, ‖p‖ + 1 with hR₁
  have hR₁F : ∀ p ∈ F, ‖p‖ < R₁ := fun p hp => by
    have := Finset.single_le_sum (f := fun p : ℂ => ‖p‖) (fun _ _ => norm_nonneg _) hp
    linarith
  have hR₁0 : 0 < R₁ := by
    have := Finset.sum_nonneg (s := F) (f := fun p : ℂ => ‖p‖) (fun _ _ => norm_nonneg _)
    linarith
  have hbig : ∀ ρ > R₁, HasLoopWind (fun t => piDs H u (ccwLoop ρ t)) (∑ p ∈ F, m p) := by
    intro ρ hρ
    have := hasLoopWind_ccwLoop_eq_sum (piDs H u) F 0 ρ (by linarith)
      (fun p hp => by rw [mem_ball_zero_iff]; linarith [hR₁F p hp])
      (hpcS.mono fun z hz => hz.2) (fun z hz => hS0 z hz.2) m hmF
    simpa using this
  have hinfU : ∀ z : ℂ, R₁ < ‖z‖ → z ∈ U := fun z hz hzΓ => by
    have := hR₁F z (Finset.mem_union_right _ hzΓ)
    linarith
  have hkinf := hasWindInfAt_cylInf_of_hasLoopWind H hH J hJ U hU u huc hu0 hhol R₁ hinfU _ hbig
  have hkz : ∀ z ∈ Γ, HasWindInfAt H u (cylEndAt z) (-1) (mΓ z + 1) := fun z hz =>
    hasWindInfAt_cylEndAt_of_hasLoopWind H hH J hJ U hU u huc hu0 hhol z (rΓ z) (hrΓ z hz)
      (hΓU z hz) (mΓ z) (hΓwind z hz)
  refine ⟨∑ p ∈ F, m p + 1, fun z => mΓ z + 1, kπ, hkinf, hkz, hWP, ?_⟩
  have hdisj : Disjoint Z Γ := Finset.disjoint_left.2 hZΓ
  rw [hFdef, Finset.sum_union hdisj]
  have h1 : ∑ p ∈ Z, m p = ∑ p ∈ Z, idx p :=
    Finset.sum_congr rfl fun p hp => by simp only [hmdef, if_neg (hZΓ p hp)]
  have h2 : ∑ p ∈ Γ, m p = ∑ p ∈ Γ, mΓ p :=
    Finset.sum_congr rfl fun p hp => by simp only [hmdef, if_pos hp]
  have h3 : ∑ z ∈ Γ, (mΓ z + 1) = ∑ z ∈ Γ, mΓ z + Γ.card := by
    rw [Finset.sum_add_distrib]; simp
  rw [h1, h2, h3, hsum]
  ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) :
    ∃ (kinf : ℤ) (kz : ℂ → ℤ) (kπ : ℤ), HasWindInfAt H u cylInf 1 kinf ∧
      (∀ z ∈ Γ, HasWindInfAt H u (cylEndAt z) (-1) (kz z)) ∧ HasWindPi H u Γ kπ ∧
      kπ = kinf - ∑ z ∈ Γ, kz z - 2 + (Γ.card + 1) :=
  windPi_eq_windInf_sub_card_aux H hH J hJ Γ u hu Pinf hinf hΓ hne
