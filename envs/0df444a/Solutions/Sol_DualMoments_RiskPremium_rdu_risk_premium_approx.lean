-- Prove2me | solution 1 for DualMoments.RiskPremium.rdu_risk_premium_approx
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T19:10:28.885407+00:00
-- url     : https://prove2.me/submissions/53e3c27d-893c-4031-934c-7ab9f69896e3

import Mathlib
import Definitions.Def_DualMoments_RiskPremium_Model

set_option autoImplicit false

namespace DMRP2826

open Filter Asymptotics Topology
open DualMoments.RiskPremium

lemma rdu_C (U h : ℝ → ℝ) (p0 δ w0 : ℝ) :
    rduValue U h (lotC p0 δ w0) =
      U (w0 - δ) * (h p0 - h 0) + U (w0 + δ) * (h 1 - h p0) := by
  simp [rduValue, lotC, Lottery.cum, Lottery.cumBefore, Finset.sum_filter, Fin.sum_univ_two]

lemma rdu_D (U h : ℝ → ℝ) (p0 ε δ w0 y : ℝ) :
    rduValue U h (lotD p0 ε δ w0 y) =
      U (w0 - δ) * (h (p0 - ε) - h 0) + U (w0 + y) * (h (p0 + ε) - h (p0 - ε)) +
        U (w0 + δ) * (h 1 - h (p0 + ε)) := by
  simp [rduValue, lotD, Lottery.cum, Lottery.cumBefore, Finset.sum_filter, Fin.sum_univ_three]
  ring_nf

lemma risk12_var (ε δ : ℝ) (hε : ε ≠ 0) :
    (risk12 ε δ).variance / (risk12 ε δ).mass = δ ^ 2 := by
  simp [Lottery.variance, Lottery.mass, Lottery.mean, risk12, Fin.sum_univ_two]
  field_simp

lemma risk12_max (ε δ : ℝ) (hε : ε ≠ 0) :
    (risk12 ε δ).maxiance / (risk12 ε δ).mass = ε * δ := by
  simp [Lottery.maxiance, Lottery.mass, Lottery.mean, risk12, Fin.sum_univ_two,
    Lottery.cum, Lottery.cumBefore, Finset.sum_filter]
  field_simp
  ring

lemma peano2 {f : ℝ → ℝ} {x : ℝ} {s : Set ℝ} (hs : IsOpen s) (hc : Convex ℝ s) (hx : x ∈ s)
    (hd : ∀ y ∈ s, HasDerivAt f (deriv f y) y)
    (hd2 : HasDerivAt (deriv f) (deriv (deriv f) x) x) :
    (fun t => f (x + t) - f x - deriv f x * t - deriv (deriv f) x / 2 * t ^ 2)
      =o[𝓝 0] (fun t => t ^ 2) := by
  have hn : 𝓝[s] x = 𝓝 x := nhdsWithin_eq_nhds.mpr (hs.mem_nhds hx)
  have key := hc.isLittleO_pow_succ_real hx (n := 1)
    (f := fun y => f y - f x - deriv f x * (y - x) - deriv (deriv f) x / 2 * (y - x) ^ 2)
    (f' := fun y => deriv f y - deriv f x - deriv (deriv f) x * (y - x)) ?_ ?_
  · rw [hn] at key
    have ht : Tendsto (fun t : ℝ => x + t) (𝓝 0) (𝓝 x) := by
      have := (continuous_const_add x).tendsto 0
      rwa [add_zero] at this
    have := key.comp_tendsto ht
    refine this.congr' ?_ ?_
    · filter_upwards with t; simp <;> ring
    · filter_upwards with t; simp
  · intro y hy
    have := (((hd y hy).sub_const (f x)).sub (((hasDerivAt_id y).sub_const x).const_mul (deriv f x))).sub
      ((((hasDerivAt_id y).sub_const x).pow 2).const_mul (deriv (deriv f) x / 2))
    convert this.hasDerivWithinAt using 1
    · funext z; simp <;> ring
    · simp <;> ring
  · rw [hn]
    have := hd2.isLittleO
    refine this.congr' ?_ ?_
    · filter_upwards with y; simp [smul_eq_mul]; ring
    · filter_upwards with y; simp


lemma cancel_O {α : Type*} {l : Filter α} {f g ε : α → ℝ} (hε : ∀ᶠ a in l, 0 < ε a)
    (h : (fun a => f a * ε a) =O[l] (fun a => ε a * g a)) : f =O[l] g := by
  rw [isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  filter_upwards [hc, hε] with a h1 h2
  rw [norm_mul, norm_mul, Real.norm_of_nonneg h2.le] at h1
  have : ‖f a‖ * ε a ≤ (c * ‖g a‖) * ε a := by linarith
  exact le_of_mul_le_mul_right this h2

lemma cancel_o {α : Type*} {l : Filter α} {f g ε : α → ℝ} (hε : ∀ᶠ a in l, 0 < ε a)
    (h : (fun a => f a * ε a) =o[l] (fun a => ε a * g a)) : f =o[l] g := by
  rw [isLittleO_iff] at h ⊢
  intro c hc
  filter_upwards [h hc, hε] with a h1 h2
  rw [norm_mul, norm_mul, Real.norm_of_nonneg h2.le] at h1
  have : ‖f a‖ * ε a ≤ (c * ‖g a‖) * ε a := by linarith
  exact le_of_mul_le_mul_right this h2

lemma mulO_of_le {α : Type*} {l : Filter α} {x ε D : α → ℝ} {k : ℝ} (hk : 0 < k)
    (h : ∀ᶠ a in l, 0 < ε a ∧ k * ε a ≤ D a) :
    (fun a => x a * ε a) =O[l] (fun a => x a * D a) := by
  refine IsBigO.of_bound (1 / k) ?_
  filter_upwards [h] with a ⟨h1, h2⟩
  rw [norm_mul, norm_mul, Real.norm_of_nonneg h1.le,
    Real.norm_of_nonneg (by nlinarith : (0:ℝ) ≤ D a)]
  have := mul_le_mul_of_nonneg_left h2 (norm_nonneg (x a))
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hk]
  nlinarith

lemma O_of_le_ev {α : Type*} {l : Filter α} {f g : α → ℝ}
    (h : ∀ᶠ a in l, 0 ≤ f a ∧ f a ≤ g a) : f =O[l] g := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h] with a ⟨h1, h2⟩
  rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg (h1.trans h2)]
  linarith

lemma core {α : Type*} {l : Filter α} (ε δ lam rp rm q hp hn : α → ℝ) (u1 u2 h1 h2 : ℝ)
    (hu1 : 0 < u1) (hh1 : 0 < h1)
    (tε : Tendsto ε l (𝓝 0))
    (pos : ∀ᶠ a in l, 0 < ε a ∧ 0 < δ a)
    (hrp : rp =o[l] fun a => δ a ^ 2) (hrm : rm =o[l] fun a => δ a ^ 2)
    (hq : q =o[l] lam) (hhp : hp =o[l] fun a => ε a ^ 2) (hhn : hn =o[l] fun a => ε a ^ 2)
    (heq : ∀ᶠ a in l,
      (-u1 * δ a + u2 / 2 * δ a ^ 2 + rm a) * (h1 * ε a - h2 / 2 * ε a ^ 2 - hn a) +
        (u1 * δ a + u2 / 2 * δ a ^ 2 + rp a) * (h1 * ε a + h2 / 2 * ε a ^ 2 + hp a) =
        (-u1 * lam a + q a) * (2 * h1 * ε a + (hp a - hn a))) :
    (fun a => lam a - (δ a ^ 2 / 2 * (-u2 / u1) + ε a * δ a / 2 * (-h2 / h1)))
      =o[l] fun a => δ a ^ 2 + ε a * δ a := by
  set g : α → ℝ := fun a => δ a ^ 2 + ε a * δ a with hg
  set W : α → ℝ := fun a => ε a * g a with hW
  set D : α → ℝ := fun a => 2 * h1 * ε a + (hp a - hn a) with hD
  have hεpos : ∀ᶠ a in l, 0 < ε a := pos.mono fun a h => h.1
  have hεsq : (fun a => ε a ^ 2) =o[l] ε := (isLittleO_pow_id one_lt_two).comp_tendsto tε
  have hK : (fun a => hp a - hn a) =o[l] ε := (hhp.sub hhn).trans hεsq
  have hDlow : ∀ᶠ a in l, 0 < ε a ∧ h1 * ε a ≤ D a := by
    filter_upwards [hK.bound hh1, hεpos] with a h1' h2'
    rw [Real.norm_of_nonneg h2'.le, Real.norm_eq_abs] at h1'
    refine ⟨h2', ?_⟩
    simp only [hD]
    have := neg_abs_le (hp a - hn a)
    nlinarith
  have hεO : (fun a => ε a) =O[l] ε := isBigO_refl _ _
  have hDO : D =O[l] ε := by
    have h1' : (fun a => 2 * h1 * ε a) =O[l] ε := hεO.const_mul_left _
    exact h1'.add hK.isBigO
  -- elementary monomial bounds
  have m1 : (fun a => δ a * ε a ^ 2) =O[l] W := by
    apply O_of_le_ev
    filter_upwards [pos] with a ⟨h1', h2'⟩
    simp only [hW, hg]
    constructor
    · positivity
    · nlinarith [mul_pos h1' h2', mul_pos (mul_pos h1' h2') h2']
  have m2 : (fun a => δ a ^ 2 * ε a) =O[l] W := by
    apply O_of_le_ev
    filter_upwards [pos] with a ⟨h1', h2'⟩
    simp only [hW, hg]
    constructor
    · positivity
    · nlinarith [mul_pos h1' h2', mul_pos (mul_pos h1' h2') h1']
  have gε : (fun a => g a * ε a) =O[l] W :=
    isBigO_of_le _ (fun a => by simp only [hW]; rw [mul_comm])
  have hδ2 : (fun a => δ a ^ 2) =O[l] g := by
    apply O_of_le_ev
    filter_upwards [pos] with a ⟨h1', h2'⟩
    simp only [hg]
    constructor
    · positivity
    · nlinarith [mul_pos h1' h2']
  have hεδ : (fun a => ε a * δ a) =O[l] g := by
    apply O_of_le_ev
    filter_upwards [pos] with a ⟨h1', h2'⟩
    simp only [hg]
    constructor
    · positivity
    · nlinarith [mul_pos h1' h2']
  -- the factors F1, F2 are O(ε)
  have hε2O : (fun a => ε a ^ 2) =O[l] ε := hεsq.isBigO
  have hF1 : (fun a => h1 * ε a - h2 / 2 * ε a ^ 2 - hn a) =O[l] ε :=
    ((hεO.const_mul_left h1).sub (hε2O.const_mul_left _)).sub (hhn.trans hεsq).isBigO
  have hF2 : (fun a => h1 * ε a + h2 / 2 * ε a ^ 2 + hp a) =O[l] ε :=
    ((hεO.const_mul_left h1).add (hε2O.const_mul_left _)).add (hhp.trans hεsq).isBigO
  -- the remainder
  set Rest : α → ℝ := fun a => u1 * (δ a * (hp a + hn a)) + u2 / 2 * (δ a ^ 2 * (hp a - hn a)) +
      rm a * (h1 * ε a - h2 / 2 * ε a ^ 2 - hn a) + rp a * (h1 * ε a + h2 / 2 * ε a ^ 2 + hp a)
    with hRest
  have hR : Rest =o[l] W := by
    have r1 : (fun a => δ a * (hp a + hn a)) =o[l] W :=
      ((isBigO_refl δ l).mul_isLittleO (hhp.add hhn)).trans_isBigO m1
    have r2 : (fun a => δ a ^ 2 * (hp a - hn a)) =o[l] W :=
      ((isBigO_refl (fun a => δ a ^ 2) l).mul_isLittleO hK).trans_isBigO m2
    have r3 : (fun a => rm a * (h1 * ε a - h2 / 2 * ε a ^ 2 - hn a)) =o[l] W :=
      (hrm.mul_isBigO hF1).trans_isBigO m2
    have r4 : (fun a => rp a * (h1 * ε a + h2 / 2 * ε a ^ 2 + hp a)) =o[l] W :=
      (hrp.mul_isBigO hF2).trans_isBigO m2
    exact ((r1.const_mul_left u1).add (r2.const_mul_left _)).add r3 |>.add r4
  -- step B: lam = O(g)
  have hLHS : (fun a => (u1 * lam a - q a) * D a) =O[l] W := by
    have hm : (fun a => -(u1 * h2 * (δ a * ε a ^ 2) + u2 * h1 * (δ a ^ 2 * ε a) + Rest a))
        =O[l] W :=
      (((m1.const_mul_left (u1 * h2)).add (m2.const_mul_left (u2 * h1))).add hR.isBigO).neg_left
    refine hm.congr' ?_ EventuallyEq.rfl
    filter_upwards [heq] with a ha
    simp only [hRest, hD]
    linear_combination (-1 : ℝ) * ha
  have hq1 : q =o[l] fun a => u1 * lam a := hq.trans_isBigO (isBigO_self_const_mul hu1.ne' lam l)
  have hlamO : lam =O[l] fun a => u1 * lam a - q a :=
    (isBigO_self_const_mul hu1.ne' lam l).trans hq1.right_isBigO_sub
  have hlD : (fun a => lam a * D a) =O[l] W :=
    (hlamO.mul (isBigO_refl D l)).trans hLHS
  have hlε : (fun a => lam a * ε a) =O[l] W := (mulO_of_le hh1 hDlow).trans hlD
  have hlamg : lam =O[l] g := cancel_O hεpos hlε
  have hqg : q =o[l] g := hq.trans_isBigO hlamg
  -- step C
  set T : α → ℝ := fun a => δ a ^ 2 / 2 * (-u2 / u1) + ε a * δ a / 2 * (-h2 / h1) with hT
  have hTg : T =O[l] g := by
    have := (hδ2.const_mul_left (1 / 2 * (-u2 / u1))).add (hεδ.const_mul_left (1 / 2 * (-h2 / h1)))
    refine this.congr' ?_ EventuallyEq.rfl
    filter_upwards with a
    simp only [hT]; ring
  have hEDu : (fun a => (lam a - T a) * (D a * u1)) =o[l] W := by
    have t1 : (fun a => q a * D a) =o[l] W := (hqg.mul_isBigO hDO).trans_isBigO gε
    have t2 : (fun a => T a * (hp a - hn a)) =o[l] W := (hTg.mul_isLittleO hK).trans_isBigO gε
    have := (t1.sub hR).sub (t2.const_mul_left u1)
    refine this.congr' ?_ EventuallyEq.rfl
    filter_upwards [heq] with a ha
    simp only [hRest, hD, hT]
    linear_combination (norm := skip) (-1 : ℝ) * ha
    field_simp
    ring
  have hEε : (fun a => (lam a - T a) * ε a) =o[l] W := by
    refine ((mulO_of_le (D := fun a => D a * u1) (k := h1 * u1) (by positivity) ?_).trans_isLittleO hEDu)
    filter_upwards [hDlow] with a ⟨h1', h2'⟩
    refine ⟨h1', ?_⟩
    nlinarith
  exact cancel_o hεpos hEε

end DMRP2826

open DualMoments.RiskPremium Filter Asymptotics Topology in
theorem solution (U h : ℝ → ℝ) (hU : UtilityStanding U)
    (hh : WeightingStanding h) (p0 w0 : ℝ) (hp0 : 0 < p0 ∧ p0 < 1) (lam : ℝ → ℝ → ℝ)
    (hlam : ∀ ε₁ ε₂, Feasible p0 ε₁ → 0 < ε₂ → IsRDUPremium U h p0 w0 ε₁ ε₂ (lam ε₁ ε₂)) :
    (fun e : ℝ × ℝ => lam e.1 e.2 -
        ((risk12 e.1 e.2).variance / (2 * (risk12 e.1 e.2).mass) *
            (-(deriv (deriv U) w0) / deriv U w0) +
          (risk12 e.1 e.2).maxiance / (2 * (risk12 e.1 e.2).mass) *
            (-(deriv (deriv h) p0) / deriv h p0)))
      =o[𝓝[Set.Ioi 0 ×ˢ Set.Ioi 0] ((0 : ℝ), (0 : ℝ))]
    (fun e : ℝ × ℝ => (risk12 e.1 e.2).variance / (risk12 e.1 e.2).mass +
        (risk12 e.1 e.2).maxiance / (risk12 e.1 e.2).mass) := by
  obtain ⟨hUc, hUpos⟩ := hU
  obtain ⟨hhc, -, h0, h1v, hhpos⟩ := hh
  set l := 𝓝[Set.Ioi 0 ×ˢ Set.Ioi 0] ((0 : ℝ), (0 : ℝ)) with hl
  have hUd : ∀ y ∈ (Set.univ : Set ℝ), HasDerivAt U (deriv U y) y := fun y _ =>
    ((hUc.differentiable (by norm_num)) y).hasDerivAt
  have hUc' : ContDiff ℝ (1 + 1) U := by simpa [one_add_one_eq_two] using hUc
  have hU1 : ContDiff ℝ 1 (deriv U) := hUc'.deriv'
  have hUd2 : HasDerivAt (deriv U) (deriv (deriv U) w0) w0 :=
    ((hU1.differentiable one_ne_zero) w0).hasDerivAt
  have hhIoo : ContDiffOn ℝ (1 + 1) h (Set.Ioo 0 1) := by
    simpa [one_add_one_eq_two] using hhc.mono Set.Ioo_subset_Icc_self
  obtain ⟨hdiff, -, hd1⟩ := (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mp hhIoo
  have hp0m : p0 ∈ Set.Ioo (0:ℝ) 1 := hp0
  have hhd : ∀ y ∈ Set.Ioo (0:ℝ) 1, HasDerivAt h (deriv h y) y := fun y hy =>
    (hdiff.differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  have hhd2 : HasDerivAt (deriv h) (deriv (deriv h) p0) p0 :=
    ((hd1.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hp0m)).hasDerivAt
  have hh1pos : 0 < deriv h p0 := by
    have := hhpos p0 ⟨hp0.1.le, hp0.2.le⟩
    rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hp0.1 hp0.2)] at this
  have PU := DMRP2826.peano2 isOpen_univ convex_univ (Set.mem_univ w0) hUd hUd2
  have Ph := DMRP2826.peano2 isOpen_Ioo (convex_Ioo 0 1) hp0m hhd hhd2
  have t1 : Tendsto (fun e : ℝ × ℝ => e.1) l (𝓝 0) :=
    (continuous_fst.tendsto ((0:ℝ), (0:ℝ))).mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun e : ℝ × ℝ => e.2) l (𝓝 0) :=
    (continuous_snd.tendsto ((0:ℝ), (0:ℝ))).mono_left nhdsWithin_le_nhds
  have tn1 : Tendsto (fun e : ℝ × ℝ => -e.1) l (𝓝 0) := by simpa using t1.neg
  have tn2 : Tendsto (fun e : ℝ × ℝ => -e.2) l (𝓝 0) := by simpa using t2.neg
  have pos : ∀ᶠ e in l, 0 < e.1 ∧ 0 < e.2 := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact he
  have small : ∀ᶠ e in l, e.1 < min p0 (1 - p0) :=
    t1 (Iio_mem_nhds (lt_min hp0.1 (by linarith [hp0.2])))
  have hprem : ∀ᶠ e in l, IsRDUPremium U h p0 w0 e.1 e.2 (lam e.1 e.2) := by
    filter_upwards [pos, small] with e he hs
    exact hlam _ _ ⟨hp0.1, hp0.2, he.1, hs⟩ he.2
  have tl : Tendsto (fun e : ℝ × ℝ => lam e.1 e.2) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tn2 t2 ?_ ?_
    · filter_upwards [hprem] with e he
      linarith [he.2.1]
    · filter_upwards [hprem] with e he
      linarith [he.1]
  have tw : Tendsto (fun e : ℝ × ℝ => w0 - lam e.1 e.2) l (𝓝 w0) := by
    simpa using (tendsto_const_nhds (x := w0)).sub tl
  have hrp : (fun e : ℝ × ℝ => U (w0 + e.2) - U w0 - deriv U w0 * e.2 -
      deriv (deriv U) w0 / 2 * e.2 ^ 2) =o[l] (fun e => e.2 ^ 2) := PU.comp_tendsto t2
  have hrm : (fun e : ℝ × ℝ => U (w0 - e.2) - U w0 + deriv U w0 * e.2 -
      deriv (deriv U) w0 / 2 * e.2 ^ 2) =o[l] (fun e => e.2 ^ 2) := by
    refine (PU.comp_tendsto tn2).congr' ?_ ?_
    · filter_upwards with e
      simp only [Function.comp_apply, ← sub_eq_add_neg, neg_sq]
      ring
    · filter_upwards with e
      simp only [Function.comp_apply, neg_sq]
  have hhp : (fun e : ℝ × ℝ => h (p0 + e.1) - h p0 - deriv h p0 * e.1 -
      deriv (deriv h) p0 / 2 * e.1 ^ 2) =o[l] (fun e => e.1 ^ 2) := Ph.comp_tendsto t1
  have hhn : (fun e : ℝ × ℝ => h (p0 - e.1) - h p0 + deriv h p0 * e.1 -
      deriv (deriv h) p0 / 2 * e.1 ^ 2) =o[l] (fun e => e.1 ^ 2) := by
    refine (Ph.comp_tendsto tn1).congr' ?_ ?_
    · filter_upwards with e
      simp only [Function.comp_apply, ← sub_eq_add_neg, neg_sq]
      ring
    · filter_upwards with e
      simp only [Function.comp_apply, neg_sq]
  have hq : (fun e : ℝ × ℝ => U (w0 - lam e.1 e.2) - U w0 + deriv U w0 * lam e.1 e.2)
      =o[l] (fun e => lam e.1 e.2) := by
    have h1 := (hUd w0 (Set.mem_univ _)).isLittleO.comp_tendsto tw
    rw [← isLittleO_neg_right]
    refine h1.congr' ?_ ?_
    · filter_upwards with e
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    · filter_upwards with e
      simp only [Function.comp_apply]
      ring
  have key := DMRP2826.core (fun e : ℝ × ℝ => e.1) (fun e => e.2) (fun e => lam e.1 e.2) _ _ _ _ _
    (deriv U w0) (deriv (deriv U) w0) (deriv h p0) (deriv (deriv h) p0) (hUpos w0) hh1pos
    t1 pos hrp hrm hq hhp hhn ?_
  · refine key.congr' ?_ ?_
    · filter_upwards [pos] with e he
      have hne : e.1 ≠ 0 := he.1.ne'
      rw [div_mul_eq_div_div_swap, DMRP2826.risk12_var _ _ hne,
        div_mul_eq_div_div_swap, DMRP2826.risk12_max _ _ hne]
    · filter_upwards [pos] with e he
      have hne : e.1 ≠ 0 := he.1.ne'
      rw [DMRP2826.risk12_var _ _ hne, DMRP2826.risk12_max _ _ hne]
  · filter_upwards [hprem] with e he
    have eq := he.2.2
    rw [DMRP2826.rdu_C, DMRP2826.rdu_D, h0] at eq
    simp only [← sub_eq_add_neg] at eq
    linear_combination eq
