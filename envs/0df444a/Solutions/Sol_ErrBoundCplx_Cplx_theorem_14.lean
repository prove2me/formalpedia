-- Prove2me | solution 1 for ErrBoundCplx.Cplx.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T04:18:26.038725+00:00
-- url     : https://prove2.me/submissions/5668f3e4-af6a-47be-a9b4-149e321a8789

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology

section
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology
open scoped InnerProductSpace
namespace ErrBoundCplx.Cplx.KLFresh
end ErrBoundCplx.Cplx.KLFresh
end

section
open Filter Topology
namespace ErrBoundCplx.Cplx.KLFresh

theorem strong_limit_of_summable_steps {H : Type*} [NormedAddCommGroup H]
    [CompleteSpace H] (x : ℕ → H)
    (hs : Summable (fun n => ‖x (n + 1) - x n‖)) :
    ∃ z, Tendsto x atTop (𝓝 z) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_summable_dist
  simpa only [dist_eq_norm, norm_sub_rev] using hs

theorem limit_distance_bound {H : Type*} [NormedAddCommGroup H]
    {x : ℕ → H} {z : H} (hz : Tendsto x atTop (𝓝 z))
    (B : ℕ → ℝ) (hB : ∀ k ≥ 1, ∀ n ≥ k, ‖x k - x n‖ ≤ B k) :
    ∀ k ≥ 1, ‖x k - z‖ ≤ B k := by
  intro k hk
  apply le_of_tendsto ((tendsto_const_nhds.sub hz).norm)
  filter_upwards [eventually_ge_atTop k] with n hn
  exact hB k hk n hn

theorem value_tendsto_zero {H : Type*} [NormedAddCommGroup H]
    {x : ℕ → H} {z : H} (hz : Tendsto x atTop (𝓝 z))
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (b : ℝ) (w : H)
    (hs : Summable (fun n => ‖x (n + 1) - x n‖))
    (hbound : ∀ n, r (n + 1) ≤ b * ‖x (n + 1) - x n‖ * ‖x (n + 1) - w‖) :
    Tendsto r atTop (𝓝 0) := by
  have hx : Tendsto (fun n => x (n + 1)) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat 1).2 hz
  have hupper : Tendsto (fun n => b * ‖x (n + 1) - x n‖ * ‖x (n + 1) - w‖)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hs.tendsto_atTop_zero).mul
      ((hx.sub tendsto_const_nhds).norm)
  exact (tendsto_add_atTop_iff_nat 1).1
    (squeeze_zero (fun n => hr (n + 1)) hbound hupper)

theorem lsc_limit_minimum {H : Type*} [TopologicalSpace H]
    {f : H → EReal} (hf : LowerSemicontinuous f) (hnonneg : ∀ y, 0 ≤ f y)
    {x : ℕ → H} {z : H} (hx : Tendsto x atTop (𝓝 z))
    (hv : Tendsto (fun n => f (x n)) atTop (𝓝 0)) : f z = 0 := by
  apply le_antisymm _ (hnonneg z)
  by_contra h
  have hpos : (0 : EReal) < f z := lt_of_not_ge h
  obtain ⟨a, ha, haz⟩ := exists_between hpos
  have he : ∀ᶠ n in atTop, a ≤ f (x n) :=
    (hx.eventually ((hf z) a haz)).mono fun _ h => h.le
  exact (not_le_of_gt ha) (ge_of_tendsto hv he)

end ErrBoundCplx.Cplx.KLFresh
end

section
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology
open scoped InnerProductSpace
namespace ErrBoundCplx.Cplx.KLFresh
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f : H → EReal} {a b : ℝ} {x : ℕ → H}

theorem values_antitone (ha : 0 < a) (hx : IsSubgradDescentSeq f a b x) :
    Antitone (fun k => f (x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := hx.2.1 (k+1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  have hnon : (0 : EReal) ≤ ((a * ‖x (k+1)-x k‖^2 : ℝ) : EReal) := by
    exact_mod_cast mul_nonneg ha.le (sq_nonneg _)
  exact (le_add_of_nonneg_right hnon).trans h

theorem value_finite (hmin : IsMinZero f) (ha : 0 < a)
    (hx : IsSubgradDescentSeq f a b x) (k : ℕ) : f (x k) ≠ ⊤ ∧ f (x k) ≠ ⊥ := by
  constructor
  · exact ne_top_of_le_ne_top hx.1 (values_antitone ha hx (Nat.zero_le k))
  · exact ne_bot_of_le_ne_bot (by simp) (hmin.1 (x k))

theorem value_coe (hmin : IsMinZero f) (ha : 0 < a)
    (hx : IsSubgradDescentSeq f a b x) (k : ℕ) : ((f (x k)).toReal : EReal) = f (x k) :=
  EReal.coe_toReal (value_finite hmin ha hx k).1 (value_finite hmin ha hx k).2

theorem value_nonneg (hmin : IsMinZero f) (ha : 0 < a)
    (hx : IsSubgradDescentSeq f a b x) (k : ℕ) : 0 ≤ (f (x k)).toReal := by
  have h := hmin.1 (x k)
  rw [← value_coe hmin ha hx k] at h
  exact_mod_cast h

theorem value_le_initial (hmin : IsMinZero f) (ha : 0 < a)
    (hx : IsSubgradDescentSeq f a b x) {r0 : ℝ} (hx0 : f (x 0) ≤ (r0 : EReal))
    (k : ℕ) : (f (x k)).toReal ≤ r0 := by
  have h := (values_antitone ha hx (Nat.zero_le k)).trans hx0
  change f (x k) ≤ (r0 : EReal) at h
  rw [← value_coe hmin ha hx k] at h
  exact_mod_cast h

theorem value_decrease (hmin : IsMinZero f) (ha : 0 < a)
    (hx : IsSubgradDescentSeq f a b x) (k : ℕ) (hk : 1 ≤ k) :
    (f (x k)).toReal + a * ‖x k-x (k-1)‖^2 ≤ (f (x (k-1))).toReal := by
  have h := hx.2.1 k hk
  rw [← value_coe hmin ha hx k, ← value_coe hmin ha hx (k-1), ← EReal.coe_add] at h
  exact_mod_cast h

theorem step_sqrt_bound (hmin : IsMinZero f) (ha : 0 < a)
    (hx : IsSubgradDescentSeq f a b x) (k : ℕ) (hk : 1 ≤ k) :
    ‖x k-x (k-1)‖ ≤ Real.sqrt ((f (x (k-1))).toReal / a) := by
  apply (Real.le_sqrt (norm_nonneg _) (div_nonneg (value_nonneg hmin ha hx _) ha.le)).2
  apply (le_div_iff₀ ha).2
  have h := value_decrease hmin ha hx k hk
  have hn := value_nonneg hmin ha hx k
  nlinarith
end ErrBoundCplx.Cplx.KLFresh
end

section
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology
open scoped InnerProductSpace
namespace ErrBoundCplx.Cplx.KLFresh
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f : H → EReal} {a b : ℝ} {x : ℕ → H}

theorem value_le_step_distance (hmin : IsMinZero f) (ha : 0 < a) (_hb : 0 < b)
    (hx : IsSubgradDescentSeq f a b x) (z : H) (hz : f z = 0) (k : ℕ) (hk : 1 ≤ k) :
    (f (x k)).toReal ≤ b * ‖x k-x (k-1)‖ * ‖x k-z‖ := by
  obtain ⟨v, hv, hvbound⟩ := hx.2.2 k hk
  have h := hv.2.2 z
  rw [hz, ← value_coe hmin ha hx k, ← EReal.coe_add] at h
  have hreal : (f (x k)).toReal + ⟪z-x k,v⟫_ℝ ≤ 0 := by exact_mod_cast h
  have hi := abs_real_inner_le_norm (z-x k) v
  have hn : ‖z-x k‖ = ‖x k-z‖ := norm_sub_rev _ _
  have hm := mul_le_mul_of_nonneg_left hvbound (norm_nonneg (x k-z))
  rw [hn] at hi
  have habs := neg_le_abs (⟪z-x k,v⟫_ℝ)
  nlinarith
end ErrBoundCplx.Cplx.KLFresh
end

section
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology
namespace ErrBoundCplx.Cplx.KLFresh

theorem native_limit_minimizer {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → EReal} {a b : ℝ} {x : ℕ → H}
    (hf : GammaZero f) (hmin : IsMinZero f) (ha : 0 < a) (hb : 0 < b)
    (hx : IsSubgradDescentSeq f a b x)
    (hs : Summable (fun n => ‖x (n + 1) - x n‖))
    {z : H} (hz : Tendsto x atTop (𝓝 z)) : f z = 0 := by
  obtain ⟨w, hw⟩ := hmin.2
  have hr : Tendsto (fun n => (f (x n)).toReal) atTop (𝓝 0) := by
    apply value_tendsto_zero hz (fun n => (f (x n)).toReal)
      (fun n => value_nonneg hmin ha hx n) b w hs
    intro n
    simpa only [Nat.add_sub_cancel] using
      value_le_step_distance hmin ha hb hx w hw (n + 1) (by omega)
  have he : Tendsto (fun n => ((f (x n)).toReal : EReal)) atTop (𝓝 0) := by
    simpa only [EReal.coe_zero] using (EReal.tendsto_coe.mpr hr)
  simp only [value_coe hmin ha hx] at he
  exact lsc_limit_minimum hf.2.2.2 hmin.1 hz he

end ErrBoundCplx.Cplx.KLFresh
end

section
open NonconvexSplitting.ADMMKL
namespace ErrBoundCplx.Cplx.KLFresh

theorem concave_difference {rbar : ℝ} {φ : ℝ → ℝ} (hφ : IsDesingularizer rbar φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 < t) (htr : t < rbar) :
    deriv φ t * (t-s) ≤ φ t-φ s := by
  rcases eq_or_lt_of_le hst with rfl | hst
  · simp
  have hd : DifferentiableAt ℝ φ t :=
    (hφ.2.2.2.2.1.differentiableOn (by norm_num) t ⟨ht,htr⟩).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨ht,htr⟩)
  have h := hφ.2.1.deriv_le_slope ⟨hs,hst.trans htr⟩ ⟨ht.le,htr⟩ hst hd
  rw [slope_def_field] at h
  exact (le_div_iff₀ (sub_pos.mpr hst)).1 h
end ErrBoundCplx.Cplx.KLFresh
end

section
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
namespace ErrBoundCplx.Cplx.KLFresh
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f : H → EReal} {a b rbar r0 : ℝ} {x : ℕ → H} {φ : ℝ → ℝ}

theorem value_phi_nonneg (hmin : IsMinZero f) (ha : 0 < a)
    (hx : IsSubgradDescentSeq f a b x) (hx0 : f (x 0) ≤ (r0 : EReal))
    (hr0 : r0 < rbar) (hφ : IsDesingularizer rbar φ) (k : ℕ) :
    0 ≤ φ (f (x k)).toReal :=
  hφ.2.2.1 _ ⟨value_nonneg hmin ha hx k, (value_le_initial hmin ha hx hx0 k).trans_lt hr0⟩

theorem native_recurrence (hmin : IsMinZero f) (ha : 0 < a) (hb : 0 < b)
    (hx : IsSubgradDescentSeq f a b x) (hx0 : f (x 0) ≤ (r0 : EReal))
    (hr0 : r0 < rbar) (hφ : IsDesingularizer rbar φ) (hKL : KLOnBand f rbar φ)
    (k : ℕ) (hk : 1 ≤ k) :
    2 * ‖x (k+1)-x k‖ ≤ ‖x k-x (k-1)‖ +
      (b/a) * (φ (f (x k)).toReal - φ (f (x (k+1))).toReal) := by
  let r := (f (x k)).toReal
  let rn := (f (x (k+1))).toReal
  let s := ‖x (k+1)-x k‖
  let t := ‖x k-x (k-1)‖
  have hr : 0 ≤ r := value_nonneg hmin ha hx k
  have hrn : 0 ≤ rn := value_nonneg hmin ha hx (k+1)
  have hdec : rn + a*s^2 ≤ r := by
    simpa only [Nat.add_sub_cancel] using value_decrease hmin ha hx (k+1) (by omega)
  have hrnr : rn ≤ r := by nlinarith [sq_nonneg s]
  change 2*s ≤ t+(b/a)*(φ r-φ rn)
  by_cases hz : r=0
  · have hs2 : s^2 ≤ 0 := (mul_le_mul_iff_right₀ ha).mp (by nlinarith : a*s^2 ≤ a*0)
    have hs : s=0 := by nlinarith [sq_nonneg s]
    have hrnz : rn=0 := by linarith
    rw [hz,hrnz,sub_self,mul_zero,add_zero,hs,mul_zero]
    exact norm_nonneg _
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have hrr : r < rbar := (value_le_initial hmin ha hx hx0 k).trans_lt hr0
  have hdpos : 0 < deriv φ r := hφ.2.2.2.2.2 _ ⟨hrpos,hrr⟩
  obtain ⟨v,hv,hvb⟩ := hx.2.2 k hk
  have hkl : 1 ≤ deriv φ r * ‖v‖ := by
    apply hKL (x k) _ _ v hv
    · rw [← value_coe hmin ha hx k]
      exact_mod_cast hrpos
    · rw [← value_coe hmin ha hx k]
      exact_mod_cast hrr
  have hbt : 1 ≤ deriv φ r * (b*t) :=
    hkl.trans (mul_le_mul_of_nonneg_left hvb hdpos.le)
  have ht : 0 < t := by
    have ht0 : 0 ≤ t := norm_nonneg _
    by_contra hn
    have htzero : t=0 := le_antisymm (not_lt.mp hn) ht0
    simp only [htzero,mul_zero] at hbt
    linarith
  have hconc := concave_difference hφ hrn hrnr hrpos hrr
  have hmul := mul_le_mul_of_nonneg_right hbt (sub_nonneg.mpr hrnr)
  have hcmul := mul_le_mul_of_nonneg_left hconc (mul_nonneg hb.le ht.le)
  have hquad : a*s^2 ≤ b*t*(φ r-φ rn) := by nlinarith
  have hlin : a*(2*s-t) ≤ b*(φ r-φ rn) := by
    apply (mul_le_mul_iff_left₀ ht).mp
    nlinarith [mul_nonneg ha.le (sq_nonneg (s-t))]
  have hdiv : 2*s-t ≤ b/a*(φ r-φ rn) := by
    apply (le_of_mul_le_mul_left (a := a) _ ha)
    calc
      a*(2*s-t) ≤ b*(φ r-φ rn) := hlin
      _ = a*(b/a*(φ r-φ rn)) := by field_simp
  linarith
end ErrBoundCplx.Cplx.KLFresh
end

section

open scoped BigOperators
namespace ErrBoundCplx.Cplx.KLFresh

lemma finite_length_telescope (d ψ : ℕ → ℝ) (C : ℝ)
    (hstep : ∀ k ≥ 1, 2*d k ≤ d (k-1)+C*(ψ k-ψ (k+1)))
    (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    (∑ j ∈ Finset.range m, d (k+j)) + d (k+m-1) ≤
      d (k-1)+C*(ψ k-ψ (k+m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    change (∑ j ∈ Finset.range m, d (k+j)) + d (k+m) + d (k+m) ≤
      d (k-1)+C*(ψ k-ψ (k+m+1))
    have h := hstep (k+m) (by omega)
    nlinarith

lemma finite_length_partial_tail (d ψ : ℕ → ℝ) (C : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hψ : ∀ k, 0 ≤ ψ k) (hC : 0 ≤ C)
    (hstep : ∀ k ≥ 1, 2*d k ≤ d (k-1)+C*(ψ k-ψ (k+1)))
    (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    (∑ j ∈ Finset.range m, d (k+j)) ≤ d (k-1)+C*ψ k := by
  have h := finite_length_telescope d ψ C hstep k hk m
  nlinarith [hd (k+m-1), mul_nonneg hC (hψ (k+m))]

lemma finite_length_summable (d ψ : ℕ → ℝ) (C : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hψ : ∀ k, 0 ≤ ψ k) (hC : 0 ≤ C)
    (hstep : ∀ k ≥ 1, 2*d k ≤ d (k-1)+C*(ψ k-ψ (k+1))) : Summable d := by
  have hs : Summable (fun j : ℕ => d (j+1)) := by
    apply summable_of_sum_range_le (fun j => hd (j+1))
    intro m
    simpa only [Nat.add_comm, Nat.sub_self] using
      finite_length_partial_tail d ψ C hd hψ hC hstep 1 (by omega) m
  exact (summable_nat_add_iff 1).mp hs

lemma finite_length_tail (d ψ : ℕ → ℝ) (C : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hψ : ∀ k, 0 ≤ ψ k) (hC : 0 ≤ C)
    (hstep : ∀ k ≥ 1, 2*d k ≤ d (k-1)+C*(ψ k-ψ (k+1)))
    (k : ℕ) (hk : 1 ≤ k) :
    (∑' j : ℕ, d (k+j)) ≤ d (k-1)+C*ψ k := by
  apply Real.tsum_le_of_sum_range_le (fun j => hd (k+j))
  exact fun m => finite_length_partial_tail d ψ C hd hψ hC hstep k hk m

end ErrBoundCplx.Cplx.KLFresh
end

section
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology
open scoped BigOperators
namespace ErrBoundCplx.Cplx.KLFresh

theorem native_theorem_14 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (rbar : ℝ) (φ : ℝ → ℝ) (hφ : IsDesingularizer rbar φ) (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (r0 : ℝ) (hx0 : f (x 0) ≤ (r0 : EReal)) (hr0 : r0 < rbar) :
    ∃ xstar : H, f xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ k ≥ 1, ‖x k - xstar‖
        ≤ b / a * φ (f (x k)).toReal + Real.sqrt ((f (x (k - 1))).toReal / a) := by
  let d : ℕ → ℝ := fun n => ‖x (n + 1) - x n‖
  let ψ : ℕ → ℝ := fun n => φ (f (x n)).toReal
  have hd : ∀ n, 0 ≤ d n := fun n => norm_nonneg _
  have hψ : ∀ n, 0 ≤ ψ n := value_phi_nonneg hmin ha hx hx0 hr0 hφ
  have hC : 0 ≤ b / a := div_nonneg hb.le ha.le
  have hstep : ∀ k ≥ 1, 2 * d k ≤ d (k - 1) + (b / a) * (ψ k - ψ (k + 1)) := by
    intro k hk
    have he : k - 1 + 1 = k := by omega
    simpa only [d, ψ, he] using native_recurrence hmin ha hb hx hx0 hr0 hφ hKL k hk
  have hs : Summable d := finite_length_summable d ψ (b / a) hd hψ hC hstep
  obtain ⟨z, hz⟩ := strong_limit_of_summable_steps x hs
  refine ⟨z, native_limit_minimizer hf hmin ha hb hx hs hz, hz, ?_⟩
  intro k hk
  have hdist : ‖x k - z‖ ≤ ∑' j : ℕ, d (k + j) := by
    simpa only [dist_eq_norm] using
      dist_le_tsum_of_dist_le_of_tendsto d
        (fun n => by
          rw [dist_eq_norm]
          change ‖x n - x (n + 1)‖ ≤ ‖x (n + 1) - x n‖
          exact le_of_eq (norm_sub_rev _ _))
        hs hz k
  have htail := finite_length_tail d ψ (b / a) hd hψ hC hstep k hk
  have he : k - 1 + 1 = k := by omega
  have hsqrt : d (k - 1) ≤ Real.sqrt ((f (x (k - 1))).toReal / a) := by
    simpa only [d, he] using step_sqrt_bound hmin ha hx k hk
  change ‖x k - z‖ ≤ (b / a) * ψ k + Real.sqrt ((f (x (k - 1))).toReal / a)
  linarith

end ErrBoundCplx.Cplx.KLFresh
end

open ErrBoundCplx.Cplx

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (rbar : ℝ) (φ : ℝ → ℝ) (hφ : IsDesingularizer rbar φ) (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (r0 : ℝ) (hx0 : f (x 0) ≤ (r0 : EReal)) (hr0 : r0 < rbar) :
    ∃ xstar : H, f xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ k ≥ 1, ‖x k - xstar‖
        ≤ b / a * φ (f (x k)).toReal + Real.sqrt ((f (x (k - 1))).toReal / a) := by
  exact KLFresh.native_theorem_14 f hf hmin rbar φ hφ hKL a b ha hb x hx r0 hx0 hr0
