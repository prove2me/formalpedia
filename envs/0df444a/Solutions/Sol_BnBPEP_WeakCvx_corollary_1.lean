-- Prove2me | solution 1 for BnBPEP.WeakCvx.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T11:43:07.878793+00:00
-- url     : https://prove2.me/submissions/c7d6f6f0-16e1-4609-a5d9-d77b193eb6b8

/-
SPDX-License-Identifier: Apache-2.0
Standalone proof of the full weakly convex subgradient-rate Corollary 1.
Mathematical source: Das Gupta, Van Parys, and Ryu, Mathematical Programming
204 (2024), Section 6.3, pp. 614–627, https://doi.org/10.1007/s10107-023-01973-1.
All four native definitions and the actual real-inf envelope/gradient are unchanged.
The new proof derives proximal strong growth and the actual gradient by a quadratic
remainder sandwich, then uses direct proximal descent and backward geometric weights.
The small-segment minimizer argument adapts our own earlier elementary AdaGrad proof.
No accepted third-party implementation is copied; all modules are independently authored.
-/
import Mathlib
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_BnBPEP_WeakCvx_IsWeakSubgrad
import Definitions.Def_BnBPEP_WeakCvx_InWeakClass
import Definitions.Def_BnBPEP_WeakCvx_moreauEnv

-- BEGIN Foundation
open scoped BigOperators
open Filter Set

namespace WeakCvxRateProof
end WeakCvxRateProof
-- END Foundation

-- BEGIN ProxGap
open BnBPEP.WeakCvx
open Set

namespace WeakCvxRateProof
variable {d : ℕ}

lemma norm_segment_sq (y z : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖(1-t) • y + t • z‖^2 = (1-t)*‖y‖^2+t*‖z‖^2-t*(1-t)*‖z-y‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, RCLike.conj_to_real]
  rw [real_inner_comm z y]
  ring

lemma norm_segment_sub_sq (y z x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖(1-t) • y+t • z-x‖^2 =
      (1-t)*‖y-x‖^2+t*‖z-x‖^2-t*(1-t)*‖z-y‖^2 := by
  have he : (1-t) • y+t • z-x = (1-t) • (y-x)+t • (z-x) := by module
  rw [he, norm_segment_sq]
  have hz : (z-x)-(y-x)=z-y := by abel
  rw [hz]

lemma prox_strong_gap {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1/2 * ‖z‖^2))
    {x y : EuclideanSpace ℝ (Fin d)} (hp : SAGA.Convex.IsProxPoint f (1/2) x y)
    (z : EuclideanSpace ℝ (Fin d)) :
    f y + ‖y-x‖^2 + 1/2*‖z-y‖^2 ≤ f z + ‖z-x‖^2 := by
  have hm (u : EuclideanSpace ℝ (Fin d)) : f y+‖y-x‖^2 ≤ f u+‖u-x‖^2 := by
    simpa using hp u
  let B : ℝ := 1/2*‖z-y‖^2
  let D : ℝ := (f z+‖z-x‖^2)-(f y+‖y-x‖^2)
  have hD : 0 ≤ D := sub_nonneg.mpr (hm z)
  suffices B ≤ D by dsimp [B,D] at this; linarith
  by_contra hn
  have hDB : D < B := lt_of_not_ge hn
  have hBp : 0 < B := lt_of_le_of_lt hD hDB
  let t := (B-D)/(2*B)
  have ht : 0 < t := div_pos (sub_pos.mpr hDB) (by positivity)
  have htB : t*(2*B)=B-D := div_mul_cancel₀ _ (ne_of_gt (by positivity : 0<2*B))
  have ht1 : t < 1 := by nlinarith
  have hc := hf.2 (Set.mem_univ y) (Set.mem_univ z)
    (show 0 ≤ 1-t by linarith) ht.le (by ring : (1-t)+t=1)
  simp only [smul_eq_mul] at hc
  rw [norm_segment_sq] at hc
  have hl := hm ((1-t) • y+t • z)
  rw [norm_segment_sub_sq] at hl
  have hi : (1-t)*B ≤ D := by dsimp [B,D]; nlinarith
  nlinarith

lemma prox_weak_subgrad {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1/2 * ‖z‖^2))
    {x y : EuclideanSpace ℝ (Fin d)} (hp : SAGA.Convex.IsProxPoint f (1/2) x y) :
    IsWeakSubgrad 1 f y ((2 : ℝ) • (x-y)) := by
  intro z
  have hg := prox_strong_gap hf hp z
  have he : z-x = (z-y)-(x-y) := by abel
  rw [norm_sub_rev y x, he, norm_sub_sq_real (z-y) (x-y)] at hg
  change f y + inner ℝ ((2 : ℝ) • (x-y)) (z-y) - (1 : ℝ)/2*‖z-y‖^2 ≤ f z
  rw [inner_smul_left]
  simp only [RCLike.conj_to_real]
  rw [real_inner_comm (x-y) (z-y)] at hg
  linarith

end WeakCvxRateProof
-- END ProxGap

-- BEGIN EnvelopeGradient
open BnBPEP.WeakCvx
open Filter Set

namespace WeakCvxRateProof
variable {d : ℕ}

lemma prox_objective_shift (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x y z v : EuclideanSpace ℝ (Fin d)) :
    f z+‖z-(x+v)‖^2 = f z+‖z-x‖^2+
      2*inner ℝ (x-y) v+‖v‖^2-2*inner ℝ (z-y) v := by
  have he : z-(x+v)=(z-x)-v := by abel
  rw [he, norm_sub_sq_real]
  simp only [inner_sub_left]
  ring

lemma prox_perturbed_lower {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1/2 * ‖z‖^2))
    {x y : EuclideanSpace ℝ (Fin d)} (hp : SAGA.Convex.IsProxPoint f (1/2) x y)
    (v z : EuclideanSpace ℝ (Fin d)) :
    f y+‖y-x‖^2+inner ℝ ((2 : ℝ) • (x-y)) v-‖v‖^2 ≤ f z+‖z-(x+v)‖^2 := by
  have hg := prox_strong_gap hf hp z
  have hs := sq_nonneg ‖(z-y)-(2 : ℝ) • v‖
  rw [norm_sub_sq_real] at hs
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hs
  rw [prox_objective_shift f x y z v]
  simp only [inner_smul_left, RCLike.conj_to_real]
  nlinarith

lemma envelope_sandwich {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1/2 * ‖z‖^2))
    {x y : EuclideanSpace ℝ (Fin d)} (hp : SAGA.Convex.IsProxPoint f (1/2) x y)
    (v : EuclideanSpace ℝ (Fin d)) :
    f y+‖y-x‖^2+inner ℝ ((2 : ℝ) • (x-y)) v-‖v‖^2 ≤ moreauEnv 2 f (x+v) ∧
    moreauEnv 2 f (x+v) ≤ f y+‖y-x‖^2+inner ℝ ((2 : ℝ) • (x-y)) v+‖v‖^2 := by
  have hl := prox_perturbed_lower hf hp v
  have hb : BddBelow (Set.range (fun z => f z+‖z-(x+v)‖^2)) :=
    ⟨_, by rintro _ ⟨z,rfl⟩; exact hl z⟩
  have hi : moreauEnv 2 f (x+v) = ⨅ z, f z+‖z-(x+v)‖^2 := by
    simp [moreauEnv]
  rw [hi]
  refine ⟨le_ciInf hl, ?_⟩
  have hu := ciInf_le hb y
  have he := prox_objective_shift f x y y v
  simp only [sub_self, inner_zero_left, mul_zero, sub_zero] at he
  simp only [inner_smul_left, RCLike.conj_to_real]
  linarith

lemma envelope_eq_prox {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1/2 * ‖z‖^2))
    {x y : EuclideanSpace ℝ (Fin d)} (hp : SAGA.Convex.IsProxPoint f (1/2) x y) :
    moreauEnv 2 f x = f y+‖y-x‖^2 := by
  have hs := envelope_sandwich hf hp 0
  simp only [add_zero, inner_zero_right, norm_zero, zero_pow (by omega : 2 ≠ 0), sub_zero] at hs
  exact le_antisymm hs.2 hs.1

lemma envelope_hasGradient {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1/2 * ‖z‖^2))
    {x y : EuclideanSpace ℝ (Fin d)} (hp : SAGA.Convex.IsProxPoint f (1/2) x y) :
    HasGradientAt (moreauEnv 2 f) ((2 : ℝ) • (x-y)) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) hc] with v hv
  have hvn : ‖v‖ < c := by simpa [Metric.mem_ball, dist_zero_right] using hv
  have hs := envelope_sandwich hf hp v
  rw [envelope_eq_prox hf hp]
  rw [Real.norm_eq_abs]
  have hb : |moreauEnv 2 f (x+v) - (f y+‖y-x‖^2) - inner ℝ ((2 : ℝ) • (x-y)) v| ≤ ‖v‖^2 :=
    abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact hb.trans (by nlinarith [norm_nonneg v])

lemma envelope_gradient {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1/2 * ‖z‖^2))
    {x y : EuclideanSpace ℝ (Fin d)} (hp : SAGA.Convex.IsProxPoint f (1/2) x y) :
    gradient (moreauEnv 2 f) x = (2 : ℝ) • (x-y) :=
  (envelope_hasGradient hf hp).gradient

end WeakCvxRateProof
-- END EnvelopeGradient

-- BEGIN Potential
namespace WeakCvxRateProof

open BnBPEP.WeakCvx
open scoped BigOperators

variable {d : ℕ}

noncomputable def proxEnergy (f : EuclideanSpace ℝ (Fin d) → ℝ) (fstar : ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ := f y - fstar + ‖x - y‖ ^ 2

lemma weak_subgrad_inner (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1 / 2 * ‖z‖ ^ 2))
    (x y g : EuclideanSpace ℝ (Fin d))
    (hp : SAGA.Convex.IsProxPoint f (1 / 2) x y) (hg : IsWeakSubgrad 1 f x g) :
    ‖x - y‖ ^ 2 ≤ inner ℝ g (x - y) := by
  have hyx := prox_weak_subgrad hf hp x
  have hxy := hg y
  have he : y - x = -(x - y) := by abel
  rw [he, inner_neg_right, norm_neg] at hxy
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq] at hyx
  norm_num at hyx hxy
  linarith

lemma energy_descent (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1 / 2 * ‖z‖ ^ 2))
    (fstar h : ℝ) (hh : 0 ≤ h) (x y g y' : EuclideanSpace ℝ (Fin d))
    (hp : SAGA.Convex.IsProxPoint f (1 / 2) x y) (hg : IsWeakSubgrad 1 f x g)
    (hp' : SAGA.Convex.IsProxPoint f (1 / 2) (x - h • g) y') :
    proxEnergy f fstar (x - h • g) y' ≤ proxEnergy f fstar x y -
      2 * h * ‖x - y‖ ^ 2 + h ^ 2 * ‖g‖ ^ 2 := by
  have hi := weak_subgrad_inner f hf x y g hp hg
  have hm := hp' y
  norm_num at hm
  rw [norm_sub_rev y' (x - h • g), norm_sub_rev y (x - h • g)] at hm
  have he : x - h • g - y = (x - y) - h • g := by abel
  rw [he, norm_sub_sq_real (x - y) (h • g), inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm] at hm
  unfold proxEnergy
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * h by positivity)]

lemma potential_step (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ (fun z => f z + 1 / 2 * ‖z‖ ^ 2))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ z, f xstar ≤ f z)
    (h B b : ℝ) (hh : 0 ≤ h) (hB : 0 ≤ B) (hcap : h * B ≤ 2)
    (hb : b = 4 + (1 - 2 * h) * B) (x y g y' : EuclideanSpace ℝ (Fin d))
    (hp : SAGA.Convex.IsProxPoint f (1 / 2) x y) (hg : IsWeakSubgrad 1 f x g)
    (hp' : SAGA.Convex.IsProxPoint f (1 / 2) (x - h • g) y') :
    4 * ‖x - y‖ ^ 2 + B * proxEnergy f (f xstar) (x - h • g) y' -
      b * proxEnergy f (f xstar) x y ≤ B * h ^ 2 * ‖g‖ ^ 2 := by
  have hd := mul_le_mul_of_nonneg_left (energy_descent f hf (f xstar) h hh x y g y' hp hg hp') hB
  have hn := mul_nonpos_of_nonpos_of_nonneg (show 2 * h * B - 4 ≤ 0 by linarith)
    (sub_nonneg.mpr (hxstar y))
  rw [hb]
  unfold proxEnergy at *
  nlinarith

lemma sum_potential_steps (a v : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (a k + v (k + 1) - v k)) =
      (∑ k ∈ Finset.range n, a k) + v n - v 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, ih]; ring

lemma run_budget (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : InWeakClass 1 L f) (xstar : EuclideanSpace ℝ (Fin d))
    (hxstar : ∀ z, f xstar ≤ f z) (R h : ℝ) (hh : 0 ≤ h)
    (n : ℕ) (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) (hbn : b n = 0)
    (hcap : ∀ k < n, h * b (k + 1) ≤ 2)
    (hrec : ∀ k < n, b k = 4 + (1 - 2 * h) * b (k + 1))
    (x g y : ℕ → EuclideanSpace ℝ (Fin d))
    (hg : ∀ k < n, IsWeakSubgrad 1 f (x k) (g k))
    (hstep : ∀ k < n, x (k + 1) = x k - h • g k)
    (hy : ∀ k ≤ n, SAGA.Convex.IsProxPoint f (1 / 2) (x k) (y k))
    (hinit : proxEnergy f (f xstar) (x 0) (y 0) ≤ R ^ 2) :
    (∑ k ∈ Finset.range n, 4 * ‖x k - y k‖ ^ 2) ≤
      L ^ 2 * h ^ 2 * (∑ k ∈ Finset.range n, b (k + 1)) + b 0 * R ^ 2 := by
  have hs : ∀ k ∈ Finset.range n,
      4 * ‖x k - y k‖ ^ 2 + b (k + 1) * proxEnergy f (f xstar) (x (k + 1)) (y (k + 1)) -
        b k * proxEnergy f (f xstar) (x k) (y k) ≤ L ^ 2 * h ^ 2 * b (k + 1) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hpn := hy (k + 1) (by omega)
    rw [hstep k hk'] at hpn
    have hp := potential_step f hf.1 xstar hxstar h (b (k + 1)) (b k) hh (hb _)
      (hcap k hk') (hrec k hk') (x k) (y k) (g k) (y (k + 1)) (hy k (by omega)) (hg k hk') hpn
    rw [← hstep k hk'] at hp
    have hnorm : ‖g k‖ ^ 2 ≤ L ^ 2 := sq_le_sq₀ (norm_nonneg _) hL |>.mpr (hf.2 _ _ (hg k hk'))
    have hm := mul_le_mul_of_nonneg_left hnorm
      (mul_nonneg (hb (k + 1)) (sq_nonneg h))
    nlinarith
  have hsum := Finset.sum_le_sum hs
  rw [sum_potential_steps (fun k => 4 * ‖x k - y k‖ ^ 2)
    (fun k => b k * proxEnergy f (f xstar) (x k) (y k)) n,
    hbn, zero_mul, add_zero] at hsum
  simp only [← Finset.mul_sum] at hsum ⊢
  have hi := mul_le_mul_of_nonneg_left hinit (hb 0)
  linarith

end WeakCvxRateProof
-- END Potential

-- BEGIN Weights
namespace WeakCvxRateProof

open scoped BigOperators

noncomputable def backwardWeight (h : ℝ) (n k : ℕ) : ℝ :=
  (2 / h) * (1 - (1 - 2 * h) ^ (n - k))

lemma backwardWeight_terminal (h : ℝ) (n : ℕ) : backwardWeight h n n = 0 := by
  simp [backwardWeight]

lemma backwardWeight_nonneg (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (n k : ℕ) : 0 ≤ backwardWeight h n k := by
  have hr : 0 ≤ 1 - 2 * h := by linarith
  have hp : (1 - 2 * h) ^ (n - k) ≤ 1 := pow_le_one₀ hr (by linarith)
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hp)

lemma backwardWeight_cap (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (n k : ℕ) : h * backwardWeight h n k ≤ 2 := by
  have hp : 0 ≤ (1 - 2 * h) ^ (n - k) := pow_nonneg (by linarith) _
  have hp' : 0 ≤ (1 - h * 2) ^ (n - k) := by simpa only [mul_comm] using hp
  unfold backwardWeight
  field_simp
  nlinarith

lemma backwardWeight_recurrence (h : ℝ) (hh : 0 < h) (n k : ℕ) (hk : k < n) :
    backwardWeight h n k = 4 + (1 - 2 * h) * backwardWeight h n (k + 1) := by
  have he : n - k = n - (k + 1) + 1 := by omega
  unfold backwardWeight
  rw [he, pow_succ]
  field_simp
  ring

lemma sum_sub_succ (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (a k - a (k + 1))) = a 0 - a n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

lemma backwardWeight_sum (h : ℝ) (hh : 0 < h) (n : ℕ) :
    h ^ 2 * (∑ k ∈ Finset.range n, backwardWeight h n (k + 1)) =
      2 * h * n - h * backwardWeight h n 0 / 2 := by
  have he : ∀ k ∈ Finset.range n,
      backwardWeight h n k - backwardWeight h n (k + 1) =
        4 - (2 * h) * backwardWeight h n (k + 1) := by
    intro k hk
    rw [backwardWeight_recurrence h hh n k (Finset.mem_range.mp hk)]
    ring
  have hs := Finset.sum_congr rfl he
  rw [sum_sub_succ, backwardWeight_terminal] at hs
  simp only [sub_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum] at hs
  nlinarith [congrArg (fun z : ℝ => h * z) hs]

lemma decay_power_bound (h : ℝ) (_hh : 0 < h) (hh' : h ≤ 1 / 2) (n : ℕ) :
    (1 - 2 * h) ^ n * (1 + 2 * h * n) ≤ 1 := by
  have hr : 0 ≤ 1 - 2 * h := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : (1 - 2 * h) * (1 + 2 * h * ((n : ℝ) + 1)) ≤
        1 + 2 * h * n := by
      nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ (n : ℝ) + 1 by positivity)]
    calc
      _ = (1 - 2 * h) ^ n * ((1 - 2 * h) * (1 + 2 * h * ((n : ℝ) + 1))) := by
        rw [pow_succ, Nat.cast_add_one]; ring
      _ ≤ (1 - 2 * h) ^ n * (1 + 2 * h * n) :=
        mul_le_mul_of_nonneg_left ha (pow_nonneg hr n)
      _ ≤ 1 := ih

lemma decay_power_le_inverse (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (n : ℕ) (hn : 0 < n) : (1 - 2 * h) ^ n ≤ 1 / (2 * h * n) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ (by positivity : 0 < 2 * h * n)).mpr
  have hp : 0 ≤ (1 - 2 * h) ^ n := pow_nonneg (by linarith) _
  nlinarith [decay_power_bound h hh hh' n]

lemma prescribed_step_pos (L R : ℝ) (n : ℕ) (hn : 0 < n) :
    0 < Real.sqrt (4 * (R / L) ^ 2 * n + 1) / (2 * n) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < 4 * (R / L) ^ 2 * n + 1 := by positivity
  exact div_pos (Real.sqrt_pos.mpr hs) (by positivity)

lemma scalar_budget (L R h : ℝ) (hL : 0 < L) (n : ℕ) (hn : 0 < n)
    (hhdef : h = Real.sqrt (4 * (R / L) ^ 2 * n + 1) / (2 * n))
    (hh' : h ≤ 1 / 2) :
    L ^ 2 * h ^ 2 * (∑ k ∈ Finset.range n, backwardWeight h n (k + 1)) +
      backwardWeight h n 0 * R ^ 2 ≤
      L ^ 2 * (2 * Real.sqrt (4 * (R / L) ^ 2 * n + 1) - 1) := by
  have hh : 0 < h := by rw [hhdef]; exact prescribed_step_pos L R n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 ≤ (1 - 2 * h) ^ n := pow_nonneg (by linarith) _
  have hb := decay_power_le_inverse h hh hh' n hn
  have hsum := backwardWeight_sum h hh n
  have he : L ^ 2 * h ^ 2 * (∑ k ∈ Finset.range n, backwardWeight h n (k + 1)) +
      backwardWeight h n 0 * R ^ 2 =
      L ^ 2 * (-1 + (1 - 2 * h) ^ n + 2 * h * n) +
        (2 * R ^ 2 / h) * (1 - (1 - 2 * h) ^ n) := by
    rw [mul_assoc, hsum]
    simp only [backwardWeight, Nat.sub_zero]
    field_simp
    ring
  have hu : L ^ 2 * (-1 + (1 - 2 * h) ^ n + 2 * h * n) +
      (2 * R ^ 2 / h) * (1 - (1 - 2 * h) ^ n) ≤
      L ^ 2 * (-1 + 1 / (2 * h * n) + 2 * h * n) + 2 * R ^ 2 / h := by
    have h1 := mul_le_mul_of_nonneg_left hb (sq_nonneg L)
    have h2 := mul_nonneg (show 0 ≤ 2 * R ^ 2 / h by positivity) hp
    nlinarith
  rw [he]
  refine hu.trans_eq ?_
  have hspos : 0 < Real.sqrt (4 * (R / L) ^ 2 * n + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 4 * (R / L) ^ 2 * n + 1 by positivity)
  rw [hhdef]
  field_simp
  field_simp at hs
  nlinarith

end WeakCvxRateProof
-- END Weights

-- BEGIN NativeRoot
namespace BnBPEP.WeakCvx

/-- Corollary 1, p. 625: in the setup of Theorem 1 (which requires `h ∈ (0, 1/2]`), the stepsize
`h = √(4κ²(N+1) + 1) / (2(N+1))` with `κ = R/L` yields
`(1/(N+1)) Σ_{i=0}^N ‖∇f_{(1/2)}(x_i)‖² ≤ L² (2√(4κ²(N+1) + 1) - 1)/(N+1)`.
Here `L` is the paper's `L̃` (subgradient bound after normalizing `ρ = 1`). -/
theorem corollary_1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hL : 0 < L) (hf : InWeakClass 1 L f)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ z, f xstar ≤ f z)
    (R : ℝ) (hR : 0 < R) (N : ℕ) (h : ℝ)
    (hhdef : h = √(4 * (R / L) ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1)))
    (hh : h ≤ 1 / 2)
    (x g y : ℕ → EuclideanSpace ℝ (Fin d))
    (hg : ∀ k ≤ N, IsWeakSubgrad 1 f (x k) (g k))
    (hstep : ∀ k ≤ N, x (k + 1) = x k - h • g k)
    (hy : ∀ k ≤ N + 1, SAGA.Convex.IsProxPoint f (1 / 2) (x k) (y k))
    (hinit : f (y 0) - f xstar + ‖x 0 - y 0‖ ^ 2 ≤ R ^ 2) :
    1 / ((N : ℝ) + 1) * ∑ i ∈ Finset.range (N + 1), ‖gradient (moreauEnv 2 f) (x i)‖ ^ 2
      ≤ L ^ 2 * (2 * √(4 * (R / L) ^ 2 * ((N : ℝ) + 1) + 1) - 1) / ((N : ℝ) + 1) := by
  have _ := hR
  have hn : 0 < N + 1 := by omega
  have hhdef' : h = Real.sqrt (4 * (R / L) ^ 2 * (N + 1 : ℕ) + 1) / (2 * (N + 1 : ℕ)) := by
    simpa only [Nat.cast_add_one] using hhdef
  have hhpos : 0 < h := by
    rw [hhdef']
    exact WeakCvxRateProof.prescribed_step_pos L R (N + 1) hn
  have hb := WeakCvxRateProof.run_budget f L hL.le hf xstar hxstar R h hhpos.le (N + 1)
    (WeakCvxRateProof.backwardWeight h (N + 1))
    (WeakCvxRateProof.backwardWeight_nonneg h hhpos hh (N + 1))
    (WeakCvxRateProof.backwardWeight_terminal h (N + 1))
    (fun k _ => WeakCvxRateProof.backwardWeight_cap h hhpos hh (N + 1) (k + 1))
    (fun k hk => WeakCvxRateProof.backwardWeight_recurrence h hhpos (N + 1) k hk)
    x g y (fun k hk => hg k (by omega)) (fun k hk => hstep k (by omega)) hy hinit
  have hs := WeakCvxRateProof.scalar_budget L R h hL (N + 1) hn hhdef' hh
  have he : (∑ i ∈ Finset.range (N + 1), ‖gradient (moreauEnv 2 f) (x i)‖ ^ 2) =
      ∑ i ∈ Finset.range (N + 1), 4 * ‖x i - y i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [WeakCvxRateProof.envelope_gradient hf.1 (hy i (by simpa using (Finset.mem_range.mp hi).le))]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_pow]
    ring
  rw [he]
  have hbound := hb.trans hs
  have hnpos : 0 < (N : ℝ) + 1 := by positivity
  have hc := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 1 / ((N : ℝ) + 1) by positivity)
  simpa only [Nat.cast_add_one, div_eq_mul_inv, one_mul, mul_comm] using hc

end BnBPEP.WeakCvx
-- END NativeRoot

open BnBPEP.WeakCvx

theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hL : 0 < L) (hf : InWeakClass 1 L f)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ z, f xstar ≤ f z)
    (R : ℝ) (hR : 0 < R) (N : ℕ) (h : ℝ)
    (hhdef : h = √(4 * (R / L) ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1)))
    (hh : h ≤ 1 / 2)
    (x g y : ℕ → EuclideanSpace ℝ (Fin d))
    (hg : ∀ k ≤ N, IsWeakSubgrad 1 f (x k) (g k))
    (hstep : ∀ k ≤ N, x (k + 1) = x k - h • g k)
    (hy : ∀ k ≤ N + 1, SAGA.Convex.IsProxPoint f (1 / 2) (x k) (y k))
    (hinit : f (y 0) - f xstar + ‖x 0 - y 0‖ ^ 2 ≤ R ^ 2) :
    1 / ((N : ℝ) + 1) * ∑ i ∈ Finset.range (N + 1), ‖gradient (moreauEnv 2 f) (x i)‖ ^ 2
      ≤ L ^ 2 * (2 * √(4 * (R / L) ^ 2 * ((N : ℝ) + 1) + 1) - 1) / ((N : ℝ) + 1) :=
  BnBPEP.WeakCvx.corollary_1 f L hL hf xstar hxstar R hR N h hhdef hh x g y hg hstep hy hinit
