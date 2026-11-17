-- Prove2me | solution 1 for BranchSpectral.critical_kernel_pos_expanded
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:37:33.868855+00:00
-- url     : https://prove2.me/submissions/68b41fbc-3ee5-40c9-8e11-eb0d4e312ea5

import Mathlib
noncomputable section
namespace BranchFull

def smallRatio (t : ℝ) : ℝ :=
  ((t⁻¹)^2 + t⁻¹) * Real.exp (-t⁻¹ + (10000 + 1/4)*t)
def largeRatio (t : ℝ) : ℝ :=
  (1000000 + t⁻¹) * Real.exp (-(1000000 - 10000 - 1/4)*t)

theorem exp_neg_quartic (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 24 / y^4 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 4
  norm_num at h
  rw [Real.exp_neg]
  rw [← one_div (Real.exp y)]
  apply (div_le_div_iff₀ (Real.exp_pos y) (pow_pos hy 4)).2
  nlinarith

theorem small_ratio_y (y : ℝ) (hy : 10000 ≤ y) :
    (y^2+y) * Real.exp (-y+(10000+1/4)/y) < 1/2 := by
  have hp : 0 < y := by linarith
  have he : -y+(10000+1/4)/y ≤ -(y/2) := by
    have hd : (10000+1/4)/y ≤ y/2 := by
      apply (div_le_iff₀ hp).2
      nlinarith
    linarith
  have hb := Real.exp_le_exp.mpr he
  have hq := exp_neg_quartic (y/2) (by positivity)
  have hm : (y^2+y)*Real.exp (-y+(10000+1/4)/y) ≤
      (y^2+y)*(24/(y/2)^4) :=
    mul_le_mul_of_nonneg_left (hb.trans hq) (by positivity)
  have hid : (y^2+y)*(24/(y/2)^4) = 384*(1/y^2+1/y^3) := by
    field_simp
    <;> ring
  rw [hid] at hm
  have h2 : (1:ℝ)/y^2 ≤ 1/10000^2 := by gcongr
  have h3 : (1:ℝ)/y^3 ≤ 1/10000^3 := by gcongr
  linarith

theorem small_ratio_lt_half (t : ℝ) (ht : 0 < t) (hc : t ≤ 1/10000) :
    smallRatio t < 1/2 := by
  have hi : (10000:ℝ) ≤ t⁻¹ := by
    rw [← one_div t]
    apply (le_div_iff₀ ht).2
    linarith
  have h := small_ratio_y (t⁻¹) hi
  simpa [smallRatio, div_eq_mul_inv] using h

theorem large_ratio_lt_half (t : ℝ) (ht : 1/10000 ≤ t) :
    largeRatio t < 1/2 := by
  have hp : 0 < t := by linarith
  have hi : t⁻¹ ≤ (10000:ℝ) := by
    rw [← one_div t]
    apply (div_le_iff₀ hp).2
    linarith
  have he : -(1000000-10000-1/4)*t ≤ (-98:ℝ) := by linarith
  have hExp := (Real.exp_le_exp.mpr he).trans (exp_neg_quartic 98 (by norm_num))
  have hm : largeRatio t ≤ 1010000*(24/98^4) := by
    unfold largeRatio
    exact mul_le_mul (by linarith) hExp (Real.exp_pos _).le (by norm_num)
  norm_num at hm ⊢
  linarith

theorem heat_lower_bound (K : ℝ → ℝ)
    (hs : ∀ t > 0, t ≤ 1/10000 →
      Real.exp (-10000*t)*(1-smallRatio t) ≤ K t)
    (hl : ∀ t > 0, 1/10000 ≤ t →
      Real.exp (-10000*t)*(1-largeRatio t) ≤ K t) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < K t := by
  intro t ht
  have hp := Real.exp_pos (-10000*t)
  by_cases h : t ≤ 1/10000
  · have hr := small_ratio_lt_half t ht h
    have hk := hs t ht h
    nlinarith
  · have hr := large_ratio_lt_half t (le_of_lt (lt_of_not_ge h))
    have hk := hl t ht (le_of_lt (lt_of_not_ge h))
    nlinarith
end BranchFull

open MeasureTheory Set
noncomputable section
namespace QnAudit

def weight (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (n - 1) * Real.exp (-x * t)

def moment (K : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), weight x n t * K t

def oldQ (K : ℝ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * u ^ (2 * n - 1) * moment K (u ^ 2) n

def newQ (K : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (Nat.factorial (n - 1) : ℝ) * moment K x n

theorem weight_pos (x : ℝ) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < weight x n t := by
  exact mul_pos (pow_pos ht _) (Real.exp_pos _)

theorem positive_integral_Ioi (f : ℝ → ℝ)
    (hf : ∀ t > 0, 0 < f t)
    (hi : IntegrableOn f (Ioi 0)) :
    0 < ∫ t in Ioi (0 : ℝ), f t := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact le_of_lt (hf t ht)
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg hi).2
  have hsub : Ioc (0 : ℝ) 1 ⊆ Function.support f := by
    intro t ht
    exact ne_of_gt (hf t ht.1)
  have hmeasure : (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 1) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    have hinter : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 :=
      inter_eq_left.mpr (fun _ ht => ht.1)
    rw [hinter, Real.volume_Ioc]
    norm_num
  calc
    0 < (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 1) := by rw [hmeasure]; norm_num
    _ ≤ (volume.restrict (Ioi (0 : ℝ))) (Function.support f) := measure_mono hsub

theorem moment_pos (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < moment K x n := by
  exact positive_integral_Ioi _ (fun t ht => mul_pos (weight_pos x n t ht) (hK t ht)) hi

theorem oldQ_pos (K : ℝ → ℝ) (u : ℝ) (n : ℕ)
    (hu : 0 < u) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    0 < oldQ K u n := by
  exact mul_pos (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) (pow_pos hu _))
    (moment_pos K (u ^ 2) n hK hi)

theorem newQ_pos (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < newQ K x n := by
  have hfac : (0 : ℝ) < (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  exact mul_pos (div_pos (pow_pos hx _) hfac) (moment_pos K x n hK hi)

theorem positive_head_controls_signed_tail (H N E r : ℝ)
    (hH : 0 < H) (hN : 0 ≤ N) (hr : r < 1) (hE : |E| ≤ r * H) :
    0 < H + N + E := by
  have he := neg_abs_le E
  have hm : r * H < H := by nlinarith
  linarith

theorem heat_pos_from_two_regimes (K H N E r : ℝ → ℝ) (t0 : ℝ)
    (hsplit : ∀ t > 0, K t = H t + N t + E t)
    (hH : ∀ t > 0, 0 < H t) (hN : ∀ t > 0, 0 ≤ N t)
    (hE : ∀ t > 0, |E t| ≤ r t * H t)
    (hsmall : ∀ t > 0, t ≤ t0 → r t < 1)
    (hlarge : ∀ t > 0, t0 < t → r t < 1) :
    ∀ t > 0, 0 < K t := by
  intro t ht
  rw [hsplit t ht]
  apply positive_head_controls_signed_tail _ _ _ _ (hH t ht) (hN t ht)
  · by_cases h : t ≤ t0
    · exact hsmall t ht h
    · exact hlarge t ht (lt_of_not_ge h)
  · exact hE t ht

theorem ordinary_Q_positive_from_heat_representation
    (Q : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hrep : ∀ n ≥ 1, ∀ u > 0, Q n u = oldQ K u n)
    (hK : ∀ t > 0, 0 < K t)
    (hint : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    ∀ n ≥ 1, ∀ u > 0, 0 < Q n u := by
  intro n hn u hu
  rw [hrep n hn u hu]
  exact oldQ_pos K u n hu hK (hint n hn u hu)

end QnAudit

namespace BranchSpectral
open Set

def atom (g e t : ℝ) := Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)
def gaussian (g t : ℝ) := Real.exp (-g^2*t)
def kernel (g e : ℕ → ℝ) (t : ℝ) := ∑' j, atom (g j) (e j) t

theorem atom_abs_bound (g e t : ℝ) (he : |e| ≤ 1/2) (ht : 0 < t) :
    |atom g e t| ≤ Real.exp (t/4)*gaussian g t := by
  have he2 : e^2 ≤ 1/4 := by
    obtain ⟨h1,h2⟩ := abs_le.mp he
    nlinarith
  unfold atom gaussian
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(g^2-e^2)*t)*1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (t/4)*Real.exp (-g^2*t) := by
      rw [mul_one, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

theorem kernel_summable (g e : ℕ → ℝ) (t : ℝ)
    (he : ∀ j, |e j| ≤ 1/2) (ht : 0 < t)
    (hg : Summable (fun j => gaussian (g j) t)) :
    Summable (fun j => atom (g j) (e j) t) := by
  apply (hg.mul_left (Real.exp (t/4))).of_norm_bounded
  intro j
  simpa only [Real.norm_eq_abs] using atom_abs_bound (g j) (e j) t (he j) ht

theorem atom_near_nonneg (g e t : ℝ) (hg : 0 < g)
    (he : |e| ≤ 1/2) (ht : 0 < t) (hnear : g ≤ t⁻¹) :
    0 ≤ atom g e t := by
  have hgt : g*t ≤ 1 := by
    rw [← one_div t] at hnear
    exact (le_div_iff₀ ht).mp hnear
  have hab : |2*e*g*t| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos ht, abs_of_pos hg]
    norm_num
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-2*|e|) (le_of_lt (mul_pos hg ht))]
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.cos_nonneg_of_mem_Icc
  have hp := Real.pi_gt_three
  have hb := abs_le.mp hab
  constructor <;> linarith

theorem critical_atom_nonneg (g t : ℝ) : 0 ≤ atom g 0 t := by
  simp only [atom, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero, zero_mul,
    Real.cos_zero, mul_one]
  exact (Real.exp_pos _).le

theorem anchor_bound (g t : ℝ) (hg : 0 < g) (h100 : g ≤ 100) (ht : 0 < t) :
    Real.exp (-10000*t) ≤ atom g 0 t := by
  simp only [atom, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero, zero_mul,
    Real.cos_zero, mul_one]
  apply Real.exp_le_exp.mpr
  have hs : g^2 ≤ 10000 := by nlinarith
  nlinarith

-- A generic infinite-sum lemma: no positivity of the total is assumed.
theorem head_tail_sum_bound (f G : ℕ → ℝ) (j0 : ℕ) (H C L : ℝ)
    (hf : Summable f) (hG : Summable G) (hC : 0 ≤ C)
    (hhead : H ≤ f j0) (hzero : G j0 = 0)
    (hpoint : ∀ j, j ≠ j0 → -C*G j ≤ f j)
    (htail : (∑' j, G j) ≤ L) :
    H-C*L ≤ ∑' j, f j := by
  classical
  let head : ℕ → ℝ := fun j => if j = j0 then H else 0
  have hh : Summable head := summable_of_ne_finset_zero (s := {j0}) (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [head,hj])
  have hdom : ∀ j, head j-C*G j ≤ f j := by
    intro j
    by_cases h : j = j0
    · subst j
      simpa [head,hzero] using hhead
    · simpa [head,h] using hpoint j h
  have hi := (hh.sub (hG.mul_left C)).tsum_le_tsum hdom hf
  rw [hh.tsum_sub (hG.mul_left C), tsum_mul_left] at hi
  have hs : (∑' j, head j) = H := by simp [head]
  rw [hs] at hi
  nlinarith

structure SpectralInput where
  gamma : ℕ → ℝ
  eps : ℕ → ℝ
  gamma_pos : ∀ j, 0 < gamma j
  strip : ∀ j, |eps j| ≤ 1/2
  verified : ∀ j, gamma j ≤ 1000 → eps j = 0
  anchor : ℕ
  anchor_low : gamma anchor ≤ 100
  gauss_sum : ∀ t > 0, Summable (fun j => gaussian (gamma j) t)
  gauss_tail : ∀ t > 0, ∀ L ≥ 10,
    (∑' j, if L < gamma j then gaussian (gamma j) t else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)

theorem spectral_head_tail (S : SpectralInput) (t L : ℝ) (ht : 0 < t)
    (hL : 10 ≤ L) (ha : S.gamma S.anchor ≤ L)
    (hnear : ∀ j, S.gamma j ≤ L → 0 ≤ atom (S.gamma j) (S.eps j) t) :
    Real.exp (-10000*t) - Real.exp (t/4)*(L^2+t⁻¹)*Real.exp (-L^2*t) ≤
      kernel S.gamma S.eps t := by
  classical
  let G : ℕ → ℝ := fun j => if L < S.gamma j then gaussian (S.gamma j) t else 0
  have hGs : Summable G := (S.gauss_sum t ht).of_nonneg_of_le
    (by intro j; simp only [G]; split_ifs
        · exact (Real.exp_pos _).le
        · exact le_rfl)
    (by intro j; simp only [G]; split_ifs; exact le_rfl; exact (Real.exp_pos _).le)
  have he0 : S.eps S.anchor = 0 := S.verified _ (by linarith [S.anchor_low])
  have hz : G S.anchor = 0 := by simp [G, not_lt.mpr ha]
  have hhead : Real.exp (-10000*t) ≤ atom (S.gamma S.anchor) (S.eps S.anchor) t := by
    rw [he0]
    exact anchor_bound _ t (S.gamma_pos _) S.anchor_low ht
  have hpoint : ∀ j, j ≠ S.anchor →
      -Real.exp (t/4)*G j ≤ atom (S.gamma j) (S.eps j) t := by
    intro j hj
    by_cases h : L < S.gamma j
    · simp only [G, if_pos h]
      have hb := atom_abs_bound (S.gamma j) (S.eps j) t (S.strip j) ht
      have hn := neg_abs_le (atom (S.gamma j) (S.eps j) t)
      nlinarith
    · simp only [G, if_neg h, mul_zero]
      exact hnear j (le_of_not_gt h)
  have h := head_tail_sum_bound _ G S.anchor (Real.exp (-10000*t))
    (Real.exp (t/4)) ((L^2+t⁻¹)*Real.exp (-L^2*t))
    (kernel_summable S.gamma S.eps t S.strip ht (S.gauss_sum t ht)) hGs
    (Real.exp_pos _).le hhead hz hpoint (S.gauss_tail t ht L hL)
  simpa only [kernel, mul_assoc] using h
end BranchSpectral

namespace BranchSpectral
open BranchFull MeasureTheory Set

theorem spectral_small_bound (S : SpectralInput) (t : ℝ) (ht : 0 < t)
    (hc : t ≤ 1/10000) :
    Real.exp (-10000*t)*(1-smallRatio t) ≤ kernel S.gamma S.eps t := by
  have hi : (10000:ℝ) ≤ t⁻¹ := by
    rw [← one_div t]
    apply (le_div_iff₀ ht).2
    linarith
  have h := spectral_head_tail S t t⁻¹ ht (by linarith)
    (le_trans S.anchor_low (by linarith))
    (fun j hj => atom_near_nonneg _ _ _ (S.gamma_pos j) (S.strip j) ht hj)
  have he : -10000*t + (-t⁻¹+(10000+1/4)*t) = t/4 + (-(t⁻¹)^2*t) := by
    field_simp
    <;> ring
  have heq : Real.exp (-10000*t)*smallRatio t =
      Real.exp (t/4)*((t⁻¹)^2+t⁻¹)*Real.exp (-(t⁻¹)^2*t) := by
    unfold smallRatio
    calc
      _ = ((t⁻¹)^2+t⁻¹)*(Real.exp (-10000*t)*Real.exp (-t⁻¹+(10000+1/4)*t)) := by ring
      _ = ((t⁻¹)^2+t⁻¹)*Real.exp (t/4+(-(t⁻¹)^2*t)) := by rw [← Real.exp_add, he]
      _ = _ := by rw [Real.exp_add]; ring
  rw [← heq] at h
  nlinarith

theorem spectral_large_bound (S : SpectralInput) (t : ℝ) (ht : 0 < t) :
    Real.exp (-10000*t)*(1-largeRatio t) ≤ kernel S.gamma S.eps t := by
  have h := spectral_head_tail S t 1000 ht (by norm_num)
    (by linarith [S.anchor_low]) (by
      intro j hj
      rw [S.verified j hj]
      exact critical_atom_nonneg _ _)
  have he : -10000*t + (-(1000000-10000-1/4)*t) = t/4 + (-(1000:ℝ)^2*t) := by ring
  have heq : Real.exp (-10000*t)*largeRatio t =
      Real.exp (t/4)*((1000:ℝ)^2+t⁻¹)*Real.exp (-(1000:ℝ)^2*t) := by
    unfold largeRatio
    calc
      _ = (1000000+t⁻¹)*(Real.exp (-10000*t)*Real.exp (-(1000000-10000-1/4)*t)) := by ring
      _ = (1000000+t⁻¹)*Real.exp (t/4+(-(1000:ℝ)^2*t)) := by rw [← Real.exp_add, he]
      _ = _ := by rw [Real.exp_add]; ring
  rw [← heq] at h
  nlinarith

theorem spectral_kernel_lower_bound (S : SpectralInput) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < kernel S.gamma S.eps t := by
  exact heat_lower_bound _ (spectral_small_bound S)
    (fun t ht _ => spectral_large_bound S t ht)

theorem spectral_kernel_pos (S : SpectralInput) :
    ∀ t > 0, 0 < kernel S.gamma S.eps t := by
  intro t ht
  have h := spectral_kernel_lower_bound S t ht
  have hpos := Real.exp_pos (-10000*t)
  linarith

-- Contracts to be proved for the actual xi-derived Q, not declarations of axioms.
structure BaseInput (S : SpectralInput) where
  Q : ℕ → ℝ → ℝ
  representation : ∀ n ≥ 1, ∀ u > 0, Q n u = QnAudit.oldQ (kernel S.gamma S.eps) u n
  integrable : ∀ n ≥ 1, ∀ u > 0,
    IntegrableOn (fun t => QnAudit.weight (u^2) n t * kernel S.gamma S.eps t) (Ioi 0)

def NegativeSeed {S : SpectralInput} (D : BaseInput S) : Prop :=
  ∃ n ≥ 1, ∃ u > 0, D.Q n u < 0

def OffLine (S : SpectralInput) : Set ℕ := {j | S.eps j ≠ 0}

-- The analytic contradiction is uniform in the cardinality of OffLine.
theorem negative_seed_impossible (S : SpectralInput) (D : BaseInput S) :
    ¬ NegativeSeed D := by
  rintro ⟨n, hn, u, hu, hneg⟩
  rw [D.representation n hn u hu] at hneg
  have hp := QnAudit.oldQ_pos (kernel S.gamma S.eps) u n hu
    (spectral_kernel_pos S) (D.integrable n hn u hu)
  exact (not_lt_of_ge hp.le) hneg

theorem branch2_finite (S : SpectralInput) (D : BaseInput S) :
    ¬ (NegativeSeed D ∧ (OffLine S).Finite ∧ (OffLine S).Nonempty) := by
  intro h
  exact negative_seed_impossible S D h.1

theorem branch3_infinite (S : SpectralInput) (D : BaseInput S) :
    ¬ (NegativeSeed D ∧ (OffLine S).Infinite) := by
  intro h
  exact negative_seed_impossible S D h.1

-- The logical closure requested by the project, independent of the analytic proof.
theorem nonnegative_via_branches (Q : ℕ → ℝ → ℝ) (off : Set ℕ)
    (hRH : off = ∅ → ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u)
    (b2 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ off.Finite ∧ off.Nonempty))
    (b3 : ¬ ((∃ n ≥ 1, ∃ u > 0, Q n u < 0) ∧ off.Infinite)) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by
  classical
  intro n hn u hu
  by_contra h
  have hneg : Q n u < 0 := lt_of_not_ge h
  have seed : ∃ m ≥ 1, ∃ v > 0, Q m v < 0 := ⟨n,hn,u,hu,hneg⟩
  by_cases he : off = ∅
  · exact (not_lt_of_ge (hRH he n hn u hu)) hneg
  · have hne : off.Nonempty := Set.nonempty_iff_ne_empty.mpr he
    by_cases hf : off.Finite
    · exact b2 ⟨seed,hf,hne⟩
    · exact b3 ⟨seed,hf⟩

-- RH direction obtained solely from nonnegative critical atoms.
theorem critical_kernel_pos (S : SpectralInput) (hoff : OffLine S = ∅)
    (t : ℝ) (ht : 0 < t) : 0 < kernel S.gamma S.eps t := by
  have he0 : ∀ j, S.eps j = 0 := by
    intro j
    by_contra hj
    have hm : j ∈ OffLine S := hj
    rw [hoff] at hm
    exact hm
  have hs := kernel_summable S.gamma S.eps t S.strip ht (S.gauss_sum t ht)
  have hhead : Real.exp (-10000*t) ≤ atom (S.gamma S.anchor) (S.eps S.anchor) t := by
    rw [he0]
    exact anchor_bound _ _ (S.gamma_pos _) S.anchor_low ht
  have h := head_tail_sum_bound (fun j => atom (S.gamma j) (S.eps j) t)
    (fun _ => 0) S.anchor (Real.exp (-10000*t)) 0 0 hs (by simp)
    (by norm_num) hhead rfl (by
      intro j _
      rw [he0]
      simpa using critical_atom_nonneg (S.gamma j) t) (by simp)
  have hh : Real.exp (-10000*t) ≤ kernel S.gamma S.eps t := by
    simpa [kernel] using h
  exact lt_of_lt_of_le (Real.exp_pos _) hh

theorem critical_implies_base_nonnegative (S : SpectralInput) (D : BaseInput S)
    (hoff : OffLine S = ∅) : ∀ n ≥ 1, ∀ u > 0, 0 ≤ D.Q n u := by
  intro n hn u hu
  rw [D.representation n hn u hu]
  exact (QnAudit.oldQ_pos _ u n hu (critical_kernel_pos S hoff)
    (D.integrable n hn u hu)).le

theorem base_nonnegative_by_logical_chain (S : SpectralInput) (D : BaseInput S) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ D.Q n u := by
  exact nonnegative_via_branches D.Q (OffLine S) (critical_implies_base_nonnegative S D)
    (branch2_finite S D) (branch3_infinite S D)

-- A stronger consequence of the same analytic inputs; no RH premise.
theorem base_strict_positive (S : SpectralInput) (D : BaseInput S) :
    ∀ n ≥ 1, ∀ u > 0, 0 < D.Q n u := by
  exact QnAudit.ordinary_Q_positive_from_heat_representation D.Q
    (kernel S.gamma S.eps) D.representation (spectral_kernel_pos S) D.integrable
end BranchSpectral


open Set Filter
noncomputable section
namespace BranchCascade

theorem negative_seed_has_stationary_minimum
    (f : ℝ → ℝ) (a b x : ℝ)
    (hax : a < x) (hxb : x < b) (hx : f x < 0)
    (ha : f x < f a) (hb : f x < f b)
    (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ u ∈ Ioo a b, f u < 0 ∧ deriv f u = 0 := by
  obtain ⟨u, hu, hm⟩ := isCompact_Icc.exists_isMinOn
    ⟨x, hax.le, hxb.le⟩ hc
  have hux := (isMinOn_iff.mp hm) x ⟨hax.le, hxb.le⟩
  have hn : f u < 0 := lt_of_le_of_lt hux hx
  have hua : a < u := by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h] at hux
      linarith
    · exact h
  have hub : u < b := by
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h] at hux
      linarith
    · exact h
  have hmL : IsLocalMin f u := hm.isLocalMin
    (Filter.mem_of_superset (Ioo_mem_nhds hua hub) Ioo_subset_Icc_self)
  have hd' : DifferentiableAt ℝ f u :=
    (hd u ⟨hua, hub⟩).differentiableAt (Ioo_mem_nhds hua hub)
  exact ⟨u, ⟨hua, hub⟩, hn, hmL.hasDerivAt_eq_zero hd'.hasDerivAt⟩

theorem negative_seed_forces_next_index
    (Q : ℕ → ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n) (a b x : ℝ)
    (ha0 : 0 < a) (hax : a < x) (hxb : x < b) (hx : Q n x < 0)
    (ha : Q n x < Q n a) (hb : Q n x < Q n b)
    (hc : ContinuousOn (Q n) (Icc a b))
    (hd : DifferentiableOn ℝ (Q n) (Ioo a b))
    (hrec : ∀ u > 0,
      Q (n+1) u = (2*(n:ℝ)-1)*Q n u - u*deriv (Q n) u) :
    ∃ u > 0, Q (n+1) u < 0 := by
  obtain ⟨u, hu, hneg, hz⟩ := negative_seed_has_stationary_minimum
    (Q n) a b x hax hxb hx ha hb hc hd
  have hu0 : 0 < u := lt_trans ha0 hu.1
  refine ⟨u, hu0, ?_⟩
  rw [hrec u hu0, hz, mul_zero, sub_zero]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact mul_neg_of_pos_of_neg (by linarith) hneg

theorem seed_to_stationary_from_limits
    (f : ℝ → ℝ) (x : ℝ) (hx0 : 0 < x) (hx : f x < 0)
    (hc : ContinuousOn f (Ioi 0)) (hd : DifferentiableOn ℝ f (Ioi 0))
    (hleft : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hright : Tendsto f atTop atTop) :
    ∃ u > 0, f u < 0 ∧ deriv f u = 0 := by
  have he1 := hleft.eventually_const_lt hx
  have he2 : ∀ᶠ a in nhdsWithin (0:ℝ) (Ioi 0), a < x :=
    (eventually_lt_nhds hx0).filter_mono nhdsWithin_le_nhds
  have he3 : ∀ᶠ a in nhdsWithin (0:ℝ) (Ioi 0), a ∈ Ioi 0 :=
    self_mem_nhdsWithin
  obtain ⟨a, ha0, hax, hfa⟩ := (he3.and (he2.and he1)).exists
  obtain ⟨b, hxb, hfb⟩ := ((eventually_gt_atTop x).and
    (hright.eventually (eventually_gt_atTop (f x)))).exists
  have hsub : Icc a b ⊆ Ioi (0:ℝ) := by
    intro t ht
    exact lt_of_lt_of_le ha0 ht.1
  have hsub' : Ioo a b ⊆ Ioi (0:ℝ) :=
    fun t ht => lt_trans ha0 ht.1
  obtain ⟨u, hu, hn, hz⟩ := negative_seed_has_stationary_minimum f a b x
    hax hxb hx hfa hfb (hc.mono hsub) (hd.mono hsub')
  exact ⟨u, lt_trans ha0 hu.1, hn, hz⟩

theorem cascade_step_from_limits
    (Q : ℕ → ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hc : ContinuousOn (Q n) (Ioi 0))
    (hd : DifferentiableOn ℝ (Q n) (Ioi 0))
    (hleft : Tendsto (Q n) (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hright : Tendsto (Q n) atTop atTop)
    (hrec : ∀ u > 0,
      Q (n+1) u = (2*(n:ℝ)-1)*Q n u - u*deriv (Q n) u)
    (seed : ∃ x > 0, Q n x < 0) :
    ∃ u > 0, Q (n+1) u < 0 := by
  obtain ⟨x, hx0, hx⟩ := seed
  obtain ⟨u, hu, hneg, hz⟩ := seed_to_stationary_from_limits (Q n) x hx0 hx
    hc hd hleft hright
  refine ⟨u, hu, ?_⟩
  rw [hrec u hu, hz, mul_zero, sub_zero]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact mul_neg_of_pos_of_neg (by linarith) hneg

theorem full_negative_cascade
    (Q : ℕ → ℝ → ℝ) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (seed : ∃ x > 0, Q n0 x < 0)
    (step : ∀ n ≥ 1, (∃ x > 0, Q n x < 0) → ∃ x > 0, Q (n+1) x < 0) :
    ∀ j : ℕ, ∃ x > 0, Q (n0+j) x < 0 := by
  intro j
  induction j with
  | zero => simpa using seed
  | succ j ih =>
    have h := step (n0+j) (by omega) ih
    simpa [Nat.add_assoc] using h

theorem cascade_from_analytic_inputs
    (Q : ℕ → ℝ → ℝ) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (seed : ∃ x > 0, Q n0 x < 0)
    (hc : ∀ n ≥ 1, ContinuousOn (Q n) (Ioi 0))
    (hd : ∀ n ≥ 1, DifferentiableOn ℝ (Q n) (Ioi 0))
    (hleft : ∀ n ≥ 1, Tendsto (Q n) (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hright : ∀ n ≥ 1, Tendsto (Q n) atTop atTop)
    (hrec : ∀ n ≥ 1, ∀ u > 0,
      Q (n+1) u = (2*(n:ℝ)-1)*Q n u - u*deriv (Q n) u) :
    ∀ j : ℕ, ∃ u > 0, Q (n0+j) u < 0 := by
  apply full_negative_cascade Q n0 hn0 seed
  intro n hn hneg
  exact cascade_step_from_limits Q n hn (hc n hn) (hd n hn)
    (hleft n hn) (hright n hn) (hrec n hn) hneg
end BranchCascade



-- Audit every new theorem, including propositions used as hypotheses.


open MeasureTheory Set Filter Topology

theorem solution (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (hoff : ({j : ℕ | eps j ≠ 0} : Set ℕ) = ∅)
    (t : ℝ) (ht : 0 < t) : 0 < (∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) := by
  let S : BranchSpectral.SpectralInput := ⟨gamma, eps, gamma_pos, strip, verified, anchor, anchor_low, gauss_sum, gauss_tail⟩
  exact @BranchSpectral.critical_kernel_pos S hoff t ht
