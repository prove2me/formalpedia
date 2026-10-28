-- Prove2me | solution 1 for DIGing.Undir.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T13:08:41.986397+00:00
-- url     : https://prove2.me/submissions/839100ff-5bdf-4f61-9ae9-2031f73a29a0

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Undir_Setting

-- Complete module: DGProof/ScalarSmooth.lean
namespace DIGing.Undir.DGFresh

theorem scalar_descent (f f' : ℝ → ℝ) (L : ℝ) (hd : ∀ z, HasDerivAt f (f' z) z)
    (hL : ∀ a b, |f' a-f' b| ≤ L*|a-b|) (a b : ℝ) :
    f b ≤ f a + f' a*(b-a) + L/2*(b-a)^2 := by
  let q : ℝ → ℝ := fun z => f z - f a - f' a*(z-a) - L/2*(z-a)^2
  have hq (z : ℝ) : HasDerivAt q (f' z-f' a-L*(z-a)) z := by
    have h := (((hd z).sub_const (f a)).sub (((hasDerivAt_id z).sub_const a).const_mul (f' a))).sub
      ((((hasDerivAt_id z).sub_const a).pow 2).const_mul (L/2)) 
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hc : Continuous q := continuous_iff_continuousAt.mpr fun z => (hq z).continuousAt
  have hdiff : Differentiable ℝ q := fun z => (hq z).differentiableAt
  have hqa : q a = 0 := by simp [q]
  rcases le_total a b with hab | hba
  · have hm : AntitoneOn q (Set.Ici a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have haz : a ≤ z := (interior_subset hz)
      have h := (abs_le.mp (hL z a)).2
      rw [abs_of_nonneg (sub_nonneg.mpr haz)] at h
      linarith
    have h := hm (by simp) hab hab
    rw [hqa] at h
    dsimp [q] at h
    linarith
  · have hm : MonotoneOn q (Set.Iic a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have hza : z ≤ a := (interior_subset (s := Set.Iic a) hz)
      have h := (abs_le.mp (hL z a)).1
      rw [abs_of_nonpos (sub_nonpos.mpr hza)] at h
      linarith
    have h := hm hba (by simp) hba
    rw [hqa] at h
    dsimp [q] at h
    linarith

end DIGing.Undir.DGFresh

-- Complete module: DGProof/SmoothDescent.lean
open scoped RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {p : ℕ}
lemma smooth_descent (f : EuclideanSpace ℝ (Fin p) → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (x y : EuclideanSpace ℝ (Fin p)) :
    f y ≤ f x + inner ℝ (gradient f x) (y-x) + L/2*‖y-x‖^2 := by
  let d := y-x
  let g : ℝ → ℝ := fun t => f (x+t • d)
  let g' : ℝ → ℝ := fun t => inner ℝ (gradient f (x+t • d)) d
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    exact ((hf _).hasGradientAt.hasFDerivAt.comp_hasDerivAt t (hd t))
  have hl (s t : ℝ) : |g' s - g' t| ≤ (L*‖d‖^2)*|s-t| := by
    dsimp [g']
    rw [← inner_sub_left]
    calc
      |inner ℝ (gradient f (x+s • d)-gradient f (x+t • d)) d| ≤
          ‖gradient f (x+s • d)-gradient f (x+t • d)‖*‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L*‖(x+s • d)-(x+t • d)‖)*‖d‖ := mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
      _ = (L*‖d‖^2)*|s-t| := by
        rw [show (x+s • d)-(x+t • d) = (s-t) • d by module]
        rw [norm_smul, Real.norm_eq_abs]
        ring
  have h := scalar_descent g g' (L*‖d‖^2) hg hl 0 1
  simp only [g, g', zero_smul, add_zero, one_smul, sub_zero, one_pow, mul_one] at h
  have he : x + (y-x) = y := by abel
  dsimp [d] at h
  rw [he] at h
  nlinarith [h]
end DIGing.Undir.DGFresh

-- Complete module: DGProof/NativeParameters.lean
open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma agents_pos {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {mu : Fin n → ℝ}
    (h : Assumption5 f mu) : 0 < n := by
  obtain ⟨i, _⟩ := h.2.1
  exact Nat.pos_of_ne_zero (fun hn => by subst n; exact Fin.elim0 i)
lemma mean_mu_pos {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {mu : Fin n → ℝ}
    (h : Assumption5 f mu) : 0 < mubar mu := by
  have hn : (0 : ℝ) < n := by exact_mod_cast agents_pos h
  apply mul_pos (one_div_pos.mpr hn)
  obtain ⟨i, hi⟩ := h.2.1
  exact Finset.sum_pos' (fun j _ => h.1 j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (h.1 i) (Ne.symm hi)⟩
lemma Lc_le_max (Lc : Fin n → ℝ) (i : Fin n) : Lc i ≤ Lmax Lc :=
  le_ciSup (Set.finite_range Lc).bddAbove i
lemma max_pos {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) : 0 < Lmax Lc := by
  obtain ⟨i, _⟩ := h5.2.1
  exact (h4 i).1.trans_le (Lc_le_max Lc i)
lemma mean_le_max (hn : 0 < n) (Lc : Fin n → ℝ) : Lbar Lc ≤ Lmax Lc := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => Lc_le_max Lc i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  dsimp [Lbar]
  exact (mul_le_mul_of_nonneg_left h (le_of_lt (one_div_pos.mpr hn'))).trans_eq (by field_simp)

lemma strong_le_smooth (hp : 0 < p) (f : EuclideanSpace ℝ (Fin p) → ℝ) (L μ : ℝ)
    (hL : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hμ : ∀ x y, f y + inner ℝ (gradient f y) (x-y) + μ/2*‖x-y‖^2 ≤ f x) : μ ≤ L := by
  let v : EuclideanSpace ℝ (Fin p) := EuclideanSpace.single ⟨0,hp⟩ 1
  have hv : ‖v‖ = 1 := by simp [v]
  have h1 := hμ v 0
  have h2 := hμ 0 v
  simp only [sub_zero, zero_sub, norm_neg, inner_neg_right, hv, one_pow, mul_one] at h1 h2
  have h3 := abs_real_inner_le_norm (gradient f v-gradient f 0) v
  rw [inner_sub_left, hv, mul_one] at h3
  have h4 := hL v 0
  simp only [sub_zero, hv, mul_one] at h4
  have h5 := (abs_le.mp h3).2
  linarith

lemma mu_le_Lc (hp : 0 < p) {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {Lc mu : Fin n → ℝ} (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (i : Fin n) : mu i ≤ Lc i :=
  strong_le_smooth hp (f i) (Lc i) (mu i) (h4 i).2.2 (h5.2.2 i)
end DIGing.Undir.DGFresh

-- Complete module: DGProof/ScalarSplit.lean

namespace DIGing.Undir.DGFresh

noncomputable def splitRoot (J δ : ℝ) : ℝ :=
  (Real.sqrt (J ^ 2 + (1 - δ ^ 2) * J) + δ) / (J + 1)

theorem splitRoot_properties {J δ : ℝ} (hJ : 0 < J) (hd0 : 0 ≤ δ) (hd1 : δ < 1) :
    δ < splitRoot J δ ∧ splitRoot J δ < 1 ∧
      J * (1 - splitRoot J δ ^ 2) = (splitRoot J δ - δ) ^ 2 := by
  have hd : 0 < 1 - δ ^ 2 := by nlinarith
  have hs : 0 ≤ J ^ 2 + (1 - δ ^ 2) * J := by positivity
  have hq := Real.sq_sqrt hs
  have hq0 := Real.sqrt_nonneg (J ^ 2 + (1 - δ ^ 2) * J)
  have hj1 : 0 < J + 1 := by positivity
  have hlow : δ * J < Real.sqrt (J ^ 2 + (1 - δ ^ 2) * J) := by
    nlinarith [mul_pos hJ hd, mul_nonneg (sq_nonneg J) hd.le]
  have hupp : Real.sqrt (J ^ 2 + (1 - δ ^ 2) * J) < J + 1 - δ := by
    nlinarith [mul_pos hj1 (sq_pos_of_pos (show 0 < 1 - δ by linarith))]
  refine ⟨?_, ?_, ?_⟩
  · unfold splitRoot
    apply (lt_div_iff₀ hj1).2
    nlinarith
  · unfold splitRoot
    apply (div_lt_iff₀ hj1).2
    nlinarith
  · unfold splitRoot
    field_simp [ne_of_gt hj1]
    rw [show J * (J + (1 - δ ^ 2)) = J ^ 2 + (1 - δ ^ 2) * J by ring]
    nlinarith [congrArg (fun z : ℝ => J * z) hq]

theorem alphaSplit_eq {J δ μ : ℝ} (hJ : 0 < J) (hd0 : 0 ≤ δ)
    (hd1 : δ < 1) (hμ : 0 < μ) :
    alphaSplit J δ μ = (3 / 2) * (1 - splitRoot J δ ^ 2) / μ := by
  have hp := (splitRoot_properties hJ hd0 hd1).2.2
  have he : splitRoot J δ - δ =
      (Real.sqrt (J ^ 2 + (1 - δ ^ 2) * J) - δ * J) / (J + 1) := by
    unfold splitRoot
    field_simp
    ring
  rw [he] at hp
  unfold alphaSplit
  field_simp [ne_of_gt hJ, ne_of_gt hμ, ne_of_gt (show 0 < J + 1 by positivity)] at hp ⊢
  nlinarith

end DIGing.Undir.DGFresh

-- Complete module: DGProof/RateGuards.lean

namespace DIGing.Undir.DGFresh

theorem root_pow {q : ℝ} (hq : 0 ≤ q) {B : ℕ} (hB : 0 < B) :
    (q ^ ((1 : ℝ) / (B : ℝ))) ^ B = q := by
  simpa only [one_div] using Real.rpow_inv_natCast_pow hq (Nat.ne_of_gt hB)

theorem rate_guards {J δ μ α : ℝ} {B : ℕ} (hJ : 0 < J)
    (hd0 : 0 ≤ δ) (hd1 : δ < 1) (hμ : 0 < μ) (hα : 0 < α)
    (hB : 0 < B) (hmax : α < alphaMax J δ μ) :
    let l := rateLam J δ μ α B
    0 < l ∧ l < 1 ∧ δ < l ^ B ∧
      1 - α * μ / (3 / 2) ≤ l ^ (2 * B) ∧
      α * μ / (3 / 2) * J ≤ (l ^ B - δ) ^ 2 := by
  dsimp only
  let a := α * μ / (3 / 2)
  let b0 := splitRoot J δ
  obtain ⟨hb0d, hb01, hb0eq⟩ := splitRoot_properties hJ hd0 hd1
  change δ < b0 at hb0d
  change b0 < 1 at hb01
  change J * (1 - b0 ^ 2) = (b0 - δ) ^ 2 at hb0eq
  have hb00 : 0 < b0 := lt_of_le_of_lt hd0 hb0d
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hamax : a * J < (1 - δ) ^ 2 := by
    unfold alphaMax at hmax
    have hh := (lt_div_iff₀ (mul_pos hμ hJ)).mp hmax
    dsimp [a]
    nlinarith
  by_cases hs : α ≤ alphaSplit J δ μ
  · have ha : a ≤ 1 - b0 ^ 2 := by
      rw [alphaSplit_eq hJ hd0 hd1 hμ] at hs
      have hh := (le_div_iff₀ hμ).mp hs
      dsimp [a, b0]
      nlinarith
    have hq0 : 0 < 1 - a := by nlinarith [sq_pos_of_pos hb00]
    have hq1 : 1 - a < 1 := by linarith
    let l := (1 - a) ^ ((1 : ℝ) / (2 * (B : ℝ)))
    have hl0 : 0 < l := Real.rpow_pos_of_pos hq0 _
    have hl1 : l < 1 := Real.rpow_lt_one hq0.le hq1 (by positivity)
    have hp : l ^ (2 * B) = 1 - a := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using root_pow hq0.le (show 0 < 2 * B by omega)
    have hp' : (l ^ B) ^ 2 = 1 - a := by
      rw [← pow_mul, Nat.mul_comm B 2]
      exact hp
    have hb : b0 ≤ l ^ B := by nlinarith [pow_pos hl0 B]
    have hdl : δ < l ^ B := lt_of_lt_of_le hb0d hb
    have hh : a * J ≤ (l ^ B - δ) ^ 2 := by
      nlinarith [mul_nonneg hJ.le (sub_nonneg.mpr ha),
        mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hb0d.le)]
    simpa only [rateLam, if_pos hs, a, l] using
      (show 0 < l ∧ l < 1 ∧ δ < l ^ B ∧ 1 - a ≤ l ^ (2 * B) ∧
        a * J ≤ (l ^ B - δ) ^ 2 from ⟨hl0, hl1, hdl, hp.ge, hh⟩)
  · have ha : 1 - b0 ^ 2 < a := by
      have hs' := lt_of_not_ge hs
      rw [alphaSplit_eq hJ hd0 hd1 hμ] at hs'
      have hh := (div_lt_iff₀ hμ).mp hs'
      dsimp [a, b0]
      nlinarith
    let b := Real.sqrt (a * J) + δ
    have hsq := Real.sq_sqrt (show 0 ≤ a * J by positivity)
    have hs0 := Real.sqrt_nonneg (a * J)
    have hspos : 0 < Real.sqrt (a * J) := Real.sqrt_pos.2 (mul_pos ha0 hJ)
    have hb0 : 0 < b := by dsimp [b]; positivity
    have hbd : δ < b := by dsimp [b]; linarith
    have hb1 : b < 1 := by dsimp [b]; nlinarith only [hsq, hs0, hamax, hd1]
    have hb : b0 < b := by
      dsimp [b]
      nlinarith only [mul_pos hJ (sub_pos.mpr ha), hb0eq, hsq, hs0, hb0d]
    let l := b ^ ((1 : ℝ) / (B : ℝ))
    have hl0 : 0 < l := Real.rpow_pos_of_pos hb0 _
    have hl1 : l < 1 := Real.rpow_lt_one hb0.le hb1 (by positivity)
    have hp : l ^ B = b := root_pow hb0.le hB
    have hp' : l ^ (2 * B) = b ^ 2 := by rw [Nat.mul_comm 2 B, pow_mul, hp]
    have hh : 1 - a ≤ b ^ 2 := by nlinarith only [ha, hb, hb00]
    have he : a * J = (b - δ) ^ 2 := by
      dsimp [b]
      simpa only [add_sub_cancel_right] using hsq.symm
    have hdl : δ < l ^ B := by rw [hp]; exact hbd
    have hq : 1 - a ≤ l ^ (2 * B) := by rw [hp']; exact hh
    have hg : a * J ≤ (l ^ B - δ) ^ 2 := by rw [hp, ← he]
    simpa only [rateLam, if_neg hs, a, b, l, div_mul_eq_mul_div] using
      (show 0 < l ∧ l < 1 ∧ δ < l ^ B ∧ 1 - a ≤ l ^ (2 * B) ∧
        a * J ≤ (l ^ B - δ) ^ 2 from ⟨hl0, hl1, hdl, hq, hg⟩)

end DIGing.Undir.DGFresh

-- Complete module: DGProof/NativeRate.lean

namespace DIGing.Undir.DGFresh

theorem mean_mu_le_max {n p : ℕ} {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {Lc mu : Fin n → ℝ} (hp : 0 < p) (h4 : Assumption4 f Lc)
    (h5 : Assumption5 f mu) : mubar mu ≤ Lmax Lc := by
  have hn : (0 : ℝ) < n := by exact_mod_cast agents_pos h5
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (mu_le_Lc hp h4 h5 i).trans (Lc_le_max Lc i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  dsimp [mubar]
  have hm := mul_le_mul_of_nonneg_left hh (one_div_pos.mpr hn).le
  calc
    (1 / (n : ℝ)) * ∑ i, mu i ≤ (1 / (n : ℝ)) * ((n : ℝ) * Lmax Lc) := hm
    _ = Lmax Lc := by field_simp

theorem kappa_ge_one {n p : ℕ} {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {Lc mu : Fin n → ℝ} (hp : 0 < p) (h4 : Assumption4 f Lc)
    (h5 : Assumption5 f mu) : 1 ≤ kappa Lc mu := by
  apply (le_div_iff₀ (mean_mu_pos h5)).2
  simpa using mean_mu_le_max hp h4 h5

theorem native_J_pos {n p B : ℕ} {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {Lc mu : Fin n → ℝ} (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu)
    (hB : 0 < B) : 0 < J1 Lc mu B := by
  have hk : 0 < kappa Lc mu := div_pos (max_pos h4 h5) (mean_mu_pos h5)
  unfold J1
  positivity

theorem native_J_large {n p B : ℕ} {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {Lc mu : Fin n → ℝ} (hp : 0 < p) (h4 : Assumption4 f Lc)
    (h5 : Assumption5 f mu) (hB : 0 < B) : 15 ≤ J1 Lc mu B := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast agents_pos h5
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hk := kappa_ge_one hp h4 h5
  have hsn : 1 ≤ Real.sqrt (n : ℝ) := (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).2 (by simpa using hn)
  have hsk : 1 ≤ Real.sqrt (kappa Lc mu) := (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith)).2 (by simpa using hk)
  have hprod : 1 ≤ Real.sqrt (n : ℝ) * Real.sqrt (kappa Lc mu) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsn) (sub_nonneg.mpr hsk)]
  have hfac : 5 ≤ 1 + 4 * Real.sqrt (n : ℝ) * Real.sqrt (kappa Lc mu) := by nlinarith
  have hb2 : 1 ≤ (B : ℝ) ^ 2 := by nlinarith
  have hpre : 3 ≤ 3 * kappa Lc mu * (B : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hb2)]
  unfold J1
  nlinarith [mul_nonneg (sub_nonneg.mpr hpre) (sub_nonneg.mpr hfac)]

theorem rate_quantitative {J δ μ α : ℝ} {B : ℕ} (hJ : 15 ≤ J)
    (hd0 : 0 ≤ δ) (hd1 : δ < 1) (hμ : 0 < μ) (hα : 0 < α)
    (hB : 0 < B) (hmax : α < alphaMax J δ μ) :
    1 / 2 < rateLam J δ μ α B ∧
      1 - α * μ / (3 / 2) ≤ rateLam J δ μ α B ^ 2 := by
  have hJ0 : 0 < J := by linarith
  obtain ⟨hl0, hl1, _, hq, _⟩ := rate_guards hJ0 hd0 hd1 hμ hα hB hmax
  let l := rateLam J δ μ α B
  have hpow : l ^ (2 * B) ≤ l ^ 2 :=
    pow_le_pow_of_le_one hl0.le hl1.le (by omega)
  have hq' : 1 - α * μ / (3 / 2) ≤ l ^ 2 := hq.trans hpow
  have ha0 : 0 < α * μ / (3 / 2) := by positivity
  have ha : α * μ / (3 / 2) < 1 / 15 := by
    unfold alphaMax at hmax
    have hh := (lt_div_iff₀ (mul_pos hμ hJ0)).mp hmax
    have hd : (1 - δ) ^ 2 ≤ 1 := by nlinarith
    have hm := mul_nonneg (sub_nonneg.mpr hJ) ha0.le
    nlinarith only [hh, hd, hm]
  constructor
  · change 1 / 2 < l
    nlinarith only [hq', ha, hl0]
  · exact hq'

theorem native_step_bound {n p B : ℕ} {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {Lc mu : Fin n → ℝ} (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu)
    (hB : 0 < B) {δ α : ℝ} (hd0 : 0 ≤ δ) (hd1 : δ < 1) (hα : 0 < α)
    (hmax : α < alphaMax (J1 Lc mu B) δ (mubar mu)) :
    α ≤ 1 / (2 * Lmax Lc) := by
  have hμ := mean_mu_pos h5
  have hL := max_pos h4 h5
  have hJ := native_J_pos h4 h5 hB
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb2 : 1 ≤ (B : ℝ) ^ 2 := by nlinarith
  have hF : 1 ≤ 1 + 4 * Real.sqrt (n : ℝ) * Real.sqrt (kappa Lc mu) := by
    have hh := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (Real.sqrt_nonneg (kappa Lc mu))
    nlinarith
  have hid : mubar mu * J1 Lc mu B =
      3 * Lmax Lc * (B : ℝ) ^ 2 * (1 + 4 * Real.sqrt (n : ℝ) * Real.sqrt (kappa Lc mu)) := by
    unfold J1 kappa
    field_simp
  unfold alphaMax at hmax
  have hh := (lt_div_iff₀ (mul_pos hμ hJ)).mp hmax
  rw [hid] at hh
  have hd : (1 - δ) ^ 2 ≤ 1 := by nlinarith
  have hbf : 1 ≤ (B : ℝ) ^ 2 * (1 + 4 * Real.sqrt (n : ℝ) * Real.sqrt (kappa Lc mu)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hF)]
  apply (le_div_iff₀ (show 0 < 2 * Lmax Lc by positivity)).2
  have hm := mul_nonneg (show 0 ≤ α * Lmax Lc by positivity) (sub_nonneg.mpr hbf)
  nlinarith only [hh, hd, hm]

end DIGing.Undir.DGFresh

-- Complete module: DGProof/GainArithmetic.lean

namespace DIGing.Undir.DGFresh

theorem geometric_sum_bounds {l : ℝ} {B : ℕ} (hl : 0 < l) (hl1 : l ≤ 1)
    (hB : 0 < B) :
    0 < (∑ j ∈ Finset.range B, l ^ j) ∧ (∑ j ∈ Finset.range B, l ^ j) ≤ (B : ℝ) := by
  constructor
  · exact Finset.sum_pos' (fun j _ => (pow_pos hl j).le)
      ⟨0, Finset.mem_range.mpr hB, by simp⟩
  · calc
      (∑ j ∈ Finset.range B, l ^ j) ≤ ∑ _j ∈ Finset.range B, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_one₀ hl.le hl1
      _ = B := by simp

theorem four_gain_strict {l δ α L κ N : ℝ} {B : ℕ}
    (hl : 0 < l) (hl1 : l < 1) (hlhalf : 1 / 2 ≤ l) (hd : δ < l ^ B)
    (hα : 0 < α) (hL : 0 < L) (_hκ : 0 ≤ κ) (hN : 1 ≤ N) (hB : 0 < B)
    (hstep : α * 2 * L * (B : ℝ) ^ 2 * (1 + 4 * Real.sqrt N * Real.sqrt κ) ≤
      (l ^ B - δ) ^ 2) :
    let S := ∑ j ∈ Finset.range B, l ^ j
    (L * (1 + 1 / l)) * (l * S / (l ^ B - δ)) *
      (α * S / (l ^ B - δ)) * (1 + 2 * Real.sqrt κ / l) < 1 := by
  dsimp only
  let S := ∑ j ∈ Finset.range B, l ^ j
  let F := 1 + 4 * Real.sqrt N * Real.sqrt κ
  have hg : 0 < l ^ B - δ := sub_pos.mpr hd
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨hS0, hSB⟩ := geometric_sum_bounds hl hl1.le hB
  change 0 < S at hS0
  change S ≤ (B : ℝ) at hSB
  have hn : 1 ≤ Real.sqrt N := (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith)).2 (by nlinarith)
  have hk := Real.sqrt_nonneg κ
  have hF : 0 < F := by dsimp [F]; positivity
  have hlast : 1 + 2 * Real.sqrt κ / l ≤ F := by
    have hdiv : 2 * Real.sqrt κ / l ≤ 4 * Real.sqrt κ := by
      apply (div_le_iff₀ hl).2
      nlinarith [mul_nonneg hk (show 0 ≤ l - 1 / 2 by linarith)]
    dsimp [F]
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hn)]
  have hlast0 : 0 ≤ 1 + 2 * Real.sqrt κ / l := by positivity
  have he : (L * (1 + 1 / l)) * (l * S / (l ^ B - δ)) *
      (α * S / (l ^ B - δ)) * (1 + 2 * Real.sqrt κ / l) =
      α * L * (1 + l) * S ^ 2 * (1 + 2 * Real.sqrt κ / l) / (l ^ B - δ) ^ 2 := by
    field_simp
    ring
  rw [he]
  apply (div_lt_one (sq_pos_of_pos hg)).2
  calc
    α * L * (1 + l) * S ^ 2 * (1 + 2 * Real.sqrt κ / l) ≤
        α * L * (1 + l) * (B : ℝ) ^ 2 * F := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      · exact hlast
      · exact hlast0
      · positivity
    _ < α * 2 * L * (B : ℝ) ^ 2 * F := by
      have hh := mul_lt_mul_of_pos_right (show 1 + l < 2 by linarith)
        (show 0 < α * L * (B : ℝ) ^ 2 * F by positivity)
      nlinarith only [hh]
    _ ≤ (l ^ B - δ) ^ 2 := hstep

theorem four_gain_bound {Q Z Y E g1 g2 g3 g4 w2 w3 w4 : ℝ}
    (hg2 : 0 ≤ g2) (hg3 : 0 ≤ g3) (hg4 : 0 ≤ g4)
    (hgain : g1 * g2 * g3 * g4 < 1)
    (h1 : Z ≤ g1 * Q) (h2 : Y ≤ g2 * Z + w2)
    (h3 : E ≤ g3 * Y + w3) (h4 : Q ≤ g4 * E + w4) :
    Q ≤ (g4 * g3 * w2 + g4 * w3 + w4) / (1 - g1 * g2 * g3 * g4) := by
  have hY := h2.trans (add_le_add (mul_le_mul_of_nonneg_left h1 hg2) le_rfl)
  have hE := h3.trans (add_le_add (mul_le_mul_of_nonneg_left hY hg3) le_rfl)
  have hQ := h4.trans (add_le_add (mul_le_mul_of_nonneg_left hE hg4) le_rfl)
  apply (le_div_iff₀ (sub_pos.mpr hgain)).2
  nlinarith only [hQ]

end DIGing.Undir.DGFresh

-- Complete module: DGProof/NativeGain.lean

namespace DIGing.Undir.DGFresh

theorem native_gain {n p B : ℕ} {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {Lc mu : Fin n → ℝ} (hp : 0 < p) (h4 : Assumption4 f Lc)
    (h5 : Assumption5 f mu) (hB : 0 < B) {δ α : ℝ}
    (hd0 : 0 ≤ δ) (hd1 : δ < 1) (hα : 0 < α)
    (hmax : α < alphaMax (J1 Lc mu B) δ (mubar mu)) :
    let l := rateLam (J1 Lc mu B) δ (mubar mu) α B
    let S := ∑ j ∈ Finset.range B, l ^ j
    (Lmax Lc * (1 + 1 / l)) * (l * S / (l ^ B - δ)) *
      (α * S / (l ^ B - δ)) * (1 + 2 * Real.sqrt (kappa Lc mu) / l) < 1 := by
  dsimp only
  have hμ := mean_mu_pos h5
  obtain ⟨hl0, hl1, hdl, _, hg⟩ := rate_guards (native_J_pos h4 h5 hB) hd0 hd1 hμ hα hB hmax
  have hhalf := (rate_quantitative (native_J_large hp h4 h5 hB) hd0 hd1 hμ hα hB hmax).1
  have he : α * 2 * Lmax Lc * (B : ℝ) ^ 2 *
      (1 + 4 * Real.sqrt (n : ℝ) * Real.sqrt (kappa Lc mu)) =
      α * mubar mu / (3 / 2) * J1 Lc mu B := by
    unfold J1 kappa
    field_simp
  apply four_gain_strict hl0 hl1 hhalf.le hdl hα (max_pos h4 h5)
    (le_trans (by norm_num) (kappa_ge_one hp h4 h5))
    (show (1 : ℝ) ≤ n by exact_mod_cast agents_pos h5) hB
  rw [he]
  exact hg

end DIGing.Undir.DGFresh

-- Complete module: DGProof/FiniteHorizon.lean

namespace DIGing.Undir.DGFresh

theorem erg_le {l C : ℝ} {K : ℕ} {a : ℕ → ℝ}
    (h : ∀ k, k ≤ K → a k / l ^ k ≤ C) : ergK l K a ≤ C := by
  apply Finset.sup'_le
  intro k hk
  exact h k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)

theorem le_erg {l : ℝ} {K k : ℕ} (a : ℕ → ℝ) (hk : k ≤ K) :
    a k / l ^ k ≤ ergK l K a := by
  exact Finset.le_sup' (f := fun j => a j / l ^ j) (by simpa using hk)

theorem value_le_erg {l : ℝ} (hl : 0 < l) {K k : ℕ}
    (a : ℕ → ℝ) (hk : k ≤ K) : a k ≤ ergK l K a * l ^ k := by
  exact (div_le_iff₀ (pow_pos hl k)).mp (le_erg a hk)

theorem erg_nonneg {l : ℝ} (hl : 0 < l) (K : ℕ) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) : 0 ≤ ergK l K a := by
  exact (div_nonneg (ha 0) (pow_pos hl 0).le).trans (le_erg a (Nat.zero_le K))

theorem erg_mono {l : ℝ} {K L : ℕ} {a : ℕ → ℝ} (h : K ≤ L) :
    ergK l K a ≤ ergK l L a :=
  erg_le fun _ hk => le_erg a (hk.trans h)

theorem erg_of_pointwise {l : ℝ} (hl : 0 < l) {K : ℕ} {a b : ℕ → ℝ}
    (h : ∀ k, k ≤ K → a k ≤ b k) : ergK l K a ≤ ergK l K b := by
  apply erg_le
  intro k hk
  exact (div_le_div_of_nonneg_right (h k hk) (pow_pos hl k).le).trans (le_erg b hk)

theorem erg_two_term {l A B : ℝ} (hl : 0 < l) {K : ℕ} {a b c : ℕ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : ∀ k, k ≤ K → a k ≤ A * b k + B * c k) :
    ergK l K a ≤ A * ergK l K b + B * ergK l K c := by
  apply erg_le
  intro k hk
  calc
    a k / l ^ k ≤ (A * b k + B * c k) / l ^ k :=
      div_le_div_of_nonneg_right (h k hk) (pow_pos hl k).le
    _ = A * (b k / l ^ k) + B * (c k / l ^ k) := by ring
    _ ≤ A * ergK l K b + B * ergK l K c :=
      add_le_add (mul_le_mul_of_nonneg_left (le_erg b hk) hA)
        (mul_le_mul_of_nonneg_left (le_erg c hk) hB)

end DIGing.Undir.DGFresh

-- Complete module: DGProof/BlockHorizon.lean

namespace DIGing.Undir.DGFresh

theorem block_erg_bound {l δ H : ℝ} {B K : ℕ} {a : ℕ → ℝ}
    (hl : 0 < l) (hB : 0 < B) (hd : 0 ≤ δ) (hgap : δ < l ^ B)
    (hH : 0 ≤ H) (ha : ∀ k, 0 ≤ a k)
    (hr : ∀ k, k + B ≤ K → a (k + B) ≤ δ * a k + H * l ^ k) :
    ergK l K a ≤ (H + l ^ B * ergK l (B - 1) a) / (l ^ B - δ) := by
  let A := ergK l K a
  let I := ergK l (B - 1) a
  have hA : 0 ≤ A := erg_nonneg hl K ha
  have hI : 0 ≤ I := erg_nonneg hl (B - 1) ha
  have hp : 0 < l ^ B := pow_pos hl B
  have hh : A ≤ δ / l ^ B * A + H / l ^ B + I := by
    apply erg_le
    intro n hn
    by_cases hnb : n < B
    · have hi : a n / l ^ n ≤ I := le_erg a (by omega)
      have hc : 0 ≤ δ / l ^ B * A + H / l ^ B := by positivity
      linarith
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show B ≤ n by omega)
      have hk : k ≤ K := by omega
      have hr' := hr k (by omega)
      rw [Nat.add_comm k B] at hr'
      have hv := value_le_erg hl a hk
      have hb : a (B + k) ≤ (δ * A + H) * l ^ k := by
        have hm := mul_le_mul_of_nonneg_left hv hd
        dsimp [A] at hm ⊢
        nlinarith
      have hdiv := (div_le_div_of_nonneg_right hb (pow_pos hl (B + k)).le)
      have he : ((δ * A + H) * l ^ k) / l ^ (B + k) = δ / l ^ B * A + H / l ^ B := by
        rw [pow_add]
        field_simp [ne_of_gt hl]
      rw [he] at hdiv
      linarith
  apply (le_div_iff₀ (sub_pos.mpr hgap)).2
  have hm := mul_le_mul_of_nonneg_right hh hp.le
  dsimp [A, I] at hm ⊢
  field_simp [ne_of_gt hp] at hm
  nlinarith

end DIGing.Undir.DGFresh

-- Complete module: DGProof/DrivenHorizon.lean

namespace DIGing.Undir.DGFresh

theorem source_window_le {l : ℝ} (hl : 0 < l) {B K k s : ℕ}
    (hs : s ≤ 1) (hk : k + B ≤ K) (b : ℕ → ℝ) :
    (∑ j ∈ Finset.range B, b (k + j + s)) ≤
      ergK l K b * l ^ k * (l ^ s * ∑ j ∈ Finset.range B, l ^ j) := by
  calc
    (∑ j ∈ Finset.range B, b (k + j + s)) ≤
        ∑ j ∈ Finset.range B, ergK l K b * l ^ (k + j + s) := by
      apply Finset.sum_le_sum
      intro j hj
      exact value_le_erg hl b (by have := Finset.mem_range.mp hj; omega)
    _ = ergK l K b * l ^ k * (l ^ s * ∑ j ∈ Finset.range B, l ^ j) := by
      simp only [pow_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem driven_block_erg {l δ c : ℝ} {B K s : ℕ} {a b : ℕ → ℝ}
    (hl : 0 < l) (hB : 0 < B) (hd : 0 ≤ δ) (hgap : δ < l ^ B)
    (hc : 0 ≤ c) (hs : s ≤ 1) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hr : ∀ k, a (k + B) ≤ δ * a k + c * ∑ j ∈ Finset.range B, b (k + j + s)) :
    ergK l K a ≤
      (c * l ^ s * (∑ j ∈ Finset.range B, l ^ j) / (l ^ B - δ)) * ergK l K b +
        l ^ B / (l ^ B - δ) * ergK l (B - 1) a := by
  let H := c * l ^ s * (∑ j ∈ Finset.range B, l ^ j) * ergK l K b
  have hH : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (by positivity) (erg_nonneg hl K hb)
  have hr' : ∀ k, k + B ≤ K → a (k + B) ≤ δ * a k + H * l ^ k := by
    intro k hk
    calc
      a (k + B) ≤ δ * a k + c * ∑ j ∈ Finset.range B, b (k + j + s) := hr k
      _ ≤ δ * a k + c * (ergK l K b * l ^ k *
          (l ^ s * ∑ j ∈ Finset.range B, l ^ j)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (source_window_le hl hs hk b) hc)
      _ = δ * a k + H * l ^ k := by dsimp [H]; ring
  have hbound := block_erg_bound hl hB hd hgap hH ha hr'
  calc
    ergK l K a ≤ (H + l ^ B * ergK l (B - 1) a) / (l ^ B - δ) := hbound
    _ = _ := by dsimp [H]; ring

theorem increment_erg {l L : ℝ} {K : ℕ} {z q : ℕ → ℝ}
    (hl : 0 < l) (hL : 0 ≤ L) (hq : ∀ k, 0 ≤ q k) (hz : z 0 = 0)
    (hs : ∀ k, z (k + 1) ≤ L * (q (k + 1) + q k)) :
    ergK l K z ≤ L * (1 + 1 / l) * ergK l K q := by
  have hQ := erg_nonneg hl K hq
  apply erg_le
  intro k hk
  cases k with
  | zero => simp only [hz, zero_div]; positivity
  | succ k =>
    have h1 := value_le_erg hl q hk
    have h2 := value_le_erg hl q (show k ≤ K by omega)
    apply (div_le_iff₀ (pow_pos hl (k + 1))).2
    calc
      z (k + 1) ≤ L * (q (k + 1) + q k) := hs k
      _ ≤ L * (ergK l K q * l ^ (k + 1) + ergK l K q * l ^ k) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hL
      _ = _ := by rw [pow_succ]; field_simp [ne_of_gt hl]

end DIGing.Undir.DGFresh

-- Complete module: DGProof/MaxHorizon.lean

namespace DIGing.Undir.DGFresh

theorem square_max_step {u v e q l s : ℝ} (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (he : 0 ≤ e) (hl : 0 ≤ l) (hs : 0 ≤ s) (hq : q ≤ l ^ 2)
    (h : u ^ 2 ≤ max (q * v ^ 2) (s ^ 2 * e ^ 2)) :
    u ≤ max (l * v) (s * e) := by
  have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg v)
  rcases le_total (q * v ^ 2) (s ^ 2 * e ^ 2) with hab | hba
  · rw [max_eq_right hab] at h
    have hse : 0 ≤ s * e := mul_nonneg hs he
    have hh : u ≤ s * e := by nlinarith
    exact hh.trans (le_max_right _ _)
  · rw [max_eq_left hba] at h
    have hlv : 0 ≤ l * v := mul_nonneg hl hv
    have hh : u ≤ l * v := by nlinarith
    exact hh.trans (le_max_left _ _)

theorem max_recurrence_erg {l s q : ℝ} {r e : ℕ → ℝ} {K : ℕ}
    (hl : 0 < l) (hs : 0 ≤ s) (hq : q ≤ l ^ 2)
    (hr : ∀ k, 0 ≤ r k) (he : ∀ k, 0 ≤ e k)
    (hstep : ∀ k, r (k + 1) ^ 2 ≤ max (q * r k ^ 2) (s ^ 2 * e k ^ 2)) :
    ergK l K r ≤ r 0 + s / l * ergK l K e := by
  let C := r 0 + s / l * ergK l K e
  have hE := erg_nonneg hl K he
  have hbound : ∀ k, k ≤ K → r k ≤ C * l ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [pow_zero, mul_one]
      dsimp [C]
      exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hs hl.le) hE)
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hi := value_le_erg hl e (show k ≤ K by omega)
      apply (square_max_step (hr (k + 1)) (hr k) (he k) hl.le hs hq (hstep k)).trans
      apply max_le
      · calc
          l * r k ≤ l * (C * l ^ k) := mul_le_mul_of_nonneg_left hprev hl.le
          _ = C * l ^ (k + 1) := by rw [pow_succ]; ring
      · have hh : s * ergK l K e ≤ C * l := by
          dsimp [C]
          have := mul_nonneg (hr 0) hl.le
          field_simp [ne_of_gt hl]
          nlinarith
        calc
          s * e k ≤ s * (ergK l K e * l ^ k) := mul_le_mul_of_nonneg_left hi hs
          _ = (s * ergK l K e) * l ^ k := by ring
          _ ≤ (C * l) * l ^ k := mul_le_mul_of_nonneg_right hh (pow_pos hl k).le
          _ = C * l ^ (k + 1) := by rw [pow_succ]; ring
  exact erg_le fun k hk => (div_le_iff₀ (pow_pos hl k)).2 (hbound k hk)

end DIGing.Undir.DGFresh

-- Complete module: DGProof/LastHorizon.lean

namespace DIGing.Undir.DGFresh

theorem last_horizon {l κ N q : ℝ} {K : ℕ} {r e Q : ℕ → ℝ}
    (hl : 0 < l) (hκ : 0 ≤ κ) (hN : 0 < N) (hq : q ≤ l ^ 2)
    (hr : ∀ k, 0 ≤ r k) (he : ∀ k, 0 ≤ e k)
    (hstep : ∀ k, r (k + 1) ^ 2 ≤ max (q * r k ^ 2) ((4 * κ / N) * e k ^ 2))
    (hQ : ∀ k, Q k ≤ e k + Real.sqrt N * r k) :
    ergK l K Q ≤ (1 + 2 * Real.sqrt κ / l) * ergK l K e + Real.sqrt N * r 0 := by
  have hs : (2 * Real.sqrt (κ / N)) ^ 2 = 4 * κ / N := by
    have hh := Real.sq_sqrt (div_nonneg hκ hN.le)
    rw [mul_pow, hh]
    ring
  have hb := max_recurrence_erg (K := K) hl (show 0 ≤ 2 * Real.sqrt (κ / N) by positivity)
    hq hr he (fun k => by rw [hs]; exact hstep k)
  have hc := erg_two_term hl (show (0 : ℝ) ≤ 1 by norm_num) (Real.sqrt_nonneg N)
    (fun k (_ : k ≤ K) => by simpa only [one_mul] using hQ k)
  simp only [one_mul] at hc
  have hm := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg N)
  have heq : Real.sqrt N * Real.sqrt (κ / N) = Real.sqrt κ := by
    rw [← Real.sqrt_mul hN.le]
    congr 1
    field_simp
  calc
    ergK l K Q ≤ ergK l K e + Real.sqrt N * ergK l K r := hc
    _ ≤ ergK l K e + Real.sqrt N * (r 0 + 2 * Real.sqrt (κ / N) / l * ergK l K e) :=
      add_le_add le_rfl hm
    _ = _ := by
      calc
        _ = (1 + 2 * (Real.sqrt N * Real.sqrt (κ / N)) / l) * ergK l K e + Real.sqrt N * r 0 := by ring
        _ = _ := by rw [heq]

end DIGing.Undir.DGFresh

-- Complete module: DGProof/SequenceConvergence.lean

namespace DIGing.Undir.DGFresh

theorem sequence_convergence {l δ α L κ N q : ℝ} {B : ℕ}
    {Q E Y Z r : ℕ → ℝ} (hl : 0 < l) (hB : 0 < B) (hd : 0 ≤ δ)
    (hgap : δ < l ^ B) (hα : 0 ≤ α) (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hN : 0 < N)
    (hq : q ≤ l ^ 2)
    (hQ0 : ∀ k, 0 ≤ Q k) (hE0 : ∀ k, 0 ≤ E k) (hY0 : ∀ k, 0 ≤ Y k)
    (hZ0 : ∀ k, 0 ≤ Z k) (hr0 : ∀ k, 0 ≤ r k)
    (hZinit : Z 0 = 0) (hZ : ∀ k, Z (k + 1) ≤ L * (Q (k + 1) + Q k))
    (hY : ∀ k, Y (k + B) ≤ δ * Y k + ∑ j ∈ Finset.range B, Z (k + j + 1))
    (hE : ∀ k, E (k + B) ≤ δ * E k + α * ∑ j ∈ Finset.range B, Y (k + j))
    (hr : ∀ k, r (k + 1) ^ 2 ≤ max (q * r k ^ 2) ((4 * κ / N) * E k ^ 2))
    (hQ : ∀ k, Q k ≤ E k + Real.sqrt N * r k)
    (hgain :
      let S := ∑ j ∈ Finset.range B, l ^ j
      (L * (1 + 1 / l)) * (l * S / (l ^ B - δ)) *
        (α * S / (l ^ B - δ)) * (1 + 2 * Real.sqrt κ / l) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, Q k ≤ C * l ^ k := by
  let S := ∑ j ∈ Finset.range B, l ^ j
  let g1 := L * (1 + 1 / l)
  let g2 := l * S / (l ^ B - δ)
  let g3 := α * S / (l ^ B - δ)
  let g4 := 1 + 2 * Real.sqrt κ / l
  let w2 := l ^ B / (l ^ B - δ) * ergK l (B - 1) Y
  let w3 := l ^ B / (l ^ B - δ) * ergK l (B - 1) E
  let w4 := Real.sqrt N * r 0
  let C0 := (g4 * g3 * w2 + g4 * w3 + w4) / (1 - g1 * g2 * g3 * g4)
  have hgap0 : 0 < l ^ B - δ := sub_pos.mpr hgap
  have hg2 : 0 ≤ g2 := by dsimp [g2, S]; positivity
  have hg3 : 0 ≤ g3 := by dsimp [g3, S]; positivity
  have hg4 : 0 ≤ g4 := by dsimp [g4]; positivity
  have hg : g1 * g2 * g3 * g4 < 1 := hgain
  have hbound : ∀ K, ergK l K Q ≤ C0 := by
    intro K
    have h1 : ergK l K Z ≤ g1 * ergK l K Q := increment_erg hl hL hQ0 hZinit hZ
    have h2 : ergK l K Y ≤ g2 * ergK l K Z + w2 := by
      have hh := driven_block_erg (K := K) (c := 1) (s := 1) hl hB hd hgap
        (by norm_num) (by omega) hY0 hZ0 (fun k => by simpa only [one_mul] using hY k)
      simpa only [one_mul, pow_one] using hh
    have h3 : ergK l K E ≤ g3 * ergK l K Y + w3 := by
      have hh := driven_block_erg (K := K) (c := α) (s := 0) hl hB hd hgap
        hα (by omega) hE0 hY0 (fun k => by simpa only [Nat.add_zero] using hE k)
      simpa only [pow_zero, mul_one] using hh
    have h4 : ergK l K Q ≤ g4 * ergK l K E + w4 :=
      last_horizon hl hκ hN hq hr0 hE0 hr hQ
    exact four_gain_bound hg2 hg3 hg4 hg h1 h2 h3 h4
  refine ⟨max 1 C0, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro k
  exact (value_le_erg hl Q le_rfl).trans
    (mul_le_mul_of_nonneg_right ((hbound k).trans (le_max_right _ _)) (pow_pos hl k).le)

end DIGing.Undir.DGFresh

-- Complete module: DGProof/Frobenius.lean

open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh

variable {n p : ℕ}

noncomputable def hilbertStack (v : Stack n p) : PiLp 2 (fun _ : Fin n => EuclideanSpace ℝ (Fin p)) := WithLp.toLp 2 v

lemma frob_nonneg (v : Stack n p) : 0 ≤ frob v := Real.sqrt_nonneg _

lemma frob_sq (v : Stack n p) : frob v ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma frob_eq_norm (v : Stack n p) : frob v = ‖hilbertStack v‖ := by
  have h := PiLp.norm_sq_eq_of_L2 _ (hilbertStack v)
  apply (sq_eq_sq₀ (frob_nonneg v) (norm_nonneg _)).mp
  simpa [frob_sq, hilbertStack] using h.symm

lemma frob_zero : frob (0 : Stack n p) = 0 := by simp [frob]

lemma frob_add_le (u v : Stack n p) : frob (u + v) ≤ frob u + frob v := by
  simpa only [frob_eq_norm, hilbertStack, WithLp.toLp_add] using norm_add_le (hilbertStack u) (hilbertStack v)

lemma frob_smul (a : ℝ) (v : Stack n p) : frob (a • v) = |a| * frob v := by
  simpa only [frob_eq_norm, hilbertStack, WithLp.toLp_smul, Real.norm_eq_abs] using norm_smul a (hilbertStack v)

lemma frob_neg (v : Stack n p) : frob (-v) = frob v := by
  simpa only [frob_eq_norm, hilbertStack, WithLp.toLp_neg] using norm_neg (hilbertStack v)

lemma frob_sub_le (u v : Stack n p) : frob (u - v) ≤ frob u + frob v := by
  simpa only [sub_eq_add_neg, frob_neg] using frob_add_le u (-v)

lemma frob_sum_le {ι : Type*} (s : Finset ι) (v : ι → Stack n p) :
    frob (∑ i ∈ s, v i) ≤ ∑ i ∈ s, frob (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frob_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (frob_add_le _ _).trans (add_le_add_right ih _)

lemma frob_le_of_sq_le (u v : Stack n p) (h : (∑ i, ‖u i‖^2) ≤ ∑ i, ‖v i‖^2) :
    frob u ≤ frob v := Real.sqrt_le_sqrt h

lemma frob_ones (z : EuclideanSpace ℝ (Fin p)) :
    frob (ones (n := n) z) = Real.sqrt n * ‖z‖ := by
  simp [frob, ones, Real.sqrt_mul]

end DIGing.Undir.DGFresh

-- Complete module: DGProof/Averages.lean

open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}

lemma avg_add (u v : Stack n p) : avg (u + v) = avg u + avg v := by
  simp [avg, Finset.sum_add_distrib, smul_add]
lemma avg_sub (u v : Stack n p) : avg (u - v) = avg u - avg v := by
  simp [avg, Finset.sum_sub_distrib, smul_sub]
lemma avg_smul (a : ℝ) (v : Stack n p) : avg (a • v) = a • avg v := by
  simp only [avg, Pi.smul_apply, ← Finset.smul_sum]
  exact smul_comm _ _ _
lemma avg_ones (hn : 0 < n) (z : EuclideanSpace ℝ (Fin p)) : avg (ones (n := n) z) = z := by
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [avg, ones, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, h]
lemma sum_cons (hn : 0 < n) (v : Stack n p) : ∑ i, cons v i = 0 := by
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [cons, ones, avg, Finset.sum_sub_distrib, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, h]
lemma cons_add (u v : Stack n p) : cons (u + v) = cons u + cons v := by
  ext i
  simp only [cons, avg_add, Pi.sub_apply, Pi.add_apply, ones]
  abel
lemma cons_sub (u v : Stack n p) : cons (u - v) = cons u - cons v := by
  ext i
  simp only [cons, avg_sub, Pi.sub_apply, ones]
  abel
lemma cons_smul (a : ℝ) (v : Stack n p) : cons (a • v) = a • cons v := by
  ext i
  simp [cons, avg_smul, ones, smul_sub]
lemma cons_ones (hn : 0 < n) (z : EuclideanSpace ℝ (Fin p)) : cons (ones (n := n) z) = 0 := by
  simp [cons, avg_ones hn]
lemma cons_idem (hn : 0 < n) (v : Stack n p) : cons (cons v) = cons v := by
  change cons (v - ones (avg v)) = cons v
  rw [cons_sub, cons_ones hn, sub_zero]

lemma variance_identity (hn : 0 < n) (v : Stack n p) (z : EuclideanSpace ℝ (Fin p)) :
    (∑ i, ‖v i - z‖^2) = (∑ i, ‖cons v i‖^2) + (n : ℝ)*‖avg v - z‖^2 := by
  have hi : ∀ i, v i - z = cons v i + (avg v - z) := by
    intro i
    simp only [cons, Pi.sub_apply, ones]
    abel
  simp_rw [hi, norm_add_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← sum_inner, sum_cons hn]
  simp

lemma frob_cons_le (hn : 0 < n) (v : Stack n p) : frob (cons v) ≤ frob v := by
  have hv := variance_identity hn v 0
  simp only [sub_zero] at hv
  apply (sq_le_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
  rw [frob_sq, frob_sq]
  nlinarith [sq_nonneg ‖avg v‖]

lemma error_decomposition (v : Stack n p) (z : EuclideanSpace ℝ (Fin p)) :
    frob (v - ones z) ≤ frob (cons v) + Real.sqrt n * ‖avg v - z‖ := by
  have he : v - ones z = cons v + ones (avg v - z) := by
    ext i
    simp only [cons, Pi.sub_apply, Pi.add_apply, ones]
    abel
  rw [he]
  exact (frob_add_le _ _).trans_eq (by rw [frob_ones])
end DIGing.Undir.DGFresh

-- Complete module: DGProof/MixingAlgebra.lean
open scoped BigOperators
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma mix_add (M : Matrix (Fin n) (Fin n) ℝ) (u v : Stack n p) :
    mix M (u + v) = mix M u + mix M v := by
  ext i j
  simp [mix, smul_add, Finset.sum_add_distrib]
lemma mix_sub (M : Matrix (Fin n) (Fin n) ℝ) (u v : Stack n p) :
    mix M (u - v) = mix M u - mix M v := by
  ext i j
  simp [mix, smul_sub, Finset.sum_sub_distrib]
lemma mix_smul (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (v : Stack n p) :
    mix M (a • v) = a • mix M v := by
  funext i
  simp only [mix, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _
lemma mix_one (v : Stack n p) : mix 1 v = v := by
  ext i
  simp [mix, Matrix.one_apply, ite_smul]
lemma mix_mul (M N : Matrix (Fin n) (Fin n) ℝ) (v : Stack n p) :
    mix (M * N) v = mix M (mix N v) := by
  ext i
  simp only [mix, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
lemma mix_ones (M : Matrix (Fin n) (Fin n) ℝ) (hr : ∀ i, ∑ j, M i j = 1)
    (z : EuclideanSpace ℝ (Fin p)) : mix M (ones z) = ones z := by
  ext i
  simp only [mix, ones, ← Finset.sum_smul, hr, one_smul]
lemma avg_mix (M : Matrix (Fin n) (Fin n) ℝ) (hc : ∀ j, ∑ i, M i j = 1)
    (v : Stack n p) : avg (mix M v) = avg v := by
  simp only [avg, mix]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hc, one_smul]
lemma cons_mix (M : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, ∑ j, M i j = 1) (hc : ∀ j, ∑ i, M i j = 1) (v : Stack n p) :
    cons (mix M v) = mix M (cons v) := by
  simp only [cons, mix_sub, avg_mix M hc, mix_ones M hr]
lemma mix_avgMat (v : Stack n p) : mix (avgMat n) v = ones (avg v) := by
  ext i
  simp [mix, avgMat, ones, avg, Finset.smul_sum]
lemma mix_matrix_sub (M N : Matrix (Fin n) (Fin n) ℝ) (v : Stack n p) :
    mix (M - N) v = mix M v - mix N v := by
  ext i
  simp [mix, sub_smul, Finset.sum_sub_distrib]
end DIGing.Undir.DGFresh

-- Complete module: DGProof/MixingNorm.lean
open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}

lemma weighted_square (w : Fin n → ℝ) (v : Stack n p) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) : ‖∑ i, w i • v i‖^2 ≤ ∑ i, w i * ‖v i‖^2 := by
  let m := ∑ i, w i • v i
  have hp : 0 ≤ ∑ i, w i * ‖v i-m‖^2 := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have he : (∑ i, w i * ‖v i-m‖^2) = (∑ i, w i*‖v i‖^2) - ‖m‖^2 := by
    simp only [norm_sub_sq_real, mul_sub, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
    have hi : (∑ i, w i * (2 * inner ℝ (v i) m)) = 2*‖m‖^2 := by
      calc
        _ = 2 * inner ℝ (∑ i, w i • v i) m := by simp [sum_inner, real_inner_smul_left, Finset.mul_sum]; ring
        _ = 2 * ‖m‖^2 := by rw [real_inner_self_eq_norm_sq]
    rw [hi]
    ring
  rw [he] at hp
  dsimp [m] at hp
  linarith

lemma mix_nonexpansive (M : Matrix (Fin n) (Fin n) ℝ)
    (hp : ∀ i j, 0 ≤ M i j) (hr : ∀ i, ∑ j, M i j = 1)
    (hc : ∀ j, ∑ i, M i j = 1) (v : Stack n p) : frob (mix M v) ≤ frob v := by
  apply frob_le_of_sq_le
  calc
    _ ≤ ∑ i, ∑ j, M i j * ‖v j‖^2 := Finset.sum_le_sum fun i _ => weighted_square (M i) v (hp i) (hr i)
    _ = ∑ j, ‖v j‖^2 := by rw [Finset.sum_comm]; simp only [← Finset.sum_mul, hc, one_mul]

noncomputable def column (v : Stack n p) (j : Fin p) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => v i j)

lemma column_norm_sum (v : Stack n p) : (∑ j, ‖column v j‖^2) = frob v^2 := by
  rw [frob_sq]
  simp only [EuclideanSpace.real_norm_sq_eq, column]
  rw [Finset.sum_comm]

lemma column_mix (M : Matrix (Fin n) (Fin n) ℝ) (v : Stack n p) (j : Fin p) :
    column (mix M v) j = Matrix.toEuclideanCLM (𝕜 := ℝ) M (column v j) := by
  ext i
  simp [column, mix, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct]

lemma mix_opNorm (M : Matrix (Fin n) (Fin n) ℝ) (v : Stack n p) :
    frob (mix M v) ≤ sigmaMax M * frob v := by
  have hs : ∀ j, ‖column (mix M v) j‖^2 ≤ (sigmaMax M)^2*‖column v j‖^2 := by
    intro j
    rw [column_mix]
    have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm (column v j)
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h |>.trans_eq (mul_pow _ _ 2)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hs j)
  rw [column_norm_sum, ← Finset.mul_sum, column_norm_sum] at hsum
  apply (sq_le_sq₀ (frob_nonneg _) (mul_nonneg (norm_nonneg _) (frob_nonneg _))).mp
  simpa only [mul_pow, sigmaMax] using hsum
end DIGing.Undir.DGFresh

-- Complete module: DGProof/BlockMixing.lean
open scoped BigOperators
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}

def blockProduct (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | b+1 => W (k+b) * blockProduct W k b

lemma blockProduct_eq (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (k b : ℕ) :
    blockProduct W k b = prodW W b (k+b-1) := by
  induction b with
  | zero => simp [blockProduct, prodW]
  | succ b ih =>
    simp only [blockProduct, prodW, List.ofFn_succ, List.prod_cons]
    have hkb : k+(b+1)-1 = k+b := by omega
    rw [hkb]
    simp only [Fin.val_zero, Nat.zero_le, if_true, Nat.sub_zero]
    rw [ih, prodW]
    congr 1
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext t
    simp only [Fin.val_succ]
    split_ifs <;> congr 1 <;> omega

lemma forced_block_error (W : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n))
    (v d : ℕ → Stack n p) (hv : ∀ k, v (k+1)= mix (W k) (v k)+d k) (k b : ℕ) :
    frob (v (k+b)-mix (blockProduct W k b) (v k)) ≤ ∑ j ∈ Finset.range b, frob (d (k+j)) := by
  induction b with
  | zero => simp [blockProduct, mix_one, frob_zero]
  | succ b ih =>
    rw [Nat.add_succ, hv, blockProduct, mix_mul]
    have he : mix (W (k+b)) (v (k+b)) + d (k+b) - mix (W (k+b)) (mix (blockProduct W k b) (v k)) =
        mix (W (k+b)) (v (k+b)-mix (blockProduct W k b) (v k)) + d (k+b) := by rw [mix_sub]; abel
    rw [he, Finset.sum_range_succ]
    apply (frob_add_le _ _).trans
    apply add_le_add_left
    exact (mix_nonexpansive _ (fun _ _ => nonneg_of_mem_doublyStochastic (hW _))
      (sum_row_of_mem_doublyStochastic (hW _))
      (sum_col_of_mem_doublyStochastic (hW _)) _).trans ih

lemma forced_block_bound (_hn : 0 < n) (W : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n)) (B : ℕ) (δ : ℝ)
    (hδ : ∀ k, B-1 ≤ k → deltaK W B k ≤ δ)
    (v d : ℕ → Stack n p) (hc : ∀ k, avg (v k)=0)
    (hv : ∀ k, v (k+1)= mix (W k) (v k)+d k) (k : ℕ) :
    frob (v (k+B)) ≤ δ*frob (v k) + ∑ j ∈ Finset.range B, frob (d (k+j)) := by
  have hm : mix (blockProduct W k B) (v k) = mix (prodW W B (k+B-1)-avgMat n) (v k) := by
    rw [mix_matrix_sub, mix_avgMat, hc, blockProduct_eq]
    change _ = _ - (0 : Stack n p)
    rw [sub_zero]
  have h1 := mix_opNorm (prodW W B (k+B-1)-avgMat n) (v k)
  have h2 := hδ (k+B-1) (by omega)
  have h3 := forced_block_error W hW v d hv k B
  calc
    frob (v (k+B)) ≤ frob (v (k+B)-mix (blockProduct W k B) (v k)) + frob (mix (blockProduct W k B) (v k)) := by
      simpa only [sub_add_cancel] using frob_add_le (v (k+B)-mix (blockProduct W k B) (v k)) (mix (blockProduct W k B) (v k))
    _ ≤ (∑ j ∈ Finset.range B, frob (d (k+j))) + δ*frob (v k) := by
      apply add_le_add h3
      rw [hm]
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (frob_nonneg _))
    _ = _ := by ring
end DIGing.Undir.DGFresh

-- Complete module: DGProof/RunIdentities.lean
open scoped BigOperators
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma delta_guards {E : ℕ → SimpleGraph (Fin n)} {W : ℕ → Matrix (Fin n) (Fin n) ℝ} {B : ℕ}
    (h1 : Assumption1 E W B) {δ : ℝ}
    (hδ : IsLUB {d | ∃ k, B-1 ≤ k ∧ d=deltaK W B k} δ) : 0 ≤ δ ∧ δ < 1 := by
  have hm : deltaK W B (B-1) ∈ {d | ∃ k, B-1 ≤ k ∧ d=deltaK W B k} := ⟨B-1, le_rfl, rfl⟩
  refine ⟨(norm_nonneg _).trans (hδ.1 hm), ?_⟩
  obtain ⟨c,hc,hbound⟩ := h1.2.2.2
  exact (hδ.2 (fun d ⟨k,hk,hd⟩ => hd ▸ hbound k hk)).trans_lt hc
lemma avg_gradient_invariant {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {W : ℕ → Matrix (Fin n) (Fin n) ℝ} {α : ℝ} {x y : ℕ → Stack n p}
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n)) (hr : IsDIGingRun f W α x y) (k : ℕ) :
    avg (y k) = avg (gradStack f (x k)) := by
  induction k with
  | zero => rw [hr.1]
  | succ k ih =>
    rw [(hr.2 k).2, avg_sub, avg_add, avg_mix _ (sum_col_of_mem_doublyStochastic (hW k)), ih]
    abel
lemma average_step {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {W : ℕ → Matrix (Fin n) (Fin n) ℝ} {α : ℝ} {x y : ℕ → Stack n p}
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n)) (hr : IsDIGingRun f W α x y) (k : ℕ) :
    avg (x (k+1))=avg (x k)-α • avg (gradStack f (x k)) := by
  rw [(hr.2 k).1, avg_sub, avg_smul, avg_mix _ (sum_col_of_mem_doublyStochastic (hW k)), avg_gradient_invariant hW hr]
lemma cons_average_zero (hn : 0 < n) (v : Stack n p) : avg (cons v)=0 := by
  simp only [avg, sum_cons hn, smul_zero]
lemma cons_run_x {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {W : ℕ → Matrix (Fin n) (Fin n) ℝ} {α : ℝ} {x y : ℕ → Stack n p}
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n)) (hr : IsDIGingRun f W α x y) (k : ℕ) :
    cons (x (k+1))= mix (W k) (cons (x k)) + (-α) • cons (y k) := by
  rw [(hr.2 k).1, cons_sub, cons_smul, cons_mix _
    (sum_row_of_mem_doublyStochastic (hW k)) (sum_col_of_mem_doublyStochastic (hW k))]
  module
lemma cons_run_y {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {W : ℕ → Matrix (Fin n) (Fin n) ℝ} {α : ℝ} {x y : ℕ → Stack n p}
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n)) (hr : IsDIGingRun f W α x y) (k : ℕ) :
    cons (y (k+1))= mix (W k) (cons (y k)) + cons (gradStack f (x (k+1))-gradStack f (x k)) := by
  rw [(hr.2 k).2, cons_sub, cons_add, cons_sub, cons_mix _
    (sum_row_of_mem_doublyStochastic (hW k)) (sum_col_of_mem_doublyStochastic (hW k))]
  abel
end DIGing.Undir.DGFresh

-- Complete module: DGProof/GradientBound.lean
open scoped BigOperators
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma gradient_frob_bound {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (x y : Stack n p) :
    frob (gradStack f x-gradStack f y) ≤ Lmax Lc * frob (x-y) := by
  have hL := max_pos h4 h5
  have hi (i : Fin n) : ‖gradient (f i) (x i)-gradient (f i) (y i)‖^2 ≤ (Lmax Lc)^2*‖x i-y i‖^2 := by
    have h := ((h4 i).2.2 (x i) (y i)).trans
      (mul_le_mul_of_nonneg_right (Lc_le_max Lc i) (norm_nonneg _))
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg _))).mpr h
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hi i
  apply (sq_le_sq₀ (frob_nonneg _) (mul_nonneg hL.le (frob_nonneg _))).mp
  simpa only [mul_pow, frob_sq, gradStack, Pi.sub_apply, Finset.mul_sum] using hs
lemma gradient_error_bound {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (x y : Stack n p) (z : EuclideanSpace ℝ (Fin p)) :
    frob (gradStack f x-gradStack f y) ≤ Lmax Lc * (frob (x-ones z)+frob (y-ones z)) := by
  apply (gradient_frob_bound h4 h5 x y).trans
  apply mul_le_mul_of_nonneg_left _ (max_pos h4 h5).le
  have he : x-y=(x-ones z)-(y-ones z) := by abel
  rw [he]
  exact frob_sub_le _ _
end DIGing.Undir.DGFresh

-- Complete module: DGProof/RunBounds.lean
open scoped BigOperators
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma run_block_y {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {W : ℕ → Matrix (Fin n) (Fin n) ℝ} {α δ : ℝ} {x y : ℕ → Stack n p} {B : ℕ}
    (hn : 0 < n) (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n))
    (hδ : ∀ k, B-1 ≤ k → deltaK W B k ≤ δ) (hr : IsDIGingRun f W α x y) (k : ℕ) :
    frob (cons (y (k+B))) ≤ δ*frob (cons (y k)) +
      ∑ j ∈ Finset.range B, frob (zSeq f x (k+j+1)) := by
  have h := forced_block_bound hn W hW B δ hδ (fun k => cons (y k))
    (fun k => cons (gradStack f (x (k+1))-gradStack f (x k)))
    (fun k => cons_average_zero hn _) (cons_run_y hW hr) k
  apply h.trans
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j _
  simpa only [zSeq, Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel] using frob_cons_le hn (gradStack f (x (k+j+1))-gradStack f (x (k+j)))
lemma run_block_x {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    {W : ℕ → Matrix (Fin n) (Fin n) ℝ} {α δ : ℝ} {x y : ℕ → Stack n p} {B : ℕ}
    (hn : 0 < n) (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n))
    (hδ : ∀ k, B-1 ≤ k → deltaK W B k ≤ δ) (hr : IsDIGingRun f W α x y)
    (hα : 0 ≤ α) (k : ℕ) :
    frob (cons (x (k+B))) ≤ δ*frob (cons (x k)) + α *
      ∑ j ∈ Finset.range B, frob (cons (y (k+j))) := by
  have h := forced_block_bound hn W hW B δ hδ (fun k => cons (x k))
    (fun k => (-α) • cons (y k)) (fun k => cons_average_zero hn _) (cons_run_x hW hr) k
  simpa only [frob_smul, abs_neg, abs_of_nonneg hα, Finset.mul_sum] using h
lemma run_z_zero (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x : ℕ → Stack n p) :
    frob (zSeq f x 0)=0 := by simp [zSeq, frob_zero]
lemma run_z_bound {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (x : ℕ → Stack n p)
    (z : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    frob (zSeq f x (k+1)) ≤ Lmax Lc * (frob (x (k+1)-ones z)+frob (x k-ones z)) := by
  simpa [zSeq] using gradient_error_bound h4 h5 (x (k+1)) (x k) z
end DIGing.Undir.DGFresh

-- Complete module: DGProof/ObjectiveGeometry.lean
open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma objective_hasGradient {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (z : EuclideanSpace ℝ (Fin p)) :
    HasGradientAt (objective f) (avg (gradStack f (ones z))) z := by
  have h := (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => ((h4 i).2.1 z).hasFDerivAt)).const_mul (1/(n:ℝ))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [avg, gradStack, ones]
lemma objective_strong {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {mu : Fin n → ℝ}
    (h5 : Assumption5 f mu) (x z : EuclideanSpace ℝ (Fin p)) :
    objective f z + inner ℝ (avg (gradStack f (ones z))) (x-z) + mubar mu/2*‖x-z‖^2 ≤ objective f x := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h5.2.2 i x z)
  have hn : 0 ≤ (1/(n:ℝ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left h hn
  simpa [objective, avg, gradStack, ones, mubar, sum_inner, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum, mul_add, real_inner_smul_left, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hh
lemma objective_gap {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (z : EuclideanSpace ℝ (Fin p))
    (hz : ∀ x, objective f z ≤ objective f x) (x : EuclideanSpace ℝ (Fin p)) :
    mubar mu/2*‖x-z‖^2 ≤ objective f x-objective f z := by
  have hl : IsLocalMin (objective f) z := Filter.Eventually.of_forall hz
  have hg := objective_hasGradient h4 z
  have hzero : avg (gradStack f (ones z)) = 0 := by
    apply (InnerProductSpace.toDual ℝ _).injective
    rw [← hg.hasFDerivAt.fderiv, hl.fderiv_eq_zero, map_zero]
  have h := objective_strong h5 x z
  rw [hzero, inner_zero_left, add_zero] at h
  linarith
end DIGing.Undir.DGFresh

-- Complete module: DGProof/IGDGeometry.lean
open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {p : ℕ}
lemma norm_add_sq_le_two (a b : EuclideanSpace ℝ (Fin p)) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  rw [norm_add_sq_real]
  have h := sq_nonneg ‖a-b‖
  rw [norm_sub_sq_real] at h
  linarith
lemma norm_lower_three (s a z : EuclideanSpace ℝ (Fin p)) :
    (2/3:ℝ)*‖a-z‖^2-2*‖a-s‖^2 ≤ ‖s-z‖^2 := by
  have he : a-z = (a-s)+(s-z) := by abel
  have ht := norm_add_le (a-s) (s-z)
  rw [← he] at ht
  have hs := sq_le_sq₀ (norm_nonneg (a-z)) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr ht
  nlinarith [sq_nonneg (‖s-z‖-2*‖a-s‖)]
lemma gradient_step_identity (a b z g : EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (hb : b=a-α • g) :
    2*α*inner ℝ g (b-z) = ‖a-z‖^2-‖b-z‖^2-‖b-a‖^2 := by
  have he : a-z = (b-z)+(a-b) := by abel
  have hd : a-b = α • g := by rw [hb]; module
  have hn : ‖b-a‖ = ‖a-b‖ := norm_sub_rev _ _
  rw [he, norm_add_sq_real, hn, hd, real_inner_smul_right, real_inner_comm (b-z) g]
  ring
end DIGing.Undir.DGFresh

-- Complete module: DGProof/IGDPointwise.lean
open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma local_igd_bound {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (hm : ∀ i, mu i ≤ Lc i)
    (i : Fin n) (s a b z : EuclideanSpace ℝ (Fin p)) :
    f i b-f i z ≤ inner ℝ (gradient (f i) s) (b-z) + Lmax Lc*‖b-a‖^2 +
      2*Lmax Lc*‖a-s‖^2 - mu i/3*‖a-z‖^2 := by
  have h1 := smooth_descent (f i) (Lc i) (h4 i).2.1 (h4 i).2.2 s b
  have h2 := h5.2.2 i z s
  have h3 := norm_add_sq_le_two (b-a) (a-s)
  rw [show b-a+(a-s)=b-s by abel] at h3
  have h4' := norm_lower_three s a z
  have hn : ‖z-s‖=‖s-z‖ := norm_sub_rev _ _
  rw [hn] at h2
  have hinner : inner ℝ (gradient (f i) s) (b-s) - inner ℝ (gradient (f i) s) (z-s) =
      inner ℝ (gradient (f i) s) (b-z) := by
    rw [← inner_sub_right]
    congr 1
    module
  have hL := Lc_le_max Lc i
  have hμ := h5.1 i
  have hm' := (hm i).trans hL
  have hA := mul_le_mul_of_nonneg_left h3 (le_of_lt (h4 i).1)
  have hB := mul_le_mul_of_nonneg_left h4' hμ
  have hC := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖b-a‖)
  have hD := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖a-s‖)
  have hE := mul_le_mul_of_nonneg_right hm' (sq_nonneg ‖a-s‖)
  nlinarith only [h1,h2,hinner,hA,hB,hC,hD,hE]

lemma igd_mean_bound {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (hm : ∀ i, mu i ≤ Lc i)
    (s : Stack n p) (b z : EuclideanSpace ℝ (Fin p)) :
    objective f b-objective f z ≤ inner ℝ (avg (gradStack f s)) (b-z) +
      Lmax Lc*‖b-avg s‖^2 + (2*Lmax Lc/(n:ℝ))*frob (cons s)^2 -
      mubar mu/3*‖avg s-z‖^2 := by
  have hn : (0:ℝ)<n := by exact_mod_cast agents_pos h5
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => local_igd_bound h4 h5 hm i (s i) (avg s) b z)
  have hh := mul_le_mul_of_nonneg_left h (le_of_lt (one_div_pos.mpr hn))
  have hc : ∀ i, ‖avg s-s i‖^2 = ‖cons s i‖^2 := by intro i; rw [norm_sub_rev]; rfl
  simp_rw [hc] at hh
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul, ← sum_inner] at hh
  rw [frob_sq]
  dsimp [objective, avg, gradStack, mubar]
  rw [real_inner_smul_left]
  simp only [avg, ← Finset.sum_div] at hh
  have he : (1/(n:ℝ)) * (inner ℝ (∑ i, gradient (f i) (s i)) (b-z) + (n:ℝ)*(Lmax Lc*‖b-(1/(n:ℝ)) • ∑ i, s i‖^2) + 2*Lmax Lc*(∑ i, ‖cons s i‖^2) - ((∑ i, mu i)/3)*‖(1/(n:ℝ)) • ∑ i, s i-z‖^2) =
      (1/(n:ℝ))*inner ℝ (∑ i, gradient (f i) (s i)) (b-z) + Lmax Lc*‖b-(1/(n:ℝ)) • ∑ i, s i‖^2 + (2*Lmax Lc/(n:ℝ))*(∑ i, ‖cons s i‖^2) - ((1/(n:ℝ))*(∑ i, mu i))/3*‖(1/(n:ℝ)) • ∑ i, s i-z‖^2 := by
    field_simp [ne_of_gt hn]
  rw [he] at hh
  nlinarith only [hh]
end DIGing.Undir.DGFresh

-- Complete module: DGProof/IGDRecurrence.lean
open scoped BigOperators RealInnerProductSpace
namespace DIGing.Undir.DGFresh
variable {n p : ℕ}
lemma igd_squared {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (hm : ∀ i, mu i ≤ Lc i)
    {α : ℝ} (hα : 0 < α) (hstep : α ≤ 1/(2*Lmax Lc))
    (s : Stack n p) (b z : EuclideanSpace ℝ (Fin p))
    (hb : b=avg s-α • avg (gradStack f s)) :
    ‖b-z‖^2 ≤ (1-2*α*mubar mu/3)*‖avg s-z‖^2 - 2*α*(objective f b-objective f z) +
      (4*α*Lmax Lc/(n:ℝ))*frob (cons s)^2 := by
  have hL := max_pos h4 h5
  have hs : 2*α*Lmax Lc ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hL)).mp hstep
    nlinarith
  have h := igd_mean_bound h4 h5 hm s b z
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*α by positivity)
  have hid := gradient_step_identity (avg s) b z (avg (gradStack f s)) α hb
  have hdrop := mul_nonneg (show 0 ≤ 1-2*α*Lmax Lc by linarith) (sq_nonneg ‖b-avg s‖)
  have he : 2*α*(2*Lmax Lc/(n:ℝ)) = 4*α*Lmax Lc/(n:ℝ) := by ring
  nlinarith only [hh,hid,hdrop,he]
lemma igd_max_recurrence {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lc mu : Fin n → ℝ}
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu) (hm : ∀ i, mu i ≤ Lc i)
    {α : ℝ} (hα : 0 < α) (hstep : α ≤ 1/(2*Lmax Lc))
    (s : Stack n p) (b z : EuclideanSpace ℝ (Fin p))
    (hz : ∀ v, objective f z ≤ objective f v)
    (hb : b=avg s-α • avg (gradStack f s)) :
    ‖b-z‖^2 ≤ max ((1-2*α*mubar mu/3)*‖avg s-z‖^2)
      ((4*kappa Lc mu/(n:ℝ))*frob (cons s)^2) := by
  have h := igd_squared h4 h5 hm hα hstep s b z hb
  have hg := objective_gap h4 h5 z hz b
  have hμ := mean_mu_pos h5
  have hm0 : 0 < α*mubar mu := mul_pos hα hμ
  have hgg := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*α by positivity)
  have he : α*mubar mu*(4*kappa Lc mu/(n:ℝ)) = 4*α*Lmax Lc/(n:ℝ) := by
    dsimp [kappa]
    field_simp [ne_of_gt hμ]
  by_cases hsmall : ‖b-z‖^2 ≤ (4*kappa Lc mu/(n:ℝ))*frob (cons s)^2
  · exact hsmall.trans (le_max_right _ _)
  · have hc := mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) hm0.le
    rw [← mul_assoc, he] at hc
    have hbnd : ‖b-z‖^2 ≤ (1-2*α*mubar mu/3)*‖avg s-z‖^2 := by nlinarith only [h,hgg,hc]
    exact hbnd.trans (le_max_left _ _)
end DIGing.Undir.DGFresh

-- Complete module: DGProof/NativeConclusion.lean

namespace DIGing.Undir.DGFresh

theorem native_theorem_10 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc mu : Fin n → ℝ)
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu)
    (xstar : EuclideanSpace ℝ (Fin p)) (hopt : ∀ z, objective f xstar ≤ objective f z)
    (E : ℕ → SimpleGraph (Fin n)) (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (B : ℕ)
    (h1 : Assumption1 E W B)
    (δ : ℝ) (hδ : IsLUB {d | ∃ k, B - 1 ≤ k ∧ d = deltaK W B k} δ)
    (α : ℝ) (hα : 0 < α) (hαmax : α < alphaMax (J1 Lc mu B) δ (mubar mu))
    (x y : ℕ → Stack n p) (hrun : IsDIGingRun f W α x y) :
    0 < rateLam (J1 Lc mu B) δ (mubar mu) α B ∧ rateLam (J1 Lc mu B) δ (mubar mu) α B < 1 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
        frob (x k - ones xstar) ≤ C * rateLam (J1 Lc mu B) δ (mubar mu) α B ^ k := by
  have hn := agents_pos h5
  have hB := h1.2.2.1
  have hμ := mean_mu_pos h5
  have hL := max_pos h4 h5
  have hJ := native_J_pos h4 h5 hB
  obtain ⟨hd0, hd1⟩ := delta_guards h1 hδ
  let l := rateLam (J1 Lc mu B) δ (mubar mu) α B
  obtain ⟨hl0, hl1, hdl, _, _⟩ := rate_guards hJ hd0 hd1 hμ hα hB hαmax
  refine ⟨hl0, hl1, ?_⟩
  by_cases hp : p = 0
  · subst p
    refine ⟨1, zero_lt_one, ?_⟩
    intro k
    rw [show x k - ones xstar = 0 from Subsingleton.elim _ _, frob_zero]
    positivity
  · have hp' : 0 < p := Nat.pos_of_ne_zero hp
    have hstep := native_step_bound h4 h5 hB hd0 hd1 hα hαmax
    have hquant := rate_quantitative (native_J_large hp' h4 h5 hB) hd0 hd1 hμ hα hB hαmax
    have hq : 1 - 2 * α * mubar mu / 3 ≤ l ^ 2 := by
      calc
        1 - 2 * α * mubar mu / 3 = 1 - α * mubar mu / (3 / 2) := by ring
        _ ≤ l ^ 2 := hquant.2
    have hdb : ∀ k, B - 1 ≤ k → deltaK W B k ≤ δ :=
      fun k hk => hδ.1 ⟨k, hk, rfl⟩
    apply sequence_convergence
      (Q := fun k => frob (x k - ones xstar))
      (E := fun k => frob (cons (x k)))
      (Y := fun k => frob (cons (y k)))
      (Z := fun k => frob (zSeq f x k))
      (r := fun k => ‖avg (x k) - xstar‖)
      (L := Lmax Lc) (κ := kappa Lc mu) (N := (n : ℝ))
      (q := 1 - 2 * α * mubar mu / 3)
      hl0 hB hd0 hdl hα.le hL.le (div_pos hL hμ).le
      (show (0 : ℝ) < n by exact_mod_cast hn) hq
      (fun _ => frob_nonneg _) (fun _ => frob_nonneg _)
      (fun _ => frob_nonneg _) (fun _ => frob_nonneg _) (fun _ => norm_nonneg _)
      (run_z_zero f x) (run_z_bound h4 h5 x xstar)
      (run_block_y hn h1.2.1 hdb hrun)
      (run_block_x hn h1.2.1 hdb hrun hα.le)
    · intro k
      exact igd_max_recurrence h4 h5 (mu_le_Lc hp' h4 h5) hα hstep
        (x k) (avg (x (k + 1))) xstar hopt (average_step h1.2.1 hrun k)
    · exact fun k => error_decomposition (x k) xstar
    · exact native_gain hp' h4 h5 hB hd0 hd1 hα hαmax

end DIGing.Undir.DGFresh

-- Complete module: DGProof/FinalRoot.lean

namespace DIGing.Undir

theorem theorem_10 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc mu : Fin n → ℝ)
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu)
    (xstar : EuclideanSpace ℝ (Fin p)) (hopt : ∀ z, objective f xstar ≤ objective f z)
    (E : ℕ → SimpleGraph (Fin n)) (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (B : ℕ)
    (h1 : Assumption1 E W B)
    (δ : ℝ) (hδ : IsLUB {d | ∃ k, B - 1 ≤ k ∧ d = deltaK W B k} δ)
    (α : ℝ) (hα : 0 < α) (hαmax : α < alphaMax (J1 Lc mu B) δ (mubar mu))
    (x y : ℕ → Stack n p) (hrun : IsDIGingRun f W α x y) :
    0 < rateLam (J1 Lc mu B) δ (mubar mu) α B ∧ rateLam (J1 Lc mu B) δ (mubar mu) α B < 1 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
        frob (x k - ones xstar) ≤ C * rateLam (J1 Lc mu B) δ (mubar mu) α B ^ k := by
  exact DGFresh.native_theorem_10 f Lc mu h4 h5 xstar hopt E W B h1 δ hδ α hα hαmax x y hrun

end DIGing.Undir


open DIGing.Undir
theorem solution {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc mu : Fin n → ℝ)
    (h4 : Assumption4 f Lc) (h5 : Assumption5 f mu)
    (xstar : EuclideanSpace ℝ (Fin p)) (hopt : ∀ z, objective f xstar ≤ objective f z)
    (E : ℕ → SimpleGraph (Fin n)) (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (B : ℕ)
    (h1 : Assumption1 E W B)
    (δ : ℝ) (hδ : IsLUB {d | ∃ k, B - 1 ≤ k ∧ d = deltaK W B k} δ)
    (α : ℝ) (hα : 0 < α) (hαmax : α < alphaMax (J1 Lc mu B) δ (mubar mu))
    (x y : ℕ → Stack n p) (hrun : IsDIGingRun f W α x y) :
    0 < rateLam (J1 Lc mu B) δ (mubar mu) α B ∧ rateLam (J1 Lc mu B) δ (mubar mu) α B < 1 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
        frob (x k - ones xstar) ≤ C * rateLam (J1 Lc mu B) δ (mubar mu) α B ^ k := by
  exact DIGing.Undir.theorem_10 f Lc mu h4 h5 xstar hopt E W B h1 δ hδ α hα hαmax x y hrun
