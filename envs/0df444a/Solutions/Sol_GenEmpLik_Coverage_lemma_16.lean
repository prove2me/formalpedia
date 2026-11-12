-- Prove2me | solution 1 for GenEmpLik.Coverage.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T05:08:45.728316+00:00
-- url     : https://prove2.me/submissions/e86945c3-fd15-4f8c-95a3-0459442190e0

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_AssumptionB
import Definitions.Def_GenEmpLik_Coverage_optimalValue
import Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
import Definitions.Def_GenEmpLik_Coverage_divergenceBall
import Definitions.Def_GenEmpLik_Coverage_confidenceSet
import Definitions.Def_GenEmpLik_Coverage_influence
import Definitions.Def_GenEmpLik_Coverage_remainder
import Definitions.Def_GenEmpLik_Coverage_robustUpper
import Definitions.Def_GenEmpLik_Coverage_uniqueOptimizer
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar
import Theorems.Thm_GenEmpLik_Coverage_lemma_13

set_option autoImplicit false

namespace GenEmpLikCoverageLemma16Aux

open MeasureTheory ProbabilityTheory Filter Topology GenEmpLik.Coverage

/-! ### 1. Rademacher MGF and Pisier's maximal inequality -/

def radSign (b : Bool) : ℝ := if b then 1 else -1

lemma rademacher_mgf_bound {n : ℕ} (b : Fin n → ℝ) :
    ((2 : ℝ)⁻¹ ^ n) *
      ∑ σ : Fin n → Bool, Real.exp (∑ i : Fin n, radSign (σ i) * b i) ≤
      Real.exp ((∑ i : Fin n, (b i) ^ 2) / 2) := by
  have hprod :
      ∑ σ : Fin n → Bool, Real.exp (∑ i : Fin n, radSign (σ i) * b i) =
        ∏ i : Fin n, (Real.exp (b i) + Real.exp (-b i)) := by
    calc
      ∑ σ : Fin n → Bool, Real.exp (∑ i : Fin n, radSign (σ i) * b i)
          = ∑ σ : Fin n → Bool, ∏ i : Fin n, Real.exp (radSign (σ i) * b i) := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [Real.exp_sum]
      _ = ∏ i : Fin n, ∑ s : Bool, Real.exp (radSign s * b i) := by
            simpa using (Fintype.prod_sum (fun (i : Fin n) (s : Bool) =>
              Real.exp (radSign s * b i))).symm
      _ = ∏ i : Fin n, (Real.exp (b i) + Real.exp (-b i)) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            simp [radSign]
  have hpow : ((2 : ℝ)⁻¹ ^ n) = ∏ _i : Fin n, (2 : ℝ)⁻¹ := by
    simp [Finset.prod_const]
  rw [hprod, hpow, ← Finset.prod_mul_distrib]
  calc
    ∏ i : Fin n, (2 : ℝ)⁻¹ * (Real.exp (b i) + Real.exp (-b i))
        = ∏ i : Fin n, Real.cosh (b i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Real.cosh_eq]
          ring
    _ ≤ ∏ i : Fin n, Real.exp ((b i) ^ 2 / 2) := by
          refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
          exact Real.cosh_le_exp_half_sq (b i)
    _ = Real.exp ((∑ i : Fin n, (b i) ^ 2) / 2) := by
          rw [← Real.exp_sum, Finset.sum_div]

lemma rademacher_avg_const {n : ℕ} (c : ℝ) :
    ((2 : ℝ)⁻¹ ^ n) * (∑ _σ : Fin n → Bool, c) = c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero n two_ne_zero), one_mul]

lemma pisier_rademacher_max {α : Type*} {n : ℕ}
    (J : Finset α) (hJ : J.Nonempty) (a : α → Fin n → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (ha : ∀ j ∈ J, ∑ i : Fin n, (a j i) ^ 2 ≤ s ^ 2) :
    ((2 : ℝ)⁻¹ ^ n) *
      ∑ σ : Fin n → Bool, J.sup' hJ (fun j => |∑ i : Fin n, radSign (σ i) * a j i|) ≤
      s * Real.sqrt (2 * Real.log (2 * (J.card : ℝ))) := by
  rcases hs.eq_or_lt with rfl | hs_pos
  · have hzero : ∀ j ∈ J, ∀ i : Fin n, a j i = 0 := by
      intro j hj i
      have hsum : ∑ k : Fin n, (a j k) ^ 2 ≤ 0 := by simpa using ha j hj
      have hle : (a j i) ^ 2 ≤ ∑ k : Fin n, (a j k) ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (a j k)) (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp (le_antisymm (hle.trans hsum) (sq_nonneg _))
    have hsup : ∀ σ : Fin n → Bool,
        J.sup' hJ (fun j => |∑ i : Fin n, radSign (σ i) * a j i|) = 0 := by
      intro σ
      apply le_antisymm
      · refine Finset.sup'_le hJ _ fun j hj => ?_
        have : (∑ i : Fin n, radSign (σ i) * a j i) = 0 :=
          Finset.sum_eq_zero fun i _ => by simp [hzero j hj i]
        simp [this]
      · obtain ⟨j₀, hj₀⟩ := hJ
        exact le_trans (abs_nonneg _)
          (Finset.le_sup' (fun j => |∑ i : Fin n, radSign (σ i) * a j i|) hj₀)
    simp [hsup]
  · have hJcard_pos : (1 : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast hJ.card_pos
    have h2J : (1 : ℝ) < 2 * (J.card : ℝ) := by linarith
    have h2J_pos : (0 : ℝ) < 2 * (J.card : ℝ) := by linarith
    set L : ℝ := Real.log (2 * (J.card : ℝ))
    have hL_pos : 0 < L := Real.log_pos h2J
    set lam : ℝ := Real.sqrt (2 * L) / s
    have hlam_pos : 0 < lam := div_pos (Real.sqrt_pos.mpr (by positivity)) hs_pos
    set W : (Fin n → Bool) → ℝ :=
      fun σ => J.sup' hJ (fun j => |∑ i : Fin n, radSign (σ i) * a j i|)
    have hW_exp_pt : ∀ σ : Fin n → Bool,
        Real.exp (lam * W σ) ≤
          ∑ j ∈ J, (Real.exp (∑ i : Fin n, radSign (σ i) * (lam * a j i)) +
            Real.exp (∑ i : Fin n, radSign (σ i) * (-(lam * a j i)))) := by
      intro σ
      obtain ⟨j₀, hj₀, hWj₀⟩ :=
        Finset.exists_mem_eq_sup' hJ (fun j => |∑ i : Fin n, radSign (σ i) * a j i|)
      have hWj₀' : W σ = |∑ i : Fin n, radSign (σ i) * a j₀ i| := hWj₀
      rw [hWj₀']
      set u : ℝ := ∑ i : Fin n, radSign (σ i) * a j₀ i
      have hsingle : Real.exp (lam * |u|) ≤ Real.exp (lam * u) + Real.exp (-(lam * u)) := by
        rcases abs_choice u with hu | hu <;> rw [hu]
        · linarith [Real.exp_pos (-(lam * u))]
        · ring_nf; linarith [Real.exp_pos (lam * u)]
      have hrew1 : lam * u = ∑ i : Fin n, radSign (σ i) * (lam * a j₀ i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      have hrew2 : -(lam * u) = ∑ i : Fin n, radSign (σ i) * (-(lam * a j₀ i)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      have hpair :
          Real.exp (lam * u) + Real.exp (-(lam * u)) =
            Real.exp (∑ i : Fin n, radSign (σ i) * (lam * a j₀ i)) +
              Real.exp (∑ i : Fin n, radSign (σ i) * (-(lam * a j₀ i))) :=
        congrArg₂ (· + ·) (congrArg Real.exp hrew1) (congrArg Real.exp hrew2)
      refine (hsingle.trans_eq hpair).trans ?_
      exact Finset.single_le_sum
        (f := fun j => Real.exp (∑ i : Fin n, radSign (σ i) * (lam * a j i)) +
          Real.exp (∑ i : Fin n, radSign (σ i) * (-(lam * a j i))))
        (fun j _ => by positivity) hj₀
    have hlam_sq : lam ^ 2 * s ^ 2 / 2 = L := by
      have h1 : lam ^ 2 * s ^ 2 = 2 * L := by
        dsimp [lam]
        rw [div_pow, Real.sq_sqrt (by positivity),
          div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hs_pos))]
      linarith
    have hmgf_W :
        ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, Real.exp (lam * W σ) ≤ Real.exp (2 * L) := by
      calc
        ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, Real.exp (lam * W σ)
            ≤ ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool,
                ∑ j ∈ J, (Real.exp (∑ i : Fin n, radSign (σ i) * (lam * a j i)) +
                  Real.exp (∑ i : Fin n, radSign (σ i) * (-(lam * a j i)))) := by
              refine mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum fun σ _ => hW_exp_pt σ) (by positivity)
        _ = ∑ j ∈ J, (((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool,
                Real.exp (∑ i : Fin n, radSign (σ i) * (lam * a j i)) +
              ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool,
                Real.exp (∑ i : Fin n, radSign (σ i) * (-(lam * a j i)))) := by
              rw [Finset.sum_comm, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_add_distrib, mul_add]
        _ ≤ ∑ _j ∈ J, (Real.exp L + Real.exp L) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hb1 : (∑ i : Fin n, (lam * a j i) ^ 2) / 2 ≤ L := by
                calc
                  (∑ i : Fin n, (lam * a j i) ^ 2) / 2
                      = (lam ^ 2 * ∑ i : Fin n, (a j i) ^ 2) / 2 := by
                        congr 1; simp_rw [mul_pow, ← Finset.mul_sum]
                  _ ≤ lam ^ 2 * s ^ 2 / 2 := by
                        exact div_le_div_of_nonneg_right
                          (mul_le_mul_of_nonneg_left (ha j hj) (sq_nonneg lam)) (by norm_num)
                  _ = L := hlam_sq
              have hb2 : (∑ i : Fin n, (-(lam * a j i)) ^ 2) / 2 ≤ L := by
                simpa only [neg_sq] using hb1
              exact add_le_add
                ((rademacher_mgf_bound _).trans (Real.exp_le_exp.mpr hb1))
                ((rademacher_mgf_bound _).trans (Real.exp_le_exp.mpr hb2))
        _ = (2 * (J.card : ℝ)) * Real.exp L := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              ring
        _ = Real.exp (2 * L) := by
              have hexpL : Real.exp L = 2 * (J.card : ℝ) := Real.exp_log h2J_pos
              rw [← hexpL, ← Real.exp_add, two_mul]
    have hlin : ∀ σ : Fin n → Bool,
        lam * W σ - 2 * L + 1 ≤ Real.exp (-(2 * L)) * Real.exp (lam * W σ) := by
      intro σ
      calc
        lam * W σ - 2 * L + 1 ≤ Real.exp (lam * W σ - 2 * L) :=
          Real.add_one_le_exp (lam * W σ - 2 * L)
        _ = Real.exp (-(2 * L)) * Real.exp (lam * W σ) := by
          rw [← Real.exp_add]; ring_nf
    set avgW : ℝ := ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, W σ
    have havg_ineq : lam * avgW - 2 * L + 1 ≤ 1 := by
      have hsum_ineq :
          ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, (lam * W σ - 2 * L + 1) ≤
            ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool,
              (Real.exp (-(2 * L)) * Real.exp (lam * W σ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hlin σ) (by positivity)
      have hlhs :
          ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, (lam * W σ - 2 * L + 1) =
            lam * avgW - 2 * L + 1 := by
        simp only [sub_eq_add_neg, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
        rw [rademacher_avg_const (- (2 * L)), rademacher_avg_const 1]
        dsimp [avgW]
        ring
      have hrhs :
          ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool,
              (Real.exp (-(2 * L)) * Real.exp (lam * W σ)) ≤ 1 := by
        rw [← Finset.mul_sum, ← mul_assoc, mul_comm ((2 : ℝ)⁻¹ ^ n), mul_assoc]
        calc
          Real.exp (-(2 * L)) * (((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, Real.exp (lam * W σ))
              ≤ Real.exp (-(2 * L)) * Real.exp (2 * L) :=
                mul_le_mul_of_nonneg_left hmgf_W (by positivity)
          _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      linarith
    have hprod_le : lam * avgW ≤ lam * (s * Real.sqrt (2 * L)) := by
      have hval : lam * (s * Real.sqrt (2 * L)) = 2 * L := by
        dsimp [lam]
        rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hs_pos), Real.mul_self_sqrt (by positivity)]
      linarith
    exact le_of_mul_le_mul_left hprod_le hlam_pos

/-! ### 2. Elementary arithmetic bounds and dyadic nets -/

lemma sum_k_two_inv_pow_eq (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (2 : ℝ)⁻¹ ^ k =
      2 - ((K : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 K), ih]
    push_cast
    rw [pow_succ]
    ring

lemma sum_k_two_inv_le_four (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (2 : ℝ)⁻¹ ^ (k - 1) ≤ 4 := by
  have hrew :
      ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (2 : ℝ)⁻¹ ^ (k - 1) =
        2 * ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (2 : ℝ)⁻¹ ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hpow : (2 : ℝ)⁻¹ ^ k = (2 : ℝ)⁻¹ ^ (k - 1) * (2 : ℝ)⁻¹ := by
      conv_lhs => rw [← Nat.sub_add_cancel hk1, pow_succ]
    rw [hpow]
    ring
  rw [hrew, sum_k_two_inv_pow_eq]
  have hnonneg : 0 ≤ ((K : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K := by positivity
  linarith

lemma sqrt_le_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 :=
  Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩

lemma abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_abs x, sq_nonneg (|x| - 1)]

lemma sqrt_nat_mul_two_inv_pow_le_one (n : ℕ) :
    Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    have hpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      have : n ≤ 2 ^ n := n.lt_two_pow_self.le
      exact_mod_cast this
    calc
      Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right (hsqrt.trans hpow) (by positivity)
      _ = 1 := by rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero n two_ne_zero)]

noncomputable def gridBox (d m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(m : ℤ)) (m : ℤ))

lemma card_gridBox (d m : ℕ) : (gridBox d m).card = (2 * m + 1) ^ d := by
  simp only [gridBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_fin]
  congr 1
  omega

noncomputable def gridPt {d : ℕ} (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) (m : ℕ)
    (q : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun j => xs.ofLp j + (q j : ℝ) * (r / (m : ℝ)))

open Classical in
noncomputable def dyadicNet {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℕ → Finset (EuclideanSpace ℝ (Fin d))
  | 0 => {xs}
  | k + 1 =>
    let m : ℕ := (d + 1) * 2 ^ (k + 1)
    let B : Set (EuclideanSpace ℝ (Fin d)) := X ∩ Metric.closedBall xs r
    let rad : ℝ := (Real.sqrt (d : ℝ) / (2 * (m : ℝ))) * r
    insert xs
      (((gridBox d m).filter (fun q => (B ∩ Metric.closedBall (gridPt xs r m q) rad).Nonempty)).image
        (fun q =>
          if h : (B ∩ Metric.closedBall (gridPt xs r m q) rad).Nonempty then h.choose else xs))

lemma xs_mem_dyadicNet {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) (k : ℕ) :
    xs ∈ dyadicNet X xs r k := by
  classical
  cases k <;> simp [dyadicNet]

lemma dyadicNet_nonempty {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) (k : ℕ) :
    (dyadicNet X xs r k).Nonempty :=
  ⟨xs, xs_mem_dyadicNet X xs r k⟩

lemma dyadicNet_subset {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))}
    {xs : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hxs : xs ∈ X) (hr : 0 ≤ r) (k : ℕ) :
    ∀ u ∈ dyadicNet X xs r k, u ∈ X ∩ Metric.closedBall xs r := by
  cases k with
  | zero =>
    intro u hu
    simp only [dyadicNet, Finset.mem_singleton] at hu
    subst hu
    exact ⟨hxs, Metric.mem_closedBall_self hr⟩
  | succ k =>
    classical
    intro u hu
    simp only [dyadicNet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hu
    rcases hu with rfl | ⟨q, ⟨_, hq⟩, rfl⟩
    · exact ⟨hxs, Metric.mem_closedBall_self hr⟩
    · rw [dif_pos hq]
      exact hq.choose_spec.1

lemma card_dyadicNet_le {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    2 * ((dyadicNet X xs r k).card : ℝ) ≤ (2 : ℝ) ^ (2 + d * (d + 3 + k)) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  set m : ℕ := (d + 1) * 2 ^ (k' + 1)
  have hm_pos : 1 ≤ m := Nat.mul_pos (Nat.succ_pos d) (Nat.two_pow_pos (k' + 1))
  have h2m1 : 2 * m + 1 ≤ 2 ^ (d + 3 + (k' + 1)) := by
    have h1 : 2 * m + 1 ≤ 3 * m := by omega
    have h3d : 3 * (d + 1) ≤ 2 ^ (d + 3) := by
      have hd : d + 1 ≤ 2 ^ d := d.lt_two_pow_self
      calc
        3 * (d + 1) ≤ 8 * 2 ^ d := Nat.mul_le_mul (by norm_num) hd
        _ = 2 ^ (d + 3) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← Nat.pow_add, Nat.add_comm]
    calc
      2 * m + 1 ≤ 3 * ((d + 1) * 2 ^ (k' + 1)) := h1
      _ = (3 * (d + 1)) * 2 ^ (k' + 1) := by ring
      _ ≤ 2 ^ (d + 3) * 2 ^ (k' + 1) := Nat.mul_le_mul_right _ h3d
      _ = 2 ^ (d + 3 + (k' + 1)) := by rw [← Nat.pow_add]
  have hpow_le : (2 * m + 1) ^ d ≤ 2 ^ (d * (d + 3 + (k' + 1))) := by
    calc
      (2 * m + 1) ^ d ≤ (2 ^ (d + 3 + (k' + 1))) ^ d := Nat.pow_le_pow_left h2m1 d
      _ = 2 ^ (d * (d + 3 + (k' + 1))) := by rw [← Nat.pow_mul, Nat.mul_comm]
  have hcard_nat : (dyadicNet X xs r (k' + 1)).card ≤ 1 + (2 * m + 1) ^ d := by
    classical
    set B : Set (EuclideanSpace ℝ (Fin d)) := X ∩ Metric.closedBall xs r
    set rad : ℝ := (Real.sqrt (d : ℝ) / (2 * (m : ℝ))) * r
    set S : Finset (EuclideanSpace ℝ (Fin d)) :=
      ((gridBox d m).filter (fun q => (B ∩ Metric.closedBall (gridPt xs r m q) rad).Nonempty)).image
        (fun q =>
          if h : (B ∩ Metric.closedBall (gridPt xs r m q) rad).Nonempty then h.choose else xs)
    have hdef : dyadicNet X xs r (k' + 1) = insert xs S := rfl
    rw [hdef]
    calc
      (insert xs S).card ≤ S.card + 1 := Finset.card_insert_le xs S
      _ = 1 + S.card := Nat.add_comm _ _
      _ ≤ 1 + ((gridBox d m).filter
            (fun q => (B ∩ Metric.closedBall (gridPt xs r m q) rad).Nonempty)).card :=
          Nat.add_le_add_left Finset.card_image_le 1
      _ ≤ 1 + (gridBox d m).card := Nat.add_le_add_left (Finset.card_filter_le _ _) 1
      _ = 1 + (2 * m + 1) ^ d := by rw [card_gridBox]
  have htot_nat : 2 * (dyadicNet X xs r (k' + 1)).card ≤ 2 ^ (2 + d * (d + 3 + (k' + 1))) := by
    have hone : 1 ≤ 2 ^ (d * (d + 3 + (k' + 1))) := Nat.one_le_two_pow
    calc
      2 * (dyadicNet X xs r (k' + 1)).card
          ≤ 2 * (1 + (2 * m + 1) ^ d) := Nat.mul_le_mul_left 2 hcard_nat
      _ ≤ 2 * (2 ^ (d * (d + 3 + (k' + 1))) + 2 ^ (d * (d + 3 + (k' + 1)))) :=
          Nat.mul_le_mul_left 2 (Nat.add_le_add hone hpow_le)
      _ = 2 ^ (2 + d * (d + 3 + (k' + 1))) := by
          rw [← two_mul, ← Nat.mul_assoc, show 2 * 2 = 2 ^ 2 by rfl, ← Nat.pow_add]
  exact_mod_cast htot_nat

lemma sqrt_two_log_two_card_dyadicNet_le {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Real.sqrt (2 * Real.log (2 * ((dyadicNet X xs r k).card : ℝ))) ≤
      2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * (k : ℝ) := by
  have hcard_pos : (1 : ℝ) ≤ (dyadicNet X xs r k).card := by
    exact_mod_cast (dyadicNet_nonempty X xs r k).card_pos
  have hpos : (0 : ℝ) < 2 * ((dyadicNet X xs r k).card : ℝ) := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith [Real.add_one_le_exp 1]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdd3_nonneg : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) + 3) := mul_nonneg hd0 (by linarith)
  have hdd4_nonneg : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) + 4) := mul_nonneg hd0 (by linarith)
  have hlog :
      Real.log (2 * ((dyadicNet X xs r k).card : ℝ)) ≤
        (2 + (d : ℝ) * ((d : ℝ) + 4)) * (k : ℝ) := by
    have hle := Real.log_le_log hpos (card_dyadicNet_le X xs r hk)
    rw [Real.log_pow] at hle
    have hpoly : 2 + (d : ℝ) * ((d : ℝ) + 3 + (k : ℝ)) ≤
        (2 + (d : ℝ) * ((d : ℝ) + 4)) * (k : ℝ) := by
      have : 0 ≤ (2 + (d : ℝ) * ((d : ℝ) + 3)) * ((k : ℝ) - 1) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    calc
      Real.log (2 * ((dyadicNet X xs r k).card : ℝ))
          ≤ ((2 + d * (d + 3 + k) : ℕ) : ℝ) * Real.log 2 := hle
      _ ≤ ((2 + d * (d + 3 + k) : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ = 2 + (d : ℝ) * ((d : ℝ) + 3 + (k : ℝ)) := by push_cast; ring
      _ ≤ (2 + (d : ℝ) * ((d : ℝ) + 4)) * (k : ℝ) := hpoly
  set B : ℝ := 2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * (k : ℝ)
  have hB1 : 1 ≤ B := by
    have : (4 : ℝ) ≤ B := by
      calc
        (4 : ℝ) = 2 * 2 * 1 := by norm_num
        _ ≤ 2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * (k : ℝ) := by
          exact mul_le_mul (by linarith) hk1 zero_le_one (by linarith)
    linarith
  have h2log : 2 * Real.log (2 * ((dyadicNet X xs r k).card : ℝ)) ≤ B := by
    dsimp [B]; linarith
  exact (Real.sqrt_le_sqrt h2log).trans (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)

lemma exists_mem_dyadicNet_dist_le {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))}
    {xs : EuclideanSpace ℝ (Fin d)} {r : ℝ} (_hxs : xs ∈ X) (hr : 0 < r) (k : ℕ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ X ∩ Metric.closedBall xs r) :
    ∃ u ∈ dyadicNet X xs r k, ‖y - u‖ ≤ (2 : ℝ)⁻¹ ^ k * r := by
  cases k with
  | zero =>
    refine ⟨xs, xs_mem_dyadicNet X xs r 0, ?_⟩
    have : dist y xs ≤ r := Metric.mem_closedBall.mp hy.2
    simpa [dist_eq_norm] using this
  | succ k =>
    set m : ℕ := (d + 1) * 2 ^ (k + 1)
    have hm_pos_nat : 0 < m := Nat.mul_pos (Nat.succ_pos d) (Nat.two_pow_pos (k + 1))
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    set step : ℝ := r / (m : ℝ)
    have hstep_pos : 0 < step := div_pos hr hm_pos
    set q : Fin d → ℤ := fun j => ⌊(y.ofLp j - xs.ofLp j) / step + 1 / 2⌋
    have hy_norm : ‖y - xs‖ ≤ r := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hy.2
    have hcoord : ∀ j : Fin d, -(m : ℤ) ≤ q j ∧ q j ≤ (m : ℤ) ∧
        |y.ofLp j - (gridPt xs r m q).ofLp j| ≤ r / (2 * (m : ℝ)) := by
      intro j
      have hj_abs : |y.ofLp j - xs.ofLp j| ≤ r := by
        have h1 : ‖(y - xs).ofLp j‖ ≤ ‖y - xs‖ := PiLp.norm_apply_le (y - xs) j
        simpa [Real.norm_eq_abs] using h1.trans hy_norm
      set t : ℝ := (y.ofLp j - xs.ofLp j) / step
      have ht_abs : |t| ≤ (m : ℝ) := by
        rw [abs_div, abs_of_pos hstep_pos, div_le_iff₀ hstep_pos]
        have : (m : ℝ) * step = r := by dsimp [step]; exact mul_div_cancel₀ r (ne_of_gt hm_pos)
        linarith
      have ht_lo : -(m : ℝ) ≤ t := (abs_le.mp ht_abs).1
      have ht_hi : t ≤ (m : ℝ) := (abs_le.mp ht_abs).2
      have hq_lo : -(m : ℤ) ≤ q j := by
        dsimp [q]
        refine Int.le_floor.mpr ?_
        push_cast
        linarith
      have hq_hi : q j ≤ (m : ℤ) := by
        dsimp [q]
        refine Int.le_of_lt_add_one (Int.floor_lt.mpr ?_)
        push_cast
        linarith
      have hfl1 : (q j : ℝ) ≤ t + 1 / 2 := Int.floor_le (t + 1 / 2)
      have hfl2 : t + 1 / 2 < (q j : ℝ) + 1 := Int.lt_floor_add_one (t + 1 / 2)
      have hdiff_t : |t - (q j : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hdiff_coord :
          y.ofLp j - (gridPt xs r m q).ofLp j = (t - (q j : ℝ)) * step := by
        dsimp [gridPt, t, step]
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hstep_pos)]
        ring
      refine ⟨hq_lo, hq_hi, ?_⟩
      rw [hdiff_coord, abs_mul, abs_of_pos hstep_pos]
      calc
        |t - (q j : ℝ)| * step ≤ (1 / 2) * (r / (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hdiff_t hstep_pos.le
        _ = r / (2 * (m : ℝ)) := by ring
    have hq_mem : q ∈ gridBox d m := by
      simp only [gridBox, Fintype.mem_piFinset, Finset.mem_Icc]
      exact fun j => ⟨(hcoord j).1, (hcoord j).2.1⟩
    set rad : ℝ := (Real.sqrt (d : ℝ) / (2 * (m : ℝ))) * r
    have hrad_nonneg : 0 ≤ rad := by dsimp [rad]; positivity
    have hy_grid : ‖y - gridPt xs r m q‖ ≤ rad := by
      have hsq : ‖y - gridPt xs r m q‖ ^ 2 ≤ rad ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        calc
          ∑ j : Fin d, ‖(y - gridPt xs r m q).ofLp j‖ ^ 2
              ≤ ∑ _j : Fin d, (r / (2 * (m : ℝ))) ^ 2 := by
                refine Finset.sum_le_sum fun j _ => ?_
                have hj : ‖(y - gridPt xs r m q).ofLp j‖ ≤ r / (2 * (m : ℝ)) := by
                  simpa [Real.norm_eq_abs] using (hcoord j).2.2
                exact pow_le_pow_left₀ (norm_nonneg _) hj 2
          _ = (d : ℝ) * (r / (2 * (m : ℝ))) ^ 2 := by simp
          _ = rad ^ 2 := by
                dsimp only [rad]
                rw [mul_pow, div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
                ring
      nlinarith [norm_nonneg (y - gridPt xs r m q)]
    set B : Set (EuclideanSpace ℝ (Fin d)) := X ∩ Metric.closedBall xs r
    have hne : (B ∩ Metric.closedBall (gridPt xs r m q) rad).Nonempty :=
      ⟨y, hy, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hy_grid)⟩
    classical
    let u := hne.choose
    have hu_mem : u ∈ dyadicNet X xs r (k + 1) := by
      dsimp [dyadicNet]
      refine Finset.mem_insert_of_mem ?_
      refine Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq_mem, hne⟩, ?_⟩
      rw [dif_pos hne]
    have hu_grid : ‖u - gridPt xs r m q‖ ≤ rad := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp hne.choose_spec.2
    refine ⟨u, hu_mem, ?_⟩
    have htri : ‖y - u‖ ≤ 2 * rad := by
      have := norm_sub_le_norm_sub_add_norm_sub y (gridPt xs r m q) u
      rw [norm_sub_rev (gridPt xs r m q) u] at this
      linarith
    have hsqrtd : Real.sqrt (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      push_cast
      exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [Nat.cast_nonneg (α := ℝ) d]⟩
    calc
      ‖y - u‖ ≤ 2 * ((Real.sqrt (d : ℝ) / (2 * (m : ℝ))) * r) := htri
      _ = (Real.sqrt (d : ℝ) / (m : ℝ)) * r := by ring
      _ ≤ (((d + 1 : ℕ) : ℝ) / (((d + 1) * 2 ^ (k + 1) : ℕ) : ℝ)) * r := by
          refine mul_le_mul_of_nonneg_right ?_ hr.le
          exact div_le_div_of_nonneg_right hsqrtd hm_pos.le
      _ = (2 : ℝ)⁻¹ ^ (k + 1) * r := by
          push_cast
          have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
          rw [div_mul_eq_div_div, div_self hd1, one_div, inv_pow]

open Classical in
noncomputable def netProj {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) (r : ℝ) (k : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if h : ∃ u ∈ dyadicNet X xs r k, ‖y - u‖ ≤ (2 : ℝ)⁻¹ ^ k * r then h.choose else xs

lemma netProj_spec {d : ℕ} {X : Set (EuclideanSpace ℝ (Fin d))}
    {xs : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hxs : xs ∈ X) (hr : 0 < r) (k : ℕ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ X ∩ Metric.closedBall xs r) :
    netProj X xs r k y ∈ dyadicNet X xs r k ∧
      ‖y - netProj X xs r k y‖ ≤ (2 : ℝ)⁻¹ ^ k * r := by
  classical
  have hex := exists_mem_dyadicNet_dist_le hxs hr k hy
  dsimp [netProj]
  rw [dif_pos hex]
  exact hex.choose_spec

/-! ### 3. Chaining of the Rademacher process on `dyadicNet` -/

noncomputable def radProc {d n : ℕ} {Ξ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (xs : EuclideanSpace ℝ (Fin d)) (z : Fin n → Ξ)
    (σ : Fin n → Bool) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, radSign (σ i) * (ℓ x (z i) - ℓ xs (z i))

lemma radProc_xs {d n : ℕ} {Ξ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (xs : EuclideanSpace ℝ (Fin d)) (z : Fin n → Ξ) (σ : Fin n → Bool) :
    radProc ℓ xs z σ xs = 0 := by
  simp [radProc]

lemma chaining_telescoping {d n : ℕ} {Ξ : Type*}
    {X : Set (EuclideanSpace ℝ (Fin d))} {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ}
    {xs : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hxs : xs ∈ X) (hr : 0 < r)
    (z : Fin n → Ξ) (σ : Fin n → Bool) (K : ℕ) :
    (dyadicNet X xs r K).sup' (dyadicNet_nonempty X xs r K)
        (fun u => |radProc ℓ xs z σ u|) ≤
      ∑ k ∈ Finset.Icc 1 K,
        (dyadicNet X xs r k).sup' (dyadicNet_nonempty X xs r k)
          (fun v => |radProc ℓ xs z σ v - radProc ℓ xs z σ (netProj X xs r (k - 1) v)|) := by
  induction K with
  | zero =>
    simp [dyadicNet, radProc_xs]
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 K), Nat.add_sub_cancel]
    refine Finset.sup'_le (dyadicNet_nonempty X xs r (K + 1)) _ fun u hu => ?_
    have hu_B : u ∈ X ∩ Metric.closedBall xs r := dyadicNet_subset hxs hr.le (K + 1) u hu
    have hw_mem : netProj X xs r K u ∈ dyadicNet X xs r K := (netProj_spec hxs hr K hu_B).1
    have h1 : |radProc ℓ xs z σ (netProj X xs r K u)| ≤
        (dyadicNet X xs r K).sup' (dyadicNet_nonempty X xs r K)
          (fun w => |radProc ℓ xs z σ w|) :=
      Finset.le_sup' (fun w => |radProc ℓ xs z σ w|) hw_mem
    have h2 : |radProc ℓ xs z σ u - radProc ℓ xs z σ (netProj X xs r K u)| ≤
        (dyadicNet X xs r (K + 1)).sup' (dyadicNet_nonempty X xs r (K + 1))
          (fun v => |radProc ℓ xs z σ v - radProc ℓ xs z σ (netProj X xs r K v)|) :=
      Finset.le_sup'
        (fun v => |radProc ℓ xs z σ v - radProc ℓ xs z σ (netProj X xs r K v)|) hu
    have htri : |radProc ℓ xs z σ u| ≤
        |radProc ℓ xs z σ (netProj X xs r K u)| +
          |radProc ℓ xs z σ u - radProc ℓ xs z σ (netProj X xs r K u)| := by
      have := abs_add_le (radProc ℓ xs z σ (netProj X xs r K u))
        (radProc ℓ xs z σ u - radProc ℓ xs z σ (netProj X xs r K u))
      simpa using this
    linarith

lemma rademacher_chaining_bound {d n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {X : Set (EuclideanSpace ℝ (Fin d))} {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ}
    {M : Ξ → ℝ} {xs : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hn : 0 < n) (hB : AssumptionB X ℓ M) (hxs : xs ∈ X) (hr : 0 < r)
    (z : Fin n → Ξ) (K : ℕ) :
    ((2 : ℝ)⁻¹ ^ n) *
      ∑ σ : Fin n → Bool,
        (dyadicNet X xs r K).sup' (dyadicNet_nonempty X xs r K)
          (fun u => |radProc ℓ xs z σ u|) ≤
      8 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2 + 1) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  set Sn : ℝ := Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2)
  have hSn_nonneg : 0 ≤ Sn := Real.sqrt_nonneg _
  have hSn_sq : Sn ^ 2 = (1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hlevel : ∀ k ∈ Finset.Icc 1 K,
      ((2 : ℝ)⁻¹ ^ n) *
        ∑ σ : Fin n → Bool,
          (dyadicNet X xs r k).sup' (dyadicNet_nonempty X xs r k)
            (fun v => |radProc ℓ xs z σ v - radProc ℓ xs z σ (netProj X xs r (k - 1) v)|) ≤
        Sn * (2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r) *
          ((k : ℝ) * (2 : ℝ)⁻¹ ^ (k - 1)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    set sk : ℝ := Sn * ((2 : ℝ)⁻¹ ^ (k - 1) * r)
    have hsk_nonneg : 0 ≤ sk := by positivity
    set ak : EuclideanSpace ℝ (Fin d) → Fin n → ℝ :=
      fun v i => (1 / Real.sqrt (n : ℝ)) * (ℓ v (z i) - ℓ (netProj X xs r (k - 1) v) (z i))
    have hrew_diff : ∀ (σ : Fin n → Bool) (v : EuclideanSpace ℝ (Fin d)),
        radProc ℓ xs z σ v - radProc ℓ xs z σ (netProj X xs r (k - 1) v) =
          ∑ i : Fin n, radSign (σ i) * ak v i := by
      intro σ v
      dsimp [radProc, ak]
      rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hak_sq : ∀ v ∈ dyadicNet X xs r k, ∑ i : Fin n, (ak v i) ^ 2 ≤ sk ^ 2 := by
      intro v hv
      have hv_B : v ∈ X ∩ Metric.closedBall xs r := dyadicNet_subset hxs hr.le k v hv
      have hw_spec := netProj_spec hxs hr (k - 1) hv_B
      have hw_X : netProj X xs r (k - 1) v ∈ X :=
        (dyadicNet_subset hxs hr.le (k - 1) _ hw_spec.1).1
      calc
        ∑ i : Fin n, (ak v i) ^ 2
            = (1 / (n : ℝ)) *
                ∑ i : Fin n, (ℓ v (z i) - ℓ (netProj X xs r (k - 1) v) (z i)) ^ 2 := by
              dsimp [ak]
              simp_rw [mul_pow, one_div, inv_pow, Real.sq_sqrt hn_pos.le, ← Finset.mul_sum]
        _ ≤ (1 / (n : ℝ)) *
              ∑ i : Fin n, (M (z i) * ((2 : ℝ)⁻¹ ^ (k - 1) * r)) ^ 2 := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
              have hlip := hB.2.2.2 (z i) v hv_B.1 (netProj X xs r (k - 1) v) hw_X
              have hle : |ℓ v (z i) - ℓ (netProj X xs r (k - 1) v) (z i)| ≤
                  M (z i) * ((2 : ℝ)⁻¹ ^ (k - 1) * r) :=
                hlip.trans (mul_le_mul_of_nonneg_left hw_spec.2 (hB.2.2.1 (z i)))
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) hle 2
        _ = sk ^ 2 := by
              dsimp [sk]
              rw [mul_pow, hSn_sq]
              simp_rw [mul_pow, ← Finset.sum_mul]
              ring
    have hpisier :=
      pisier_rademacher_max (dyadicNet X xs r k) (dyadicNet_nonempty X xs r k) ak sk hsk_nonneg
        hak_sq
    simp_rw [hrew_diff]
    calc
      ((2 : ℝ)⁻¹ ^ n) *
          ∑ σ : Fin n → Bool,
            (dyadicNet X xs r k).sup' (dyadicNet_nonempty X xs r k)
              (fun v => |∑ i : Fin n, radSign (σ i) * ak v i|)
          ≤ sk * Real.sqrt (2 * Real.log (2 * ((dyadicNet X xs r k).card : ℝ))) := hpisier
      _ ≤ sk * (2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_left (sqrt_two_log_two_card_dyadicNet_le X xs r hk1) hsk_nonneg
      _ = Sn * (2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r) * ((k : ℝ) * (2 : ℝ)⁻¹ ^ (k - 1)) := by
          dsimp [sk]; ring
  calc
    ((2 : ℝ)⁻¹ ^ n) *
        ∑ σ : Fin n → Bool,
          (dyadicNet X xs r K).sup' (dyadicNet_nonempty X xs r K)
            (fun u => |radProc ℓ xs z σ u|)
        ≤ ((2 : ℝ)⁻¹ ^ n) *
            ∑ σ : Fin n → Bool,
              ∑ k ∈ Finset.Icc 1 K,
                (dyadicNet X xs r k).sup' (dyadicNet_nonempty X xs r k)
                  (fun v =>
                    |radProc ℓ xs z σ v - radProc ℓ xs z σ (netProj X xs r (k - 1) v)|) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun σ _ => chaining_telescoping hxs hr z σ K) (by positivity)
    _ = ∑ k ∈ Finset.Icc 1 K,
          ((2 : ℝ)⁻¹ ^ n) *
            ∑ σ : Fin n → Bool,
              (dyadicNet X xs r k).sup' (dyadicNet_nonempty X xs r k)
                (fun v =>
                  |radProc ℓ xs z σ v - radProc ℓ xs z σ (netProj X xs r (k - 1) v)|) := by
          rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Icc 1 K,
          Sn * (2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r) * ((k : ℝ) * (2 : ℝ)⁻¹ ^ (k - 1)) :=
          Finset.sum_le_sum hlevel
    _ = Sn * (2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r) *
          ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (2 : ℝ)⁻¹ ^ (k - 1) := by
          rw [← Finset.mul_sum]
    _ ≤ Sn * (2 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r) * 4 := by
          refine mul_le_mul_of_nonneg_left (sum_k_two_inv_le_four K) ?_
          have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          positivity
    _ = 8 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r * Sn := by ring
    _ ≤ 8 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r *
          ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2 + 1) := by
          refine mul_le_mul_of_nonneg_left (sqrt_le_add_one (by positivity)) ?_
          have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          positivity

/-! ### 4. Rademacher symmetrization and measurable envelope on `P₀^⊗n` -/

lemma measurable_finset_sup' {α β : Type*} [MeasurableSpace α]
    (J : Finset β) (hJ : J.Nonempty) (f : β → α → ℝ)
    (hf : ∀ j ∈ J, Measurable (f j)) :
    Measurable (fun x => J.sup' hJ (fun j => f j x)) := by
  induction J using Finset.cons_induction with
  | empty => exact absurd hJ Finset.not_nonempty_empty
  | cons a s has ih =>
    by_cases hs : s.Nonempty
    · have hrew : (fun x => (Finset.cons a s has).sup' hJ (fun j => f j x)) =
          fun x => max (f a x) (s.sup' hs (fun j => f j x)) := by
        ext x
        exact Finset.sup'_cons hs _
      rw [hrew]
      exact (hf a (Finset.mem_cons_self a s)).max
        (ih hs fun j hj => hf j (Finset.mem_cons_of_mem hj))
    · have hsemp : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hsemp
      have hrew : (fun x => (Finset.cons a ∅ has).sup' hJ (fun j => f j x)) = f a := by
        ext x
        simp
      rw [hrew]
      exact hf a (Finset.mem_cons_self a ∅)

lemma integrable_of_nonneg_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f B : α → ℝ} (hf_meas : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hle : ∀ x, f x ≤ B x) (hB : Integrable B μ) :
    Integrable f μ :=
  hB.mono' hf_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hle x)

lemma integrable_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {φ : α → β} {f : β → ℝ}
    (hmp : MeasurePreserving φ μ ν) (hf_meas : Measurable f) (hf_int : Integrable f ν) :
    Integrable (fun x => f (φ x)) μ := by
  rw [← hmp.map_eq] at hf_int
  exact (integrable_map_measure hf_meas.aestronglyMeasurable hmp.aemeasurable).mp hf_int

lemma abs_integral_le_integral_abs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f

lemma markov_measure_ge_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hf_int : Integrable f μ) {a : ℝ} (ha : 0 < a) :
    μ {ω | a ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂μ) / a) := by
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hf_int a
  have hreal : μ.real {ω | a ≤ f ω} ≤ (∫ ω, f ω ∂μ) / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact hm
  have hof : ENNReal.ofReal (μ.real {ω | a ≤ f ω}) = μ {ω | a ≤ f ω} := by
    simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)]
  rw [← hof]
  exact ENNReal.ofReal_le_ofReal hreal

noncomputable def empProc {d n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (P₀ : Measure Ξ)
    (xs : EuclideanSpace ℝ (Fin d)) (z : Fin n → Ξ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / Real.sqrt (n : ℝ)) *
    ∑ i : Fin n, ((ℓ x (z i) - ℓ xs (z i)) - (∫ z₀, ℓ x z₀ ∂P₀ - ∫ z₀, ℓ xs z₀ ∂P₀))

lemma rademacher_symmetrization {d : ℕ} (n : ℕ) {Ξ : Type*} [MeasurableSpace Ξ]
    (P₀ : Measure Ξ) [IsProbabilityMeasure P₀]
    {X : Set (EuclideanSpace ℝ (Fin d))} {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ}
    {M : Ξ → ℝ} {xs : EuclideanSpace ℝ (Fin d)}
    (hB : AssumptionB X ℓ M) (hℓmeas : ∀ x, Measurable (ℓ x))
    (hM_int : Integrable M P₀) (hℓ_int : ∀ x ∈ X, Integrable (ℓ x) P₀)
    (hxs : xs ∈ X)
    (J : Finset (EuclideanSpace ℝ (Fin d))) (hJ : J.Nonempty) (hJX : ∀ u ∈ J, u ∈ X) :
    ∫ z, J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) ∂(Measure.pi (fun _ : Fin n => P₀)) ≤
      2 * ∫ z, (((2 : ℝ)⁻¹ ^ n) *
        ∑ σ : Fin n → Bool, J.sup' hJ (fun u => |radProc ℓ xs z σ u|))
        ∂(Measure.pi (fun _ : Fin n => P₀)) := by
  set ν : Measure (Fin n → Ξ) := Measure.pi (fun _ : Fin n => P₀)
  set g : EuclideanSpace ℝ (Fin d) → Ξ → ℝ := fun u z₀ => ℓ u z₀ - ℓ xs z₀
  set mg : EuclideanSpace ℝ (Fin d) → ℝ := fun u => ∫ z₀, ℓ u z₀ ∂P₀ - ∫ z₀, ℓ xs z₀ ∂P₀
  have hg_meas : ∀ u, Measurable (g u) := fun u => (hℓmeas u).sub (hℓmeas xs)
  have hg_lip : ∀ u ∈ J, ∀ z₀, |g u z₀| ≤ M z₀ * ‖u - xs‖ := by
    intro u hu z₀
    exact hB.2.2.2 z₀ u (hJX u hu) xs hxs
  have hg_int_P₀ : ∀ u ∈ J, Integrable (g u) P₀ := fun u hu =>
    (hℓ_int u (hJX u hu)).sub (hℓ_int xs hxs)
  have hmg_eq : ∀ u ∈ J, mg u = ∫ z₀, g u z₀ ∂P₀ := fun u hu =>
    (integral_sub (hℓ_int u (hJX u hu)) (hℓ_int xs hxs)).symm
  have hM_coord_int : ∀ i : Fin n, Integrable (fun z : Fin n → Ξ => M (z i)) ν := fun i =>
    integrable_comp_mp (MeasureTheory.measurePreserving_eval (fun _ => P₀) i) hB.2.1 hM_int
  have hg_coord_int : ∀ u ∈ J, ∀ i : Fin n, Integrable (fun z : Fin n → Ξ => g u (z i)) ν :=
    fun u hu i =>
      integrable_comp_mp (MeasureTheory.measurePreserving_eval (fun _ => P₀) i)
        (hg_meas u) (hg_int_P₀ u hu)
  have hg_coord_mean : ∀ u ∈ J, ∀ i : Fin n, ∫ z, g u (z i) ∂ν = mg u := by
    intro u hu i
    have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => P₀) i
    rw [hmg_eq u hu, ← hmp.map_eq,
      integral_map hmp.aemeasurable (hg_meas u).aestronglyMeasurable]
  have hemp_int : ∀ u ∈ J, Integrable (fun z => empProc ℓ P₀ xs z u) ν := by
    intro u hu
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun i _ => ?_
    exact (hg_coord_int u hu i).sub (integrable_const _)
  have hemp_mean_zero : ∀ u ∈ J, ∫ z', empProc ℓ P₀ xs z' u ∂ν = 0 := by
    intro u hu
    have hrew : (fun z' : Fin n → Ξ => empProc ℓ P₀ xs z' u) =
        fun z' => (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (g u (z' i) - mg u) := rfl
    have hint_sub : ∀ i : Fin n, Integrable (fun a : Fin n → Ξ => g u (a i) - mg u) ν :=
      fun i => (hg_coord_int u hu i).sub (integrable_const _)
    rw [hrew, integral_const_mul,
      integral_finsetSum Finset.univ (f := fun i (a : Fin n → Ξ) => g u (a i) - mg u)
        (fun i _ => hint_sub i)]
    have hsum_zero : (∑ i : Fin n, ∫ a, (g u (a i) - mg u) ∂ν) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_sub (hg_coord_int u hu i) (integrable_const _),
        hg_coord_mean u hu i, integral_const, probReal_univ, one_smul, sub_self]
    rw [hsum_zero, mul_zero]
  set D_J : ℝ := ∑ u ∈ J, ‖u - xs‖
  have hD_nonneg : 0 ≤ D_J := Finset.sum_nonneg fun u _ => norm_nonneg _
  set H : (Fin n → Ξ) × (Fin n → Ξ) → ℝ :=
    fun p => J.sup' hJ (fun u =>
      |(1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (g u (p.1 i) - g u (p.2 i))|)
  have hH_meas : Measurable H := by
    refine measurable_finset_sup' J hJ _ fun u _ => ?_
    refine Measurable.abs (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((hg_meas u).comp ((measurable_pi_apply i).comp measurable_fst)).sub
      ((hg_meas u).comp ((measurable_pi_apply i).comp measurable_snd))
  have hH_bound : ∀ p : (Fin n → Ξ) × (Fin n → Ξ),
      H p ≤ (1 / Real.sqrt (n : ℝ)) * D_J * ∑ i : Fin n, (M (p.1 i) + M (p.2 i)) := by
    intro p
    refine Finset.sup'_le hJ _ fun u hu => ?_
    have hnorm_le : ‖u - xs‖ ≤ D_J :=
      Finset.single_le_sum (fun v _ => norm_nonneg (v - xs)) hu
    calc
      |(1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (g u (p.1 i) - g u (p.2 i))|
          = (1 / Real.sqrt (n : ℝ)) * |∑ i : Fin n, (g u (p.1 i) - g u (p.2 i))| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (|g u (p.1 i)| + |g u (p.2 i)|) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => abs_sub _ _)
      _ ≤ (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (M (p.1 i) + M (p.2 i)) * ‖u - xs‖ := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
            linarith [hg_lip u hu (p.1 i), hg_lip u hu (p.2 i)]
      _ = (1 / Real.sqrt (n : ℝ)) * ‖u - xs‖ * ∑ i : Fin n, (M (p.1 i) + M (p.2 i)) := by
            rw [← Finset.sum_mul]; ring
      _ ≤ (1 / Real.sqrt (n : ℝ)) * D_J * ∑ i : Fin n, (M (p.1 i) + M (p.2 i)) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact mul_le_mul_of_nonneg_left hnorm_le (by positivity)
            · exact Finset.sum_nonneg fun i _ => add_nonneg (hB.2.2.1 _) (hB.2.2.1 _)
  have hH_nonneg : ∀ p, 0 ≤ H p := by
    intro p
    obtain ⟨u₀, hu₀⟩ := hJ
    exact le_trans (abs_nonneg _) (Finset.le_sup'
      (fun u => |(1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (g u (p.1 i) - g u (p.2 i))|) hu₀)
  have hH_int_right : ∀ z : Fin n → Ξ, Integrable (fun z' => H (z, z')) ν := by
    intro z
    refine integrable_of_nonneg_le
      (hH_meas.comp (measurable_const.prodMk measurable_id))
      (fun z' => hH_nonneg (z, z'))
      (fun z' => hH_bound (z, z')) ?_
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun i _ => ?_
    exact (integrable_const (M (z i))).add (hM_coord_int i)
  have hH_int_prod : Integrable H (ν.prod ν) := by
    refine integrable_of_nonneg_le hH_meas hH_nonneg hH_bound ?_
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun i _ => ?_
    exact ((hM_coord_int i).comp_fst ν).add ((hM_coord_int i).comp_snd ν)
  have hsup_emp_meas : Measurable (fun z : Fin n → Ξ =>
      J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|)) := by
    refine measurable_finset_sup' J hJ _ fun u _ => ?_
    refine Measurable.abs (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((hg_meas u).comp (measurable_pi_apply i)).sub measurable_const
  have hsup_emp_int : Integrable (fun z : Fin n → Ξ =>
      J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|)) ν := by
    refine integrable_of_nonneg_le hsup_emp_meas
      (fun z => by
        obtain ⟨u₀, hu₀⟩ := hJ
        exact le_trans (abs_nonneg _)
          (Finset.le_sup' (fun u => |empProc ℓ P₀ xs z u|) hu₀))
      (B := fun z => ∑ u ∈ J, |empProc ℓ P₀ xs z u|)
      (fun z => Finset.sup'_le hJ _ fun u hu =>
        Finset.single_le_sum (fun v _ => abs_nonneg (empProc ℓ P₀ xs z v)) hu)
      (integrable_finsetSum _ fun u hu => (hemp_int u hu).abs)
  have hpt_jensen : ∀ z : Fin n → Ξ,
      J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) ≤ ∫ z', H (z, z') ∂ν := by
    intro z
    refine Finset.sup'_le hJ _ fun u hu => ?_
    have hid : empProc ℓ P₀ xs z u = ∫ z', (empProc ℓ P₀ xs z u - empProc ℓ P₀ xs z' u) ∂ν := by
      rw [integral_sub (integrable_const _) (hemp_int u hu), hemp_mean_zero u hu, sub_zero,
        integral_const, probReal_univ, one_smul]
    have hdiff : ∀ z', empProc ℓ P₀ xs z u - empProc ℓ P₀ xs z' u =
        (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (g u (z i) - g u (z' i)) := by
      intro z'
      dsimp [empProc, g, mg]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    calc
      |empProc ℓ P₀ xs z u|
          = |∫ z', (empProc ℓ P₀ xs z u - empProc ℓ P₀ xs z' u) ∂ν| := congrArg abs hid
      _ ≤ ∫ z', |empProc ℓ P₀ xs z u - empProc ℓ P₀ xs z' u| ∂ν :=
          abs_integral_le_integral_abs _
      _ ≤ ∫ z', H (z, z') ∂ν := by
          refine integral_mono ((integrable_const _).sub (hemp_int u hu)).abs (hH_int_right z) ?_
          intro z'
          dsimp only
          rw [hdiff z']
          exact Finset.le_sup'
            (fun v => |(1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (g v (z i) - g v (z' i))|) hu
  have hstep1 :
      ∫ z, J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) ∂ν ≤ ∫ p, H p ∂(ν.prod ν) := by
    calc
      ∫ z, J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) ∂ν
          ≤ ∫ z, (∫ z', H (z, z') ∂ν) ∂ν :=
            integral_mono hsup_emp_int hH_int_prod.integral_prod_left hpt_jensen
      _ = ∫ p, H p ∂(ν.prod ν) := (integral_prod H hH_int_prod).symm
  -- Transfer from `ν.prod ν` to `μ_pair := Measure.pi (fun _ : Fin n => P₀.prod P₀)`
  set μ_pair : Measure (Fin n → Ξ × Ξ) := Measure.pi (fun _ : Fin n => P₀.prod P₀)
  have hmp_split :
      MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow Ξ Ξ (Fin n)) μ_pair (ν.prod ν) :=
    MeasureTheory.measurePreserving_arrowProdEquivProdArrow Ξ Ξ (Fin n)
      (fun _ => P₀) (fun _ => P₀)
  set Hw : (Fin n → Ξ × Ξ) → ℝ := H ∘ (MeasurableEquiv.arrowProdEquivProdArrow Ξ Ξ (Fin n))
  have hHw_meas : Measurable Hw :=
    hH_meas.comp (MeasurableEquiv.arrowProdEquivProdArrow Ξ Ξ (Fin n)).measurable
  have hsplit_eq : ∫ p, H p ∂(ν.prod ν) = ∫ w, Hw w ∂μ_pair := by
    rw [← hmp_split.map_eq, integral_map hmp_split.aemeasurable hH_meas.aestronglyMeasurable]
    rfl
  -- Coordinatewise conditional swap for each sign vector `σ : Fin n → Bool`
  have hswap_eq : ∀ σ : Fin n → Bool,
      ∫ w, Hw w ∂μ_pair =
        ∫ w, J.sup' hJ (fun u =>
          |(1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|) ∂μ_pair := by
    intro σ
    set swCoord : Bool → Ξ × Ξ → Ξ × Ξ := fun b p => if b then p else p.swap
    set sw : (Fin n → Ξ × Ξ) → (Fin n → Ξ × Ξ) := fun w i => swCoord (σ i) (w i)
    have hmp_sw : MeasurePreserving sw μ_pair μ_pair := by
      refine MeasureTheory.measurePreserving_pi
        (fun _ : Fin n => P₀.prod P₀) (fun _ : Fin n => P₀.prod P₀)
        (f := fun i => swCoord (σ i)) (fun i => ?_)
      cases σ i
      · exact ⟨measurable_swap, Measure.prod_swap⟩
      · exact ⟨measurable_id, Measure.map_id⟩
    have hcomp_eq : ∀ w : Fin n → Ξ × Ξ,
        Hw (sw w) = J.sup' hJ (fun u =>
          |(1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|) := by
      intro w
      change J.sup' hJ (fun u =>
          |(1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, (g u (sw w i).1 - g u (sw w i).2)|) =
        J.sup' hJ (fun u =>
          |(1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|)
      congr 1; ext u; congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [sw, swCoord]
      cases σ i <;> simp [radSign]
    have hint_sw : ∫ w, Hw w ∂μ_pair = ∫ w, Hw (sw w) ∂μ_pair := by
      conv_lhs => rw [← hmp_sw.map_eq]
      rw [integral_map hmp_sw.aemeasurable hHw_meas.aestronglyMeasurable]
    rw [hint_sw]
    exact integral_congr_ae (Filter.Eventually.of_forall hcomp_eq)
  -- Project `fst` and `snd` from `μ_pair` back to `ν`
  have hmp_fst : MeasurePreserving (fun (w : Fin n → Ξ × Ξ) i => (w i).1) μ_pair ν :=
    MeasureTheory.measurePreserving_pi
      (fun _ : Fin n => P₀.prod P₀) (fun _ : Fin n => P₀)
      (fun _ => ⟨measurable_fst, Measure.fst_prod⟩)
  have hmp_snd : MeasurePreserving (fun (w : Fin n → Ξ × Ξ) i => (w i).2) μ_pair ν :=
    MeasureTheory.measurePreserving_pi
      (fun _ : Fin n => P₀.prod P₀) (fun _ : Fin n => P₀)
      (fun _ => ⟨measurable_snd, Measure.snd_prod⟩)
  set radMax : (Fin n → Bool) → (Fin n → Ξ) → ℝ :=
    fun σ z => J.sup' hJ (fun u => |radProc ℓ xs z σ u|)
  have hradMax_meas : ∀ σ, Measurable (radMax σ) := by
    intro σ
    refine measurable_finset_sup' J hJ _ fun u _ => ?_
    refine Measurable.abs (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.const_mul ((hg_meas u).comp (measurable_pi_apply i)) _
  have hradMax_int : ∀ σ, Integrable (radMax σ) ν := by
    intro σ
    refine integrable_of_nonneg_le (hradMax_meas σ)
      (fun z => by
        obtain ⟨u₀, hu₀⟩ := hJ
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun u => |radProc ℓ xs z σ u|) hu₀))
      (B := fun z => (1 / Real.sqrt (n : ℝ)) * D_J * ∑ i : Fin n, M (z i))
      (fun z => ?_)
      (Integrable.const_mul (integrable_finsetSum _ fun i _ => hM_coord_int i) _)
    refine Finset.sup'_le hJ _ fun u hu => ?_
    have hnorm_le : ‖u - xs‖ ≤ D_J :=
      Finset.single_le_sum (fun v _ => norm_nonneg (v - xs)) hu
    calc
      |radProc ℓ xs z σ u|
          = (1 / Real.sqrt (n : ℝ)) * |∑ i : Fin n, radSign (σ i) * g u (z i)| := by
            dsimp [radProc, g]
            rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, |radSign (σ i) * g u (z i)| := by
            exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, M (z i) * ‖u - xs‖ := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
            rw [abs_mul, show |radSign (σ i)| = 1 by cases σ i <;> simp [radSign], one_mul]
            exact hg_lip u hu (z i)
      _ = (1 / Real.sqrt (n : ℝ)) * ‖u - xs‖ * ∑ i : Fin n, M (z i) := by
            rw [← Finset.sum_mul]; ring
      _ ≤ (1 / Real.sqrt (n : ℝ)) * D_J * ∑ i : Fin n, M (z i) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnorm_le (by positivity))
              (Finset.sum_nonneg fun i _ => hB.2.2.1 _)
  have hsingle_σ : ∀ σ : Fin n → Bool,
      ∫ w, Hw w ∂μ_pair ≤ 2 * ∫ z, radMax σ z ∂ν := by
    intro σ
    rw [hswap_eq σ]
    have hrad_fst_int : Integrable (fun w : Fin n → Ξ × Ξ => radMax σ (fun i => (w i).1)) μ_pair :=
      integrable_comp_mp hmp_fst (hradMax_meas σ) (hradMax_int σ)
    have hrad_snd_int : Integrable (fun w : Fin n → Ξ × Ξ => radMax σ (fun i => (w i).2)) μ_pair :=
      integrable_comp_mp hmp_snd (hradMax_meas σ) (hradMax_int σ)
    have hpt : ∀ w : Fin n → Ξ × Ξ,
        J.sup' hJ (fun u =>
          |(1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|) ≤
          radMax σ (fun i => (w i).1) + radMax σ (fun i => (w i).2) := by
      intro w
      refine Finset.sup'_le hJ _ fun u hu => ?_
      have hsplit_u :
          (1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2) =
            radProc ℓ xs (fun i => (w i).1) σ u -
              radProc ℓ xs (fun i => (w i).2) σ u := by
        dsimp [radProc, g]
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit_u]
      exact (abs_sub _ _).trans (add_le_add
        (Finset.le_sup' (fun v => |radProc ℓ xs (fun i => (w i).1) σ v|) hu)
        (Finset.le_sup' (fun v => |radProc ℓ xs (fun i => (w i).2) σ v|) hu))
    have hint_lhs : Integrable (fun w : Fin n → Ξ × Ξ =>
        J.sup' hJ (fun u =>
          |(1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|)) μ_pair := by
      have hmeas_lhs : Measurable (fun w : Fin n → Ξ × Ξ =>
          J.sup' hJ (fun u =>
            |(1 / Real.sqrt (n : ℝ)) *
              ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|)) := by
        refine measurable_finset_sup' J hJ _ fun u _ => ?_
        refine Measurable.abs (Measurable.const_mul ?_ _)
        refine Finset.measurable_sum _ fun i _ => ?_
        exact Measurable.const_mul
          (((hg_meas u).comp (measurable_fst.comp (measurable_pi_apply i))).sub
            ((hg_meas u).comp (measurable_snd.comp (measurable_pi_apply i)))) _
      exact integrable_of_nonneg_le hmeas_lhs
        (fun w => by
          obtain ⟨u₀, hu₀⟩ := hJ
          exact le_trans (abs_nonneg _) (Finset.le_sup'
            (fun u => |(1 / Real.sqrt (n : ℝ)) *
              ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|) hu₀))
        hpt
        (hrad_fst_int.add hrad_snd_int)
    have hf1 : ∫ w, radMax σ (fun i => (w i).1) ∂μ_pair = ∫ z, radMax σ z ∂ν := by
      rw [← hmp_fst.map_eq, integral_map hmp_fst.aemeasurable (hradMax_meas σ).aestronglyMeasurable]
    have hf2 : ∫ w, radMax σ (fun i => (w i).2) ∂μ_pair = ∫ z, radMax σ z ∂ν := by
      rw [← hmp_snd.map_eq, integral_map hmp_snd.aemeasurable (hradMax_meas σ).aestronglyMeasurable]
    calc
      ∫ w, J.sup' hJ (fun u =>
          |(1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, radSign (σ i) * (g u (w i).1 - g u (w i).2)|) ∂μ_pair
          ≤ ∫ w, (radMax σ (fun i => (w i).1) + radMax σ (fun i => (w i).2)) ∂μ_pair :=
            integral_mono hint_lhs (hrad_fst_int.add hrad_snd_int) hpt
      _ = (∫ w, radMax σ (fun i => (w i).1) ∂μ_pair) +
            (∫ w, radMax σ (fun i => (w i).2) ∂μ_pair) :=
            integral_add hrad_fst_int hrad_snd_int
      _ = 2 * ∫ z, radMax σ z ∂ν := by rw [hf1, hf2]; ring
  -- Average over all `σ : Fin n → Bool`
  calc
    ∫ z, J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) ∂ν
        ≤ ∫ w, Hw w ∂μ_pair := hstep1.trans_eq hsplit_eq
    _ = ((2 : ℝ)⁻¹ ^ n) * ∑ _σ : Fin n → Bool, ∫ w, Hw w ∂μ_pair :=
          (rademacher_avg_const _).symm
    _ ≤ ((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, (2 * ∫ z, radMax σ z ∂ν) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hsingle_σ σ) (by positivity)
    _ = 2 * ∫ z, (((2 : ℝ)⁻¹ ^ n) * ∑ σ : Fin n → Bool, radMax σ z) ∂ν := by
          rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hradMax_int σ),
            ← Finset.mul_sum]
          ring

/-- Measurable envelope for `sup_{x ∈ X ∩ closedBall xs r} |empProc ℓ P₀ xs z x|`. -/
lemma exists_empProc_envelope {d : ℕ} (n : ℕ) {Ξ : Type*} [MeasurableSpace Ξ]
    (P₀ : Measure Ξ) [IsProbabilityMeasure P₀]
    {X : Set (EuclideanSpace ℝ (Fin d))} {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ}
    {M : Ξ → ℝ} {xs : EuclideanSpace ℝ (Fin d)}
    (hn : 0 < n) (hB : AssumptionB X ℓ M) (hℓmeas : ∀ x, Measurable (ℓ x))
    (hM2 : Integrable (fun z₀ => M z₀ ^ 2) P₀)
    (hℓ_int : ∀ x ∈ X, Integrable (ℓ x) P₀)
    (hxs : xs ∈ X) {r : ℝ} (hr : 0 < r) :
    ∃ U : (Fin n → Ξ) → ℝ,
      Measurable U ∧
      (∀ z, 0 ≤ U z) ∧
      Integrable U (Measure.pi (fun _ : Fin n => P₀)) ∧
      (∀ z, ∀ x ∈ X ∩ Metric.closedBall xs r, |empProc ℓ P₀ xs z x| ≤ U z) ∧
      ∫ z, U z ∂(Measure.pi (fun _ : Fin n => P₀)) ≤
        (16 * (2 + (d : ℝ) * ((d : ℝ) + 4)) + 2) * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1) * r := by
  set ν : Measure (Fin n → Ξ) := Measure.pi (fun _ : Fin n => P₀)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hM_int : Integrable M P₀ :=
    integrable_of_nonneg_le hB.2.1 hB.2.2.1
      (fun z₀ => (le_abs_self (M z₀)).trans (abs_le_sq_add_one (M z₀)))
      (hM2.add (integrable_const 1))
  have hEM_nonneg : 0 ≤ ∫ z₀, M z₀ ∂P₀ := integral_nonneg hB.2.2.1
  have hEM_le : ∫ z₀, M z₀ ∂P₀ ≤ (∫ z₀, M z₀ ^ 2 ∂P₀) + 1 := by
    calc
      ∫ z₀, M z₀ ∂P₀ ≤ ∫ z₀, (M z₀ ^ 2 + 1) ∂P₀ :=
        integral_mono hM_int (hM2.add (integrable_const 1))
          (fun z₀ => (le_abs_self (M z₀)).trans (abs_le_sq_add_one (M z₀)))
      _ = (∫ z₀, M z₀ ^ 2 ∂P₀) + 1 := by
        rw [integral_add hM2 (integrable_const 1), integral_const, probReal_univ, one_smul]
  set J := dyadicNet X xs r n
  have hJ : J.Nonempty := dyadicNet_nonempty X xs r n
  have hJX : ∀ u ∈ J, u ∈ X := fun u hu => (dyadicNet_subset hxs hr.le n u hu).1
  set U : (Fin n → Ξ) → ℝ :=
    fun z =>
      J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) +
        Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n *
          ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * r
  have hU1_meas : Measurable (fun z : Fin n → Ξ =>
      J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|)) := by
    refine measurable_finset_sup' J hJ _ fun u _ => ?_
    refine Measurable.abs (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((hℓmeas u).sub (hℓmeas xs)).comp (measurable_pi_apply i)).sub measurable_const
  have hU2_meas : Measurable (fun z : Fin n → Ξ =>
      Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * r) := by
    refine (Measurable.const_mul ?_ _).mul_const r
    refine (Measurable.const_mul ?_ _).add_const _
    exact Finset.measurable_sum _ fun i _ => hB.2.1.comp (measurable_pi_apply i)
  have hU_meas : Measurable U := hU1_meas.add hU2_meas
  have hU_nonneg : ∀ z, 0 ≤ U z := by
    intro z
    refine add_nonneg ?_ ?_
    · obtain ⟨u₀, hu₀⟩ := hJ
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun u => |empProc ℓ P₀ xs z u|) hu₀)
    · have : 0 ≤ ∑ i : Fin n, M (z i) := Finset.sum_nonneg fun i _ => hB.2.2.1 (z i)
      positivity
  have hM_coord_int : ∀ i : Fin n, Integrable (fun z : Fin n → Ξ => M (z i)) ν := fun i =>
    integrable_comp_mp (MeasureTheory.measurePreserving_eval (fun _ => P₀) i) hB.2.1 hM_int
  have hM2_coord_int : ∀ i : Fin n, Integrable (fun z : Fin n → Ξ => M (z i) ^ 2) ν := fun i =>
    integrable_comp_mp (MeasureTheory.measurePreserving_eval (fun _ => P₀) i)
      (hB.2.1.pow_const 2) hM2
  have hU1_int : Integrable (fun z : Fin n → Ξ =>
      J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|)) ν := by
    refine integrable_of_nonneg_le hU1_meas
      (fun z => by
        obtain ⟨u₀, hu₀⟩ := hJ
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun u => |empProc ℓ P₀ xs z u|) hu₀))
      (B := fun z => ∑ u ∈ J, |empProc ℓ P₀ xs z u|)
      (fun z => Finset.sup'_le hJ _ fun u hu =>
        Finset.single_le_sum (f := fun v => |empProc ℓ P₀ xs z v|) (fun v _ => abs_nonneg _) hu) ?_
    refine integrable_finsetSum _ fun u hu => ?_
    refine (Integrable.const_mul ?_ _).abs
    refine integrable_finsetSum _ fun i _ => ?_
    exact (integrable_comp_mp (MeasureTheory.measurePreserving_eval (fun _ => P₀) i)
      ((hℓmeas u).sub (hℓmeas xs))
      ((hℓ_int u (hJX u hu)).sub (hℓ_int xs hxs))).sub (integrable_const _)
  have hU2_int : Integrable (fun z : Fin n → Ξ =>
      Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * r) ν := by
    refine (Integrable.const_mul ?_ _).mul_const r
    exact (Integrable.const_mul (integrable_finsetSum _ fun i _ => hM_coord_int i) _).add
      (integrable_const _)
  have hU_int : Integrable U ν := hU1_int.add hU2_int
  -- Pointwise domination on `X ∩ closedBall xs r`
  have hU_dom : ∀ z, ∀ x ∈ X ∩ Metric.closedBall xs r, |empProc ℓ P₀ xs z x| ≤ U z := by
    intro z x hx
    have hspec := netProj_spec hxs hr n hx
    set u := netProj X xs r n x
    have hu_J : u ∈ J := hspec.1
    have hu_X : u ∈ X := hJX u hu_J
    have hdist : ‖x - u‖ ≤ (2 : ℝ)⁻¹ ^ n * r := hspec.2
    have hF_lip : |(∫ z₀, ℓ x z₀ ∂P₀) - (∫ z₀, ℓ u z₀ ∂P₀)| ≤ (∫ z₀, M z₀ ∂P₀) * ‖x - u‖ := by
      rw [← integral_sub (hℓ_int x hx.1) (hℓ_int u hu_X)]
      calc
        |∫ z₀, (ℓ x z₀ - ℓ u z₀) ∂P₀|
            ≤ ∫ z₀, |ℓ x z₀ - ℓ u z₀| ∂P₀ := abs_integral_le_integral_abs _
        _ ≤ ∫ z₀, (M z₀ * ‖x - u‖) ∂P₀ :=
            integral_mono ((hℓ_int x hx.1).sub (hℓ_int u hu_X)).abs (hM_int.mul_const _)
              (fun z₀ => hB.2.2.2 z₀ x hx.1 u hu_X)
        _ = (∫ z₀, M z₀ ∂P₀) * ‖x - u‖ := integral_mul_const _ _
    have hdiff_emp :
        |empProc ℓ P₀ xs z x - empProc ℓ P₀ xs z u| ≤
          Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n *
            ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * r := by
      have hrew : empProc ℓ P₀ xs z x - empProc ℓ P₀ xs z u =
          (1 / Real.sqrt (n : ℝ)) *
            ∑ i : Fin n, ((ℓ x (z i) - ℓ u (z i)) -
              (∫ z₀, ℓ x z₀ ∂P₀ - ∫ z₀, ℓ u z₀ ∂P₀)) := by
        dsimp [empProc]
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hrew, abs_mul, abs_of_nonneg (by positivity)]
      have hsum_lip :
          |∑ i : Fin n, ((ℓ x (z i) - ℓ u (z i)) -
              (∫ z₀, ℓ x z₀ ∂P₀ - ∫ z₀, ℓ u z₀ ∂P₀))| ≤
            (∑ i : Fin n, M (z i) + (n : ℝ) * ∫ z₀, M z₀ ∂P₀) * ‖x - u‖ := by
        calc
          |∑ i : Fin n, ((ℓ x (z i) - ℓ u (z i)) -
              (∫ z₀, ℓ x z₀ ∂P₀ - ∫ z₀, ℓ u z₀ ∂P₀))|
              ≤ ∑ i : Fin n, (|ℓ x (z i) - ℓ u (z i)| +
                  |∫ z₀, ℓ x z₀ ∂P₀ - ∫ z₀, ℓ u z₀ ∂P₀|) :=
                (Finset.abs_sum_le_sum_abs _ _).trans
                  (Finset.sum_le_sum fun i _ => abs_sub _ _)
          _ ≤ ∑ i : Fin n, (M (z i) * ‖x - u‖ + (∫ z₀, M z₀ ∂P₀) * ‖x - u‖) :=
                Finset.sum_le_sum fun i _ => add_le_add (hB.2.2.2 (z i) x hx.1 u hu_X) hF_lip
          _ = (∑ i : Fin n, M (z i) + (n : ℝ) * ∫ z₀, M z₀ ∂P₀) * ‖x - u‖ := by
                simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
                  Finset.card_fin, nsmul_eq_mul]
                ring
      have hsqrt_id :
          (1 / Real.sqrt (n : ℝ)) * (∑ i : Fin n, M (z i) + (n : ℝ) * ∫ z₀, M z₀ ∂P₀) =
            Real.sqrt (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) := by
        have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt hn_pos.le
        have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn_pos)
        field_simp [hne, ne_of_gt hn_pos]
        rw [sq, hsq]
      calc
        (1 / Real.sqrt (n : ℝ)) *
            |∑ i : Fin n, ((ℓ x (z i) - ℓ u (z i)) -
              (∫ z₀, ℓ x z₀ ∂P₀ - ∫ z₀, ℓ u z₀ ∂P₀))|
            ≤ (1 / Real.sqrt (n : ℝ)) *
                ((∑ i : Fin n, M (z i) + (n : ℝ) * ∫ z₀, M z₀ ∂P₀) * ‖x - u‖) :=
              mul_le_mul_of_nonneg_left hsum_lip (by positivity)
        _ = Real.sqrt (n : ℝ) *
              ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * ‖x - u‖ := by
              rw [← mul_assoc, hsqrt_id]
        _ ≤ Real.sqrt (n : ℝ) *
              ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * ((2 : ℝ)⁻¹ ^ n * r) := by
              refine mul_le_mul_of_nonneg_left hdist ?_
              have : 0 ≤ ∑ i : Fin n, M (z i) := Finset.sum_nonneg fun i _ => hB.2.2.1 (z i)
              positivity
        _ = Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n *
              ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * r := by ring
    have htri : |empProc ℓ P₀ xs z x| ≤
        |empProc ℓ P₀ xs z u| + |empProc ℓ P₀ xs z x - empProc ℓ P₀ xs z u| := by
      have := abs_add_le (empProc ℓ P₀ xs z u) (empProc ℓ P₀ xs z x - empProc ℓ P₀ xs z u)
      simpa using this
    exact htri.trans (add_le_add (Finset.le_sup' (fun v => |empProc ℓ P₀ xs z v|) hu_J) hdiff_emp)
  -- Expectation bound on `U`
  have hmean_M : ∫ z, ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i)) ∂ν = ∫ z₀, M z₀ ∂P₀ := by
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hM_coord_int i)]
    have hcoord : ∀ i : Fin n, ∫ z, M (z i) ∂ν = ∫ z₀, M z₀ ∂P₀ := by
      intro i
      have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => P₀) i
      rw [← hmp.map_eq, integral_map hmp.aemeasurable hB.2.1.aestronglyMeasurable]
    simp_rw [hcoord, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_div,
      inv_mul_cancel_left₀ (ne_of_gt hn_pos)]
  have hmean_M2 :
      ∫ z, ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2 + 1) ∂ν = (∫ z₀, M z₀ ^ 2 ∂P₀) + 1 := by
    rw [integral_add
      (Integrable.const_mul (integrable_finsetSum _ fun i _ => hM2_coord_int i) _)
      (integrable_const 1),
      integral_const_mul, integral_finsetSum _ (fun i _ => hM2_coord_int i),
      integral_const, probReal_univ, one_smul]
    have hcoord : ∀ i : Fin n, ∫ z, M (z i) ^ 2 ∂ν = ∫ z₀, M z₀ ^ 2 ∂P₀ := by
      intro i
      have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => P₀) i
      rw [← hmp.map_eq, integral_map hmp.aemeasurable (hB.2.1.pow_const 2).aestronglyMeasurable]
    simp_rw [hcoord, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_div,
      inv_mul_cancel_left₀ (ne_of_gt hn_pos)]
  have hrad_int : Integrable
      (fun z : Fin n → Ξ => ((2 : ℝ)⁻¹ ^ n) *
        ∑ σ : Fin n → Bool, J.sup' hJ (fun u => |radProc ℓ xs z σ u|)) ν := by
    refine Integrable.const_mul (integrable_finsetSum _ fun σ _ => ?_) _
    have hmeas_σ : Measurable (fun z : Fin n → Ξ =>
        J.sup' hJ (fun u => |radProc ℓ xs z σ u|)) := by
      refine measurable_finset_sup' J hJ _ fun u _ => ?_
      refine Measurable.abs (Measurable.const_mul ?_ _)
      refine Finset.measurable_sum _ fun i _ => ?_
      exact Measurable.const_mul (((hℓmeas u).sub (hℓmeas xs)).comp (measurable_pi_apply i)) _
    refine integrable_of_nonneg_le hmeas_σ
      (fun z => by
        obtain ⟨u₀, hu₀⟩ := hJ
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun u => |radProc ℓ xs z σ u|) hu₀))
      (B := fun z => ∑ u ∈ J, |radProc ℓ xs z σ u|)
      (fun z => Finset.sup'_le hJ _ fun u hu =>
        Finset.single_le_sum (f := fun v => |radProc ℓ xs z σ v|) (fun _ _ => abs_nonneg _) hu)
      (integrable_finsetSum _ fun u hu => ?_)
    refine (Integrable.const_mul ?_ _).abs
    refine integrable_finsetSum _ fun i _ => ?_
    exact Integrable.const_mul
      (integrable_comp_mp (MeasureTheory.measurePreserving_eval (fun _ => P₀) i)
        ((hℓmeas u).sub (hℓmeas xs))
        ((hℓ_int u (hJX u hu)).sub (hℓ_int xs hxs))) _
  have hU1_exp :
      ∫ z, J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) ∂ν ≤
        16 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1) * r := by
    have hsym := rademacher_symmetrization n P₀ hB hℓmeas hM_int hℓ_int hxs J hJ hJX
    have hchain_int : Integrable (fun z : Fin n → Ξ =>
        8 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r *
          ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2 + 1)) ν :=
      Integrable.const_mul
        ((Integrable.const_mul (integrable_finsetSum _ fun i _ => hM2_coord_int i) _).add
          (integrable_const 1)) _
    calc
      ∫ z, J.sup' hJ (fun u => |empProc ℓ P₀ xs z u|) ∂ν
          ≤ 2 * ∫ z, (((2 : ℝ)⁻¹ ^ n) *
              ∑ σ : Fin n → Bool, J.sup' hJ (fun u => |radProc ℓ xs z σ u|)) ∂ν := hsym
      _ ≤ 2 * ∫ z, (8 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * r *
              ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2 + 1)) ∂ν := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact integral_mono hrad_int hchain_int
              (fun z => rademacher_chaining_bound hn hB hxs hr z n)
      _ = 16 * (2 + (d : ℝ) * ((d : ℝ) + 4)) * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1) * r := by
            rw [integral_const_mul, hmean_M2]
            ring
  have hU2_exp :
      ∫ z, (Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n *
          ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * r) ∂ν ≤
        2 * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1) * r := by
    have h1 := sqrt_nat_mul_two_inv_pow_le_one n
    have hrew :
        ∫ z, (Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n *
            ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) + ∫ z₀, M z₀ ∂P₀) * r) ∂ν =
          Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n * (2 * ∫ z₀, M z₀ ∂P₀) * r := by
      simp_rw [mul_assoc (Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n)]
      rw [integral_const_mul, integral_mul_const,
        integral_add (Integrable.const_mul (integrable_finsetSum _ fun i _ => hM_coord_int i) _)
          (integrable_const _),
        hmean_M, integral_const, probReal_univ, one_smul]
      ring
    rw [hrew]
    calc
      Real.sqrt (n : ℝ) * (2 : ℝ)⁻¹ ^ n * (2 * ∫ z₀, M z₀ ∂P₀) * r
          ≤ 1 * (2 * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1)) * r := by
            refine mul_le_mul_of_nonneg_right ?_ hr.le
            exact mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
      _ = 2 * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1) * r := by ring
  refine ⟨U, hU_meas, hU_nonneg, hU_int, hU_dom, ?_⟩
  rw [integral_add hU1_int hU2_int]
  linarith

/-! ### 5. Remainder representation, `lemma_13` shift bound, and deterministic localization -/

lemma limsup_ennreal_eq_zero_of_forall_pos {u : ℕ → ENNReal}
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, u n ≤ ENNReal.ofReal η) :
    Filter.limsup u atTop = 0 := by
  have hle : ∀ η : ℝ, 0 < η → Filter.limsup u atTop ≤ ENNReal.ofReal η := by
    intro η hη
    rw [Filter.limsup_eq]
    exact csInf_le (OrderBot.bddBelow _) (h η hη)
  set x := Filter.limsup u atTop
  have hx_lt_top : x < ⊤ := (hle 1 one_pos).trans_lt ENNReal.ofReal_lt_top
  have hx_ne_top : x ≠ ⊤ := hx_lt_top.ne
  have hx_real_zero : x.toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra hnot
    have hpos : 0 < x.toReal := lt_of_not_ge hnot
    have hhalf := hle (x.toReal / 2) (by linarith)
    have := ENNReal.toReal_le_of_le_ofReal (by linarith) hhalf
    linarith
  rw [← ENNReal.ofReal_toReal hx_ne_top, hx_real_zero, ENNReal.ofReal_zero]

lemma divergenceBall_nonempty (f : ℝ → EReal) (hA : AssumptionA f)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {n : ℕ} (hn : 0 < n) :
    (divergenceBall f ρ n).Nonempty := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  refine ⟨fun _ : Fin n => (1 : ℝ) / (n : ℝ), ?_⟩
  refine ⟨fun _ => by positivity, ?_, ?_⟩
  · simp [Finset.sum_const, mul_inv_cancel₀ (ne_of_gt hn_pos)]
  · have hq : ((1 : ℝ) / (n : ℝ)) / ((1 : ℝ) / (n : ℝ)) = 1 :=
      div_self (ne_of_gt (div_pos one_pos hn_pos))
    have hphi : PhiDivRobust.Counterpart.phiDiv f
        (fun _ : Fin n => (1 : ℝ) / (n : ℝ)) (fun _ : Fin n => (1 : ℝ) / (n : ℝ)) = 0 := by
      unfold PhiDivRobust.Counterpart.phiDiv
      simp_rw [hq, hA.1.map_one, mul_zero, Finset.sum_const_zero]
    rw [hphi]
    exact EReal.coe_nonneg.mpr (div_nonneg hρ hn_pos.le)

lemma divergenceBall_mono (f : ℝ → EReal) {ρ ρ' : ℝ} (h : ρ ≤ ρ') (n : ℕ) :
    divergenceBall f ρ n ⊆ divergenceBall f ρ' n := by
  intro p hp
  refine ⟨hp.1, hp.2.1, hp.2.2.trans ?_⟩
  exact EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_right h (Nat.cast_nonneg n))

lemma remainder_le_on_good_event {d n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P₀ : Measure Ξ)
    {X : Set (EuclideanSpace ℝ (Fin d))} {ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ}
    {M : Ξ → ℝ} {f : ℝ → EReal} {ρ ρ' Cf K_M R δ L_R γ ε : ℝ}
    {xs : EuclideanSpace ℝ (Fin d)}
    (hn : 0 < n) (hρ_le : ρ ≤ ρ') (hρ'_pos : 0 < ρ') (hCf_pos : 0 < Cf)
    (hKM_pos : 0 < K_M) (hX : X.Nonempty) (hB : AssumptionB X ℓ M)
    (hxs_mem : xs ∈ X)
    (hxs_min : ∀ y ∈ X, (∫ z₀, ℓ xs z₀ ∂P₀) ≤ (∫ z₀, ℓ y z₀ ∂P₀))
    (hopt_eq : optimalValue X ℓ P₀ = ∫ z₀, ℓ xs z₀ ∂P₀)
    (hX_sub_R : X ⊆ Metric.closedBall xs R)
    (hl13 : ∀ p ∈ divergenceBall f ρ' n,
      Real.sqrt (∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2) ≤ Real.sqrt (ρ' * Cf))
    (hγ_sep : ∀ x ∈ X \ Metric.ball xs δ,
      γ ≤ (∫ z₀, ℓ x z₀ ∂P₀) - (∫ z₀, ℓ xs z₀ ∂P₀))
    (hn_large : (L_R + Real.sqrt (ρ' * Cf) * Real.sqrt K_M * R) / Real.sqrt (n : ℝ) < γ)
    (hδ_shift : Real.sqrt (ρ' * Cf) * Real.sqrt K_M * δ ≤ ε / 4)
    {z : Fin n → Ξ} {U_R U_δ : ℝ}
    (hz1 : (1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2 < K_M)
    (hUR_dom : ∀ x ∈ X ∩ Metric.closedBall xs R, |empProc ℓ P₀ xs z x| ≤ U_R)
    (hz2 : U_R < L_R)
    (hUδ_dom : ∀ x ∈ X ∩ Metric.closedBall xs δ, |empProc ℓ P₀ xs z x| ≤ U_δ)
    (hz3 : U_δ < ε / 4) :
    ∀ p ∈ divergenceBall f ρ n,
      |remainder X ℓ P₀ xs z p| ≤ ε / (2 * Real.sqrt (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∫ z₀, ℓ x z₀ ∂P₀
  intro p hp
  have hp_nonneg : ∀ i : Fin n, 0 ≤ p i := hp.1
  have hp_sum : ∑ i : Fin n, p i = 1 := hp.2.1
  have hp' : p ∈ divergenceBall f ρ' n := divergenceBall_mono f hρ_le n hp
  set Φ : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∑ i : Fin n, p i * ℓ x (z i)
  have hΦ_cont : ContinuousOn Φ X := by
    rw [Metric.continuousOn_iff]
    intro x hx ε' hε'
    set LΦ : ℝ := ∑ i : Fin n, p i * M (z i)
    have hLΦ_nonneg : 0 ≤ LΦ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hp_nonneg i) (hB.2.2.1 (z i))
    refine ⟨ε' / (LΦ + 1), div_pos hε' (by linarith), fun y hy hdist => ?_⟩
    rw [Real.dist_eq]
    rw [dist_eq_norm] at hdist
    calc
      |Φ y - Φ x| = |∑ i : Fin n, p i * (ℓ y (z i) - ℓ x (z i))| := by
            dsimp [Φ]
            rw [← Finset.sum_sub_distrib]
            congr 1
            refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i : Fin n, p i * |ℓ y (z i) - ℓ x (z i)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [abs_mul, abs_of_nonneg (hp_nonneg i)]
      _ ≤ (LΦ + 1) * ‖y - x‖ := by
            have h1 : ∑ i : Fin n, p i * |ℓ y (z i) - ℓ x (z i)| ≤ LΦ * ‖y - x‖ := by
              dsimp [LΦ]
              rw [Finset.sum_mul]
              refine Finset.sum_le_sum fun i _ => ?_
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (hB.2.2.2 (z i) y hy x hx) (hp_nonneg i)
            nlinarith [norm_nonneg (y - x)]
      _ < (LΦ + 1) * (ε' / (LΦ + 1)) := mul_lt_mul_of_pos_left hdist (by linarith)
      _ = ε' := mul_div_cancel₀ ε' (ne_of_gt (by linarith))
  obtain ⟨_, hxhat_least⟩ :=
    (hB.1.image_of_continuousOn hΦ_cont).exists_isLeast (hX.image Φ)
  obtain ⟨⟨xhat, hxhat_X, rfl⟩, hxhat_min⟩ := hxhat_least
  have hemp_opt_eq : empiricalOptimalValue X ℓ z p = Φ xhat :=
    IsLeast.csInf_eq ⟨⟨xhat, hxhat_X, rfl⟩, hxhat_min⟩
  have hΦ_le_xs : Φ xhat ≤ Φ xs := hxhat_min ⟨xs, hxs_mem, rfl⟩
  have hrem_eq : remainder X ℓ P₀ xs z p = Φ xhat - Φ xs := by
    dsimp [remainder, influence]
    rw [hemp_opt_eq, hopt_eq]
    have hsum_inf :
        ∑ i : Fin n, p i * (ℓ xs (z i) - F xs) = Φ xs - F xs := by
      dsimp [Φ, F]
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
    dsimp [F] at hsum_inf ⊢
    linarith
  have habs_rem :
      |remainder X ℓ P₀ xs z p| = ∑ i : Fin n, p i * (ℓ xs (z i) - ℓ xhat (z i)) := by
    have hneg_sub : -(Φ xhat - Φ xs) = Φ xs - Φ xhat := by ring
    rw [hrem_eq, abs_of_nonpos (by linarith), hneg_sub]
    dsimp [Φ]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  -- Decomposition and Cauchy-Schwarz + `lemma_13` shift bound for any `x ∈ X`
  have hdecomp : ∀ x ∈ X,
      ∑ i : Fin n, p i * (ℓ xs (z i) - ℓ x (z i)) ≤
        (F xs - F x) + (1 / Real.sqrt (n : ℝ)) * |empProc ℓ P₀ xs z x| +
          (Real.sqrt (ρ' * Cf) * Real.sqrt K_M * ‖x - xs‖) / Real.sqrt (n : ℝ) := by
    intro x hx
    have halg :
        ∑ i : Fin n, p i * (ℓ xs (z i) - ℓ x (z i)) =
          (F xs - F x) - (1 / Real.sqrt (n : ℝ)) * empProc ℓ P₀ xs z x +
            ∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i)) := by
      dsimp [empProc, F]
      have hsqn : (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) = 1 / (n : ℝ) := by
        rw [one_div_mul_one_div, Real.mul_self_sqrt hn_pos.le]
      rw [← mul_assoc, hsqn]
      calc
        ∑ i : Fin n, p i * (ℓ xs (z i) - ℓ x (z i))
            = ∑ i : Fin n, ((1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i)) +
                (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i))) := by
              refine Finset.sum_congr rfl fun i _ => by ring
        _ = (1 / (n : ℝ)) * ∑ i : Fin n, (ℓ xs (z i) - ℓ x (z i)) +
              ∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = (F xs - F x) - (1 / (n : ℝ)) *
              ∑ i : Fin n, ((ℓ x (z i) - ℓ xs (z i)) - (F x - F xs)) +
              ∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i)) := by
              have h2 : ∑ i : Fin n, ((ℓ x (z i) - ℓ xs (z i)) - (F x - F xs)) =
                  -(∑ i : Fin n, (ℓ xs (z i) - ℓ x (z i))) + (n : ℝ) * (F xs - F x) := by
                simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
                  nsmul_eq_mul]
                have : ∑ i : Fin n, (ℓ x (z i) - ℓ xs (z i)) =
                    -∑ i : Fin n, (ℓ xs (z i) - ℓ x (z i)) := by
                  rw [← Finset.sum_neg_distrib]
                  refine Finset.sum_congr rfl fun i _ => by ring
                linarith
              rw [h2, mul_add, ← mul_assoc, one_div_mul_cancel (ne_of_gt hn_pos), one_mul]
              ring
    have hshift_sq :
        (∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i))) ^ 2 ≤
          ((Real.sqrt (ρ' * Cf) * Real.sqrt K_M * ‖x - xs‖) / Real.sqrt (n : ℝ)) ^ 2 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin n => p i - 1 / (n : ℝ))
        (fun i : Fin n => ℓ xs (z i) - ℓ x (z i))
      have hp_l2 : ∑ i : Fin n, (p i - 1 / (n : ℝ)) ^ 2 ≤ (ρ' * Cf) / (n : ℝ) ^ 2 := by
        have hl := hl13 p hp'
        have hsq_l : ∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2 ≤ ρ' * Cf := by
          have h0 : 0 ≤ ρ' * Cf := by positivity
          calc
            ∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2
                = (Real.sqrt (∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2)) ^ 2 :=
                  (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
            _ ≤ (Real.sqrt (ρ' * Cf)) ^ 2 :=
                  pow_le_pow_left₀ (Real.sqrt_nonneg _) hl 2
            _ = ρ' * Cf := Real.sq_sqrt h0
        have hid_p : ∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2 =
            (n : ℝ) ^ 2 * ∑ i : Fin n, (p i - 1 / (n : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have : (n : ℝ) * (p i - 1 / (n : ℝ)) = (n : ℝ) * p i - 1 := by
            rw [mul_sub, mul_one_div_cancel (ne_of_gt hn_pos)]
          rw [← this, mul_pow]
        rw [le_div_iff₀ (sq_pos_of_pos hn_pos), mul_comm]
        linarith
      have hℓ_l2 : ∑ i : Fin n, (ℓ xs (z i) - ℓ x (z i)) ^ 2 ≤
          (n : ℝ) * K_M * ‖x - xs‖ ^ 2 := by
        calc
          ∑ i : Fin n, (ℓ xs (z i) - ℓ x (z i)) ^ 2
              ≤ ∑ i : Fin n, (M (z i) * ‖x - xs‖) ^ 2 := by
                refine Finset.sum_le_sum fun i _ => ?_
                have hlip := hB.2.2.2 (z i) xs hxs_mem x hx
                rw [norm_sub_rev] at hlip
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) hlip 2
          _ = ((n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2)) * ‖x - xs‖ ^ 2 := by
                simp_rw [mul_pow, ← Finset.sum_mul]
                rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hn_pos), one_mul]
          _ ≤ ((n : ℝ) * K_M) * ‖x - xs‖ ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
                exact mul_le_mul_of_nonneg_left hz1.le hn_pos.le
          _ = (n : ℝ) * K_M * ‖x - xs‖ ^ 2 := by ring
      calc
        (∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i))) ^ 2
            ≤ (∑ i : Fin n, (p i - 1 / (n : ℝ)) ^ 2) *
                (∑ i : Fin n, (ℓ xs (z i) - ℓ x (z i)) ^ 2) := hcs
        _ ≤ ((ρ' * Cf) / (n : ℝ) ^ 2) * ((n : ℝ) * K_M * ‖x - xs‖ ^ 2) :=
            mul_le_mul hp_l2 hℓ_l2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = ((Real.sqrt (ρ' * Cf) * Real.sqrt K_M * ‖x - xs‖) / Real.sqrt (n : ℝ)) ^ 2 := by
            rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
              Real.sq_sqrt hKM_pos.le, Real.sq_sqrt hn_pos.le]
            field_simp [ne_of_gt hn_pos]
    have hshift_le :
        ∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i)) ≤
          (Real.sqrt (ρ' * Cf) * Real.sqrt K_M * ‖x - xs‖) / Real.sqrt (n : ℝ) := by
      have hbound_nonneg :
          0 ≤ (Real.sqrt (ρ' * Cf) * Real.sqrt K_M * ‖x - xs‖) / Real.sqrt (n : ℝ) := by
        positivity
      nlinarith [sq_abs (∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i))),
        le_abs_self (∑ i : Fin n, (p i - 1 / (n : ℝ)) * (ℓ xs (z i) - ℓ x (z i)))]
    have hemp_neg_le :
        -(1 / Real.sqrt (n : ℝ)) * empProc ℓ P₀ xs z x ≤
          (1 / Real.sqrt (n : ℝ)) * |empProc ℓ P₀ xs z x| := by
      have := neg_le_abs (empProc ℓ P₀ xs z x)
      nlinarith [one_div_nonneg.mpr hsqrtn_pos.le]
    linarith
  -- Localization: `xhat ∈ Metric.ball xs δ`
  have hxhat_ball : xhat ∈ Metric.ball xs δ := by
    by_contra hxhat_out
    have hxhat_K : xhat ∈ X \ Metric.ball xs δ := ⟨hxhat_X, hxhat_out⟩
    have hF_gap : F xs - F xhat ≤ -γ := by linarith [hγ_sep xhat hxhat_K]
    have hxhat_BR : xhat ∈ X ∩ Metric.closedBall xs R := ⟨hxhat_X, hX_sub_R hxhat_X⟩
    have hnorm_R : ‖xhat - xs‖ ≤ R := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp hxhat_BR.2
    have hemp_R : |empProc ℓ P₀ xs z xhat| ≤ U_R := hUR_dom xhat hxhat_BR
    have hupper := hdecomp xhat hxhat_X
    have hlt_zero : ∑ i : Fin n, p i * (ℓ xs (z i) - ℓ xhat (z i)) < 0 := by
      have h1 : (1 / Real.sqrt (n : ℝ)) * |empProc ℓ P₀ xs z xhat| +
          (Real.sqrt (ρ' * Cf) * Real.sqrt K_M * ‖xhat - xs‖) / Real.sqrt (n : ℝ) ≤
          (L_R + Real.sqrt (ρ' * Cf) * Real.sqrt K_M * R) / Real.sqrt (n : ℝ) := by
        rw [one_div_mul_eq_div, ← add_div]
        refine div_le_div_of_nonneg_right ?_ hsqrtn_pos.le
        exact add_le_add (hemp_R.trans hz2.le)
          (mul_le_mul_of_nonneg_left hnorm_R (by positivity))
      linarith
    have hge_zero : 0 ≤ ∑ i : Fin n, p i * (ℓ xs (z i) - ℓ xhat (z i)) := by
      rw [← habs_rem]; exact abs_nonneg _
    linarith
  -- Local bound on `X ∩ closedBall xs δ`
  have hxhat_Bδ : xhat ∈ X ∩ Metric.closedBall xs δ :=
    ⟨hxhat_X, Metric.ball_subset_closedBall hxhat_ball⟩
  have hnorm_δ : ‖xhat - xs‖ ≤ δ := by
    simpa [dist_eq_norm] using Metric.mem_closedBall.mp hxhat_Bδ.2
  have hemp_δ : |empProc ℓ P₀ xs z xhat| ≤ U_δ := hUδ_dom xhat hxhat_Bδ
  have hF_nonpos : F xs - F xhat ≤ 0 := by linarith [hxs_min xhat hxhat_X]
  rw [habs_rem]
  calc
    ∑ i : Fin n, p i * (ℓ xs (z i) - ℓ xhat (z i))
        ≤ (F xs - F xhat) + (1 / Real.sqrt (n : ℝ)) * |empProc ℓ P₀ xs z xhat| +
            (Real.sqrt (ρ' * Cf) * Real.sqrt K_M * ‖xhat - xs‖) / Real.sqrt (n : ℝ) :=
          hdecomp xhat hxhat_X
    _ ≤ 0 + (ε / 4) / Real.sqrt (n : ℝ) + (ε / 4) / Real.sqrt (n : ℝ) := by
          refine add_le_add (add_le_add hF_nonpos ?_) ?_
          · rw [one_div_mul_eq_div]
            exact div_le_div_of_nonneg_right (hemp_δ.trans hz3.le) hsqrtn_pos.le
          · refine div_le_div_of_nonneg_right ?_ hsqrtn_pos.le
            exact (mul_le_mul_of_nonneg_left hnorm_δ (by positivity)).trans hδ_shift
    _ = ε / (2 * Real.sqrt (n : ℝ)) := by ring

end GenEmpLikCoverageLemma16Aux

open MeasureTheory ProbabilityTheory Filter Topology GenEmpLik.Coverage
open GenEmpLikCoverageLemma16Aux in
theorem solution
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (d : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (M : Ξ → ℝ) (f : ℝ → EReal) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hA : AssumptionA f)
    (hX : X.Nonempty) (hB : AssumptionB X ℓ M)
    (hℓmeas : ∀ x, Measurable (ℓ x))
    (hM2 : Integrable (fun z => M z ^ 2) (μ.map (ξ 0)))
    (hℓ2 : ∃ x0 ∈ X, Integrable (fun z => ℓ x0 z ^ 2) (μ.map (ξ 0)))
    (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (hunique : HasUniqueOptimizer X ℓ (μ.map (ξ 0)))
    (hvar : 0 < variance (ℓ (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique))
      (μ.map (ξ 0))) :
    ∀ ε : ℝ, 0 < ε →
      Filter.limsup (fun n : ℕ => μ {ω |
        ε / Real.sqrt (n : ℝ) ≤
          sSup ((fun p => |remainder X ℓ (μ.map (ξ 0))
            (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
            (fun i : Fin n => ξ i ω) p|) '' divergenceBall f ρ n)})
        atTop = 0 := by
  have _ := hvar
  set P₀ : Measure Ξ := μ.map (ξ 0)
  have : IsProbabilityMeasure P₀ := Measure.isProbabilityMeasure_map (hξmeas 0).aemeasurable
  set xs : EuclideanSpace ℝ (Fin d) := uniqueOptimizer X ℓ P₀ hunique
  have hxs_spec : xs ∈ X ∧ ∀ y ∈ X, (∫ z, ℓ xs z ∂P₀) ≤ (∫ z, ℓ y z ∂P₀) :=
    Classical.choose_spec hunique.exists
  have hxs_mem : xs ∈ X := hxs_spec.1
  have hxs_min : ∀ y ∈ X, (∫ z, ℓ xs z ∂P₀) ≤ (∫ z, ℓ y z ∂P₀) := hxs_spec.2
  -- Integrability of `M` and `ℓ x` for all `x ∈ X`
  have hM_int : Integrable M P₀ :=
    integrable_of_nonneg_le hB.2.1 hB.2.2.1
      (fun z₀ => (le_abs_self (M z₀)).trans (abs_le_sq_add_one (M z₀)))
      (hM2.add (integrable_const 1))
  have hEM_nonneg : 0 ≤ ∫ z₀, M z₀ ∂P₀ := integral_nonneg hB.2.2.1
  obtain ⟨x0, hx0_mem, hℓx0_sq⟩ := hℓ2
  have hℓx0_int : Integrable (ℓ x0) P₀ :=
    (hℓx0_sq.add (integrable_const 1)).mono' (hℓmeas x0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z₀ => by
        rw [Real.norm_eq_abs]; exact abs_le_sq_add_one (ℓ x0 z₀))
  have hℓ_int : ∀ x ∈ X, Integrable (ℓ x) P₀ := by
    intro x hx
    have hdiff_int : Integrable (fun z₀ => ℓ x z₀ - ℓ x0 z₀) P₀ :=
      (hM_int.mul_const ‖x - x0‖).mono' ((hℓmeas x).sub (hℓmeas x0)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z₀ => by
          rw [Real.norm_eq_abs]; exact hB.2.2.2 z₀ x hx x0 hx0_mem)
    exact (hdiff_int.add hℓx0_int).congr (Filter.Eventually.of_forall fun z₀ => by simp)
  -- Population objective `F` and optimal value `F xs`
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∫ z₀, ℓ x z₀ ∂P₀
  have hF_lip : ∀ x ∈ X, ∀ y ∈ X, |F x - F y| ≤ (∫ z₀, M z₀ ∂P₀) * ‖x - y‖ := by
    intro x hx y hy
    dsimp [F]
    rw [← integral_sub (hℓ_int x hx) (hℓ_int y hy)]
    calc
      |∫ z₀, (ℓ x z₀ - ℓ y z₀) ∂P₀|
          ≤ ∫ z₀, |ℓ x z₀ - ℓ y z₀| ∂P₀ := abs_integral_le_integral_abs _
      _ ≤ ∫ z₀, (M z₀ * ‖x - y‖) ∂P₀ :=
          integral_mono ((hℓ_int x hx).sub (hℓ_int y hy)).abs (hM_int.mul_const _)
            (fun z₀ => hB.2.2.2 z₀ x hx y hy)
      _ = (∫ z₀, M z₀ ∂P₀) * ‖x - y‖ := integral_mul_const _ _
  have hF_cont : ContinuousOn F X := by
    rw [Metric.continuousOn_iff]
    intro x hx ε' hε'
    refine ⟨ε' / ((∫ z₀, M z₀ ∂P₀) + 1), div_pos hε' (by linarith), ?_⟩
    intro y hy hdist
    rw [Real.dist_eq]
    rw [dist_eq_norm] at hdist
    calc
      |F y - F x| ≤ (∫ z₀, M z₀ ∂P₀) * ‖y - x‖ := hF_lip y hy x hx
      _ ≤ ((∫ z₀, M z₀ ∂P₀) + 1) * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
      _ < ((∫ z₀, M z₀ ∂P₀) + 1) * (ε' / ((∫ z₀, M z₀ ∂P₀) + 1)) :=
          mul_lt_mul_of_pos_left hdist (by linarith)
      _ = ε' := mul_div_cancel₀ ε' (ne_of_gt (by linarith))
  have hopt_eq : optimalValue X ℓ P₀ = F xs := by
    dsimp [optimalValue]
    exact IsLeast.csInf_eq ⟨⟨xs, hxs_mem, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hxs_min y hy⟩
  have hxs_strict : ∀ y ∈ X, y ≠ xs → F xs < F y := by
    intro y hy hne
    rcases (hxs_min y hy).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hne
      have hy_opt : y ∈ X ∧ ∀ w ∈ X, F y ≤ F w :=
        ⟨hy, fun w hw => heq.symm.trans_le (hxs_min w hw)⟩
      exact hunique.unique hy_opt hxs_spec
  -- Global radius `R > 0` enclosing `X` around `xs`, and `lemma_13` constant for `ρ' = max ρ 1`
  obtain ⟨R₀, hR₀⟩ := hB.1.isBounded.subset_closedBall xs
  set R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
  have hX_sub_R : X ⊆ Metric.closedBall xs R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left R₀ 1))
  set ρ' : ℝ := max ρ 1
  have hρ'_pos : 0 < ρ' := lt_of_lt_of_le one_pos (le_max_right ρ 1)
  obtain ⟨cf, Cf, hcf_pos, hcf_le, hl13, _⟩ := GenEmpLik.Coverage.lemma_13 f hA ρ' hρ'_pos
  have hCf_pos : 0 < Cf := hcf_pos.trans_le hcf_le
  have hEM2_nonneg : 0 ≤ ∫ z₀, M z₀ ^ 2 ∂P₀ := integral_nonneg (fun z₀ => sq_nonneg _)
  set C_emp : ℝ := (16 * (2 + (d : ℝ) * ((d : ℝ) + 4)) + 2) * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1)
  have hC_emp_pos : 0 < C_emp := by
    dsimp [C_emp]
    have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  intro ε hε
  refine limsup_ennreal_eq_zero_of_forall_pos fun η hη => ?_
  set K_M : ℝ := 3 * ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1) / η + 1
  have hKM_pos : 0 < K_M := by dsimp [K_M]; positivity
  set δ : ℝ :=
    min ((ε / 4) / (Real.sqrt (ρ' * Cf) * Real.sqrt K_M + 1))
        ((η / 3) * ε / (4 * C_emp))
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hδ_shift : Real.sqrt (ρ' * Cf) * Real.sqrt K_M * δ ≤ ε / 4 := by
    have h1 : δ ≤ (ε / 4) / (Real.sqrt (ρ' * Cf) * Real.sqrt K_M + 1) := min_le_left _ _
    have hden : 0 < Real.sqrt (ρ' * Cf) * Real.sqrt K_M + 1 := by positivity
    calc
      Real.sqrt (ρ' * Cf) * Real.sqrt K_M * δ
          ≤ (Real.sqrt (ρ' * Cf) * Real.sqrt K_M + 1) * δ := by nlinarith [hδ_pos]
      _ ≤ (Real.sqrt (ρ' * Cf) * Real.sqrt K_M + 1) *
            ((ε / 4) / (Real.sqrt (ρ' * Cf) * Real.sqrt K_M + 1)) :=
          mul_le_mul_of_nonneg_left h1 hden.le
      _ = ε / 4 := mul_div_cancel₀ _ (ne_of_gt hden)
  have hδ_markov : C_emp * δ / (ε / 4) ≤ η / 3 := by
    have h1 : δ ≤ (η / 3) * ε / (4 * C_emp) := min_le_right _ _
    calc
      C_emp * δ / (ε / 4) = (4 * C_emp * δ) / ε := by ring
      _ ≤ (4 * C_emp * ((η / 3) * ε / (4 * C_emp))) / ε := by
          refine div_le_div_of_nonneg_right ?_ hε.le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = η / 3 := by field_simp [ne_of_gt hC_emp_pos, ne_of_gt hε]
  -- Separation gap `γ > 0` on `K_out := X \ Metric.ball xs δ`
  set K_out : Set (EuclideanSpace ℝ (Fin d)) := X \ Metric.ball xs δ
  have hgap : ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ K_out, γ ≤ F x - F xs := by
    by_cases hKne : K_out.Nonempty
    · have hKcomp : IsCompact K_out := hB.1.diff Metric.isOpen_ball
      have hsub_cont : ContinuousOn (fun x => F x - F xs) K_out :=
        (hF_cont.mono Set.sdiff_subset).sub continuousOn_const
      obtain ⟨_, hxmin_least⟩ :=
        (hKcomp.image_of_continuousOn hsub_cont).exists_isLeast (hKne.image _)
      obtain ⟨⟨xmin, hxmin_mem, rfl⟩, hxmin_min⟩ := hxmin_least
      have hxmin_ne : xmin ≠ xs := by
        intro heq
        subst heq
        exact hxmin_mem.2 (Metric.mem_ball_self hδ_pos)
      refine ⟨F xmin - F xs, sub_pos.mpr (hxs_strict xmin hxmin_mem.1 hxmin_ne), ?_⟩
      intro x hx
      exact hxmin_min ⟨x, hx, rfl⟩
    · refine ⟨1, one_pos, fun x hx => False.elim (hKne ⟨x, hx⟩)⟩
  obtain ⟨γ, hγ_pos, hγ_sep⟩ := hgap
  set L_R : ℝ := 3 * C_emp * R / η + 1
  have hLR_pos : 0 < L_R := by dsimp [L_R]; positivity
  set N₀ : ℕ :=
    Nat.ceil (((L_R + Real.sqrt (ρ' * Cf) * Real.sqrt K_M * R) / γ) ^ 2) + 1
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hnN₀ => ?_⟩
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos _) hnN₀
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
  have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hn_large : (L_R + Real.sqrt (ρ' * Cf) * Real.sqrt K_M * R) / Real.sqrt (n : ℝ) < γ := by
    set num := L_R + Real.sqrt (ρ' * Cf) * Real.sqrt K_M * R
    have hnum_pos : 0 < num := by dsimp [num]; positivity
    have hceil : (num / γ) ^ 2 < (n : ℝ) := by
      have h1 : (num / γ) ^ 2 ≤ (Nat.ceil ((num / γ) ^ 2) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil ((num / γ) ^ 2) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnN₀
      linarith
    have hlt_sqrt : num / γ < Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_sq (div_pos hnum_pos hγ_pos).le]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hceil
    rw [div_lt_iff₀ hsqrtn_pos]
    have := (div_lt_iff₀ hγ_pos).mp hlt_sqrt
    linarith
  -- Sample pushforward `μ.map sampleMap = ν`
  set ν : Measure (Fin n → Ξ) := Measure.pi (fun _ : Fin n => P₀)
  set sampleMap : Ω → (Fin n → Ξ) := fun ω i => ξ i ω
  have hsample_meas : Measurable sampleMap := measurable_pi_lambda _ fun i => hξmeas i
  have hsample_law : μ.map sampleMap = ν := by
    have hind : iIndepFun (fun (i : Fin n) ω => ξ i ω) μ :=
      hξindep.precomp Fin.val_injective
    have hmap := iIndepFun.map_fun_eq_pi_map
      (fun i : Fin n => (hξmeas i).aemeasurable) hind
    have hident_eq : (fun i : Fin n => μ.map (ξ i)) = fun _ : Fin n => P₀ := by
      funext i; exact (hξident i).map_eq
    simpa [sampleMap, ν, hident_eq] using hmap
  -- Construct envelopes `U_R` (for radius `R`) and `U_δ` (for radius `δ`)
  obtain ⟨U_R, hUR_meas, hUR_nonneg, hUR_int, hUR_dom, hUR_exp⟩ :=
    exists_empProc_envelope n P₀ hn_pos_nat hB hℓmeas hM2 hℓ_int hxs_mem hR_pos
  obtain ⟨U_δ, hUδ_meas, hUδ_nonneg, hUδ_int, hUδ_dom, hUδ_exp⟩ :=
    exists_empProc_envelope n P₀ hn_pos_nat hB hℓmeas hM2 hℓ_int hxs_mem hδ_pos
  -- Three bad events on `Fin n → Ξ`
  set avgM2 : (Fin n → Ξ) → ℝ := fun z => (1 / (n : ℝ)) * ∑ i : Fin n, M (z i) ^ 2
  have havgM2_meas : Measurable avgM2 :=
    Measurable.const_mul
      (Finset.measurable_sum _ fun i _ => (hB.2.1.pow_const 2).comp (measurable_pi_apply i)) _
  have hM2_coord_int : ∀ i : Fin n, Integrable (fun z : Fin n → Ξ => M (z i) ^ 2) ν := fun i =>
    integrable_comp_mp (MeasureTheory.measurePreserving_eval (fun _ => P₀) i)
      (hB.2.1.pow_const 2) hM2
  have havgM2_int : Integrable avgM2 ν :=
    Integrable.const_mul (integrable_finsetSum _ fun i _ => hM2_coord_int i) _
  have havgM2_exp : ∫ z, avgM2 z ∂ν = ∫ z₀, M z₀ ^ 2 ∂P₀ := by
    dsimp [avgM2]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hM2_coord_int i)]
    have hcoord : ∀ i : Fin n, ∫ z, M (z i) ^ 2 ∂ν = ∫ z₀, M z₀ ^ 2 ∂P₀ := by
      intro i
      have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin n => P₀) i
      rw [← hmp.map_eq, integral_map hmp.aemeasurable (hB.2.1.pow_const 2).aestronglyMeasurable]
    simp_rw [hcoord, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_div,
      inv_mul_cancel_left₀ (ne_of_gt hn_pos)]
  set E₁ : Set (Fin n → Ξ) := {z | K_M ≤ avgM2 z}
  set E₂ : Set (Fin n → Ξ) := {z | L_R ≤ U_R z}
  set E₃ : Set (Fin n → Ξ) := {z | ε / 4 ≤ U_δ z}
  have hE₁_meas : MeasurableSet E₁ := measurableSet_Ici.preimage havgM2_meas
  have hE₂_meas : MeasurableSet E₂ := measurableSet_Ici.preimage hUR_meas
  have hE₃_meas : MeasurableSet E₃ := measurableSet_Ici.preimage hUδ_meas
  have hνE₁ : ν E₁ ≤ ENNReal.ofReal (η / 3) := by
    refine (markov_measure_ge_le ν
      (fun z => by dsimp [avgM2]; positivity) havgM2_int hKM_pos).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [havgM2_exp, div_le_iff₀ hKM_pos]
    have h1 : K_M * (η / 3) = ((∫ z₀, M z₀ ^ 2 ∂P₀) + 1) + η / 3 := by
      dsimp [K_M]; field_simp [ne_of_gt hη]
    linarith
  have hνE₂ : ν E₂ ≤ ENNReal.ofReal (η / 3) := by
    refine (markov_measure_ge_le ν hUR_nonneg hUR_int hLR_pos).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (∫ z, U_R z ∂ν) / L_R ≤ (C_emp * R) / L_R :=
      div_le_div_of_nonneg_right hUR_exp hLR_pos.le
    refine h1.trans ?_
    rw [div_le_iff₀ hLR_pos]
    have h2 : L_R * (η / 3) = C_emp * R + η / 3 := by
      dsimp [L_R]; field_simp [ne_of_gt hη]
    linarith
  have hνE₃ : ν E₃ ≤ ENNReal.ofReal (η / 3) := by
    refine (markov_measure_ge_le ν hUδ_nonneg hUδ_int (by positivity)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    exact (div_le_div_of_nonneg_right hUδ_exp (by positivity)).trans hδ_markov
  set Bad_n : Set Ω :=
    {ω | ε / Real.sqrt (n : ℝ) ≤
      sSup ((fun p => |remainder X ℓ P₀ xs (sampleMap ω) p|) '' divergenceBall f ρ n)}
  have hsub : Bad_n ⊆ sampleMap ⁻¹' E₁ ∪ sampleMap ⁻¹' E₂ ∪ sampleMap ⁻¹' E₃ := by
    intro ω hω
    by_contra hgood
    simp only [Set.mem_union, Set.mem_preimage, not_or] at hgood
    obtain ⟨⟨hnot1, hnot2⟩, hnot3⟩ := hgood
    have hrem_le :=
      remainder_le_on_good_event P₀ hn_pos_nat (le_max_left ρ 1) hρ'_pos hCf_pos hKM_pos
        hX hB hxs_mem hxs_min hopt_eq hX_sub_R (hl13 n hn_pos_nat) hγ_sep hn_large hδ_shift
        (lt_of_not_ge hnot1) (hUR_dom (sampleMap ω)) (lt_of_not_ge hnot2)
        (hUδ_dom (sampleMap ω)) (lt_of_not_ge hnot3)
    have hball_ne : (divergenceBall f ρ n).Nonempty :=
      divergenceBall_nonempty f hA hρ hn_pos_nat
    have hsup_le :
        sSup ((fun p => |remainder X ℓ P₀ xs (sampleMap ω) p|) '' divergenceBall f ρ n) ≤
          ε / (2 * Real.sqrt (n : ℝ)) := by
      refine csSup_le (hball_ne.image _) ?_
      rintro _ ⟨p, hp, rfl⟩
      exact hrem_le p hp
    have hω_ge :
        ε / Real.sqrt (n : ℝ) ≤
          sSup ((fun p => |remainder X ℓ P₀ xs (sampleMap ω) p|) '' divergenceBall f ρ n) := hω
    have hhalf_lt : ε / (2 * Real.sqrt (n : ℝ)) < ε / Real.sqrt (n : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hsqrtn_pos]
      nlinarith
    linarith
  have hμ1 : μ (sampleMap ⁻¹' E₁) ≤ ENNReal.ofReal (η / 3) := by
    rw [← Measure.map_apply hsample_meas hE₁_meas, hsample_law]
    exact hνE₁
  have hμ2 : μ (sampleMap ⁻¹' E₂) ≤ ENNReal.ofReal (η / 3) := by
    rw [← Measure.map_apply hsample_meas hE₂_meas, hsample_law]
    exact hνE₂
  have hμ3 : μ (sampleMap ⁻¹' E₃) ≤ ENNReal.ofReal (η / 3) := by
    rw [← Measure.map_apply hsample_meas hE₃_meas, hsample_law]
    exact hνE₃
  calc
    μ Bad_n ≤ μ (sampleMap ⁻¹' E₁ ∪ sampleMap ⁻¹' E₂ ∪ sampleMap ⁻¹' E₃) :=
      measure_mono hsub
    _ ≤ μ (sampleMap ⁻¹' E₁ ∪ sampleMap ⁻¹' E₂) + μ (sampleMap ⁻¹' E₃) :=
      measure_union_le _ _
    _ ≤ μ (sampleMap ⁻¹' E₁) + μ (sampleMap ⁻¹' E₂) + μ (sampleMap ⁻¹' E₃) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) :=
      add_le_add (add_le_add hμ1 hμ2) hμ3
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
