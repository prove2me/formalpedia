-- Prove2me | solution 1 for DetDLP.weighted_mode_branching_bound
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:15:54.878211+00:00
-- url     : https://prove2.me/submissions/a1b18600-434c-4ba0-bb3d-6c62267f6099

import Mathlib

namespace DetDLP.WeightedModeCount
open Finset Real Filter Topology

private theorem reciprocal_squares (N : ℕ) :
    (∑ k ∈ range N, 1/((k:ℝ)+1)^2) ≤ 2 := by
  have h (n : ℕ) : (∑ k ∈ range (n+1), 1/((k:ℝ)+1)^2) ≤ 2-1/((n:ℝ)+1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ]
      have hdelta : 1/((n:ℝ)+2)^2 ≤ 1/((n:ℝ)+1)-1/((n:ℝ)+2) := by
        field_simp
        nlinarith [show (0:ℝ) ≤ n by positivity]
      push_cast; rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring]; linarith
  cases N with
  | zero => simp
  | succ n => exact (h n).trans (sub_le_self _ (by positivity))

/-- A bound on one column of the double series from the generating product. The
effective weight is w(i)+1, so only strictly positive weights occur. -/
private theorem exponential_weights {ι : Type*} [Fintype ι] (w : ι → ℕ) (B : ℕ)
    (hm : ∀ j, (univ.filter fun i => w i=j).card ≤ B) {x : ℝ} (hx : 0 < x) :
    (∑ i, exp (-x*((w i:ℝ)+1))) ≤ B/x := by
  classical
  let q := exp (-x)
  have hq : 0 < q := exp_pos _
  have hq1 : q < 1 := by dsimp [q]; simpa using hx
  let N := univ.sup w+1
  have hmaps : ∀ i ∈ (univ : Finset ι), w i ∈ range N := by
    intro i hi; exact mem_range.mpr (Nat.lt_succ_of_le (le_sup hi))
  have hb (j : ℕ) : (∑ i ∈ univ.filter (fun i => w i=j), q^(w i+1)) ≤ (B:ℝ)*q^(j+1) := by
    calc
      _ = ∑ _ ∈ univ.filter (fun i => w i=j), q^(j+1) :=
        sum_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2])
      _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast hm j
  have he (j : ℕ) : exp (-x*((j:ℝ)+1)) = q^(j+1) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  simp_rw [he]
  calc
    _ = ∑ j ∈ range N, ∑ i ∈ univ.filter (fun i => w i=j), q^(w i+1) :=
      (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ range N,(B:ℝ)*q^(j+1) := sum_le_sum fun j _ => hb j
    _ = ((B:ℝ)*q)*∑ j ∈ range N, q^j := by simp_rw [pow_succ]; rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ ((B:ℝ)*q)*(1-q)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_hasSum _ (fun i _ => (pow_nonneg hq.le i)) (hasSum_geometric_of_lt_one hq.le hq1)
    _ ≤ _ := by
      have hh := add_one_le_exp x
      have hpos : 0 < 1-q := by linarith
      have hh' : q*(x+1) ≤ 1 := by
        change exp (-x)*(x+1) ≤ 1
        rw [exp_neg,inv_mul_eq_div]; exact (div_le_one (exp_pos _)).mpr hh
      have hh'' : q*(1-q)⁻¹ ≤ 1/x := by
        rw [← div_eq_mul_inv,div_le_div_iff₀ hpos hx]; nlinarith only [hh']
      simpa only [mul_assoc,mul_one_div] using mul_le_mul_of_nonneg_left hh'' (Nat.cast_nonneg B)

private theorem log_partition {ι : Type*} [Fintype ι] (w : ι → ℕ) (B : ℕ)
    (hm : ∀ j, (univ.filter fun i => w i=j).card ≤ B) {θ : ℝ} (hθ : 0 < θ) :
    (∑ i, -log (1-exp (-θ*((w i:ℝ)+1)))) ≤ 2*B/θ := by
  classical
  let a (i : ι) := exp (-θ*((w i:ℝ)+1))
  have h1 (i : ι) : |a i| < 1 := by
    rw [abs_of_pos (exp_pos _),exp_lt_one_iff]; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hθ) (by positivity)
  have conv : Tendsto (fun N : ℕ => ∑ i, ∑ n ∈ range N,(a i)^(n+1)/((n:ℝ)+1)) atTop
      (𝓝 (∑ i,-log (1-a i))) :=
    tendsto_finsetSum _ (fun i _ => (hasSum_pow_div_log_of_abs_lt_one (h1 i)).tendsto_sum_nat)
  apply le_of_tendsto conv (Filter.Eventually.of_forall (fun N => ?_))
  rw [sum_comm]
  have hn (n : ℕ) : (∑ i, (a i)^(n+1)/((n:ℝ)+1)) ≤ ((B:ℝ)/θ)*(1/((n:ℝ)+1)^2) := by
    have hN : (0:ℝ) < (n:ℝ)+1 := by positivity
    have he (i : ι) : (a i)^(n+1) = exp (-(θ*((n:ℝ)+1))*((w i:ℝ)+1)) := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    simp_rw [he]; rw [← sum_div]
    have h := exponential_weights w B hm (mul_pos hθ hN)
    calc
      _ ≤ ((B:ℝ)/(θ*((n:ℝ)+1)))/((n:ℝ)+1) := div_le_div_of_nonneg_right h hN.le
      _ = _ := by field_simp
  calc
    _ ≤ ∑ n ∈ range N, ((B:ℝ)/θ)*(1/((n:ℝ)+1)^2) := sum_le_sum (fun n _ => hn n)
    _ = ((B:ℝ)/θ)*∑ n ∈ range N, 1/((n:ℝ)+1)^2 := (mul_sum ..).symm
    _ ≤ ((B:ℝ)/θ)*2 := mul_le_mul_of_nonneg_left (reciprocal_squares N) (by positivity)
    _ = _ := by ring

/-- The modes are the exponent vectors whose strictly positive weighted cost fits the precision. -/
noncomputable def tuples {ι : Type*} [Fintype ι] (w : ι → ℕ) (p : ℕ) : Finset (ι → Fin p) := by
  classical
  exact univ.filter fun β => (∑ i, (w i+1)*(β i).val) < p

private theorem finite_generator {ι : Type*} [Fintype ι] (w : ι → ℕ) (p : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ((tuples w p).card:ℝ) ≤ exp (θ*p) * exp (∑ i, -log (1-exp (-θ*((w i:ℝ)+1)))) := by
  classical
  let a (i : ι) := exp (-θ*((w i:ℝ)+1))
  have ha (i : ι) : 0 < a i := exp_pos _
  have h1 (i : ι) : a i < 1 := by
    apply exp_lt_one_iff.mpr; exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hθ) (by positivity)
  let mass (β : ι → Fin p) := ∏ i, (a i)^(β i).val
  have hmass (β : ι → Fin p) (hb : β ∈ tuples w p) : 1 ≤ exp (θ*p)*mass β := by
    have hbudget : (∑ i,(w i+1)*(β i).val) ≤ p := (mem_filter.mp hb).2.le
    have hh : (∑ i,((w i:ℝ)+1)*(β i).val) ≤ (p:ℝ) := by exact_mod_cast hbudget
    have he (i : ι) : (a i)^(β i).val = exp (-θ*(((w i:ℝ)+1)*(β i).val)) := by
      rw [← exp_nat_mul]; congr 1; ring
    dsimp only [mass]; simp_rw [he]; rw [← exp_sum,← mul_sum,← exp_add]
    exact one_le_exp_iff.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hh hθ.le])
  have hprod (i : ι) : (∑ b : Fin p,(a i)^b.val) ≤ (1-a i)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range]
    exact sum_le_hasSum _ (fun j _ => pow_nonneg (ha i).le j) (hasSum_geometric_of_lt_one (ha i).le (h1 i))
  have he : (∏ i,(1-a i)⁻¹) = exp (∑ i, -log (1-a i)) := by
    rw [exp_sum]; apply prod_congr rfl; intro i _
    rw [exp_neg,exp_log (sub_pos.mpr (h1 i))]
  calc
    _ = ∑ _ ∈ tuples w p,(1:ℝ) := by simp
    _ ≤ ∑ β ∈ tuples w p,exp (θ*p)*mass β := sum_le_sum hmass
    _ ≤ ∑ β : ι → Fin p, exp (θ*p)*mass β := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun β _ _ =>
      mul_nonneg (exp_pos _).le (prod_nonneg (fun i _ => pow_nonneg (ha i).le _)))
    _ = exp (θ*p)*∏ i,∑ b : Fin p,(a i)^b.val := by rw [← mul_sum,Fintype.prod_sum]
    _ ≤ exp (θ*p)*∏ i,(1-a i)⁻¹ := mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => sum_nonneg fun b _ => pow_nonneg (ha i).le _) (fun i _ => hprod i)) (exp_pos _).le
    _ = _ := by rw [he]

theorem count {ι : Type*} [Fintype ι] (w : ι → ℕ) (B p : ℕ)
    (hm : ∀ j, (univ.filter fun i => w i=j).card ≤ B)
    (hB : 0 < B) (hp : 0 < p) :
    ((tuples w p).card:ℝ) ≤ exp (3*sqrt ((B:ℝ)*p)) := by
  let θ := sqrt ((B:ℝ)*p)/(p:ℝ)
  have hbr : (0:ℝ) < B := by exact_mod_cast hB
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have ht : θ*p = sqrt ((B:ℝ)*p) := by dsimp [θ]; field_simp
  have hh : (B:ℝ)/θ = sqrt ((B:ℝ)*p) := by
    apply (div_eq_iff hθ.ne').mpr
    dsimp [θ]; rw [← mul_div_assoc,← sq,Real.sq_sqrt (by positivity)]; field_simp
  have h := log_partition w B hm hθ
  apply (finite_generator w p hθ).trans
  rw [← exp_add]; apply exp_le_exp.mpr
  rw [ht,mul_div_assoc,hh] at *
  linarith
end DetDLP.WeightedModeCount

open DetDLP

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (B p : ℕ)
    (hm : ∀ j, (Finset.univ.filter fun i => w i=j).card ≤ B)
    (hB : 0 < B) (hp : 0 < p) (M D u C : ℝ) (hM : 0 ≤ M) (hD : 0 < D)
    (hu : 0 < u) (hC : 0 ≤ C) (hBD : (B:ℝ) ≤ 6*M/D) (hP : (p:ℝ) ≤ C*M*D/u) :
    let N := (Finset.univ.filter fun β : ι → Fin p => (∑ i, (w i+1)*(β i).val) < p).card
    (N:ℝ) ≤ Real.exp (3*Real.sqrt ((B:ℝ)*p)) ∧
      (N:ℝ) ≤ Real.exp (3*Real.sqrt (6*C)*M/Real.sqrt u) := by
  intro N
  have hcount := WeightedModeCount.count w B p hm hB hp
  have heq : N = (WeightedModeCount.tuples w p).card := by
    apply congrArg Finset.card
    ext β
    simp [WeightedModeCount.tuples]
  rw [← heq] at hcount
  refine ⟨hcount,hcount.trans (Real.exp_le_exp.mpr ?_)⟩
  have hbp : (B:ℝ)*p ≤ (6*C)*M^2/u := by
    calc
      _ ≤ (6*M/D)*(C*M*D/u) := mul_le_mul hBD hP (by positivity) (by positivity)
      _ = _ := by field_simp <;> ring
  have hs := Real.sqrt_le_sqrt hbp
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (show 0 ≤ 6*C by positivity),Real.sqrt_sq hM] at hs
  calc
    _ ≤ 3*(Real.sqrt (6*C)*M/Real.sqrt u) := by linarith
    _ = _ := by ring
