-- Prove2me | solution 1 for FoundationsML.MaxEnt.maxent_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:56:52.332046+00:00
-- url     : https://prove2.me/submissions/1cca4f19-915c-46b6-9989-41f696b3948a

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_MaxEntPrimalObjective
import Definitions.Def_FoundationsML_MaxEnt_MaxEntDualObjective
import Definitions.Def_FoundationsML_MaxEnt_RelativeEntropy
import Definitions.Def_FoundationsML_MaxEnt_GibbsDistribution

namespace FoundationsML.MaxEnt

open Filter Topology

lemma aux_me_Zpos {X : Type*} [Fintype X] [Nonempty X] {N : ℕ} (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) :
    0 < PartitionFunction p0 Φ w :=
  Finset.sum_pos (fun x _ => mul_pos (hp0 x) (Real.exp_pos _)) Finset.univ_nonempty

lemma aux_me_gibbs_pos {X : Type*} [Fintype X] [Nonempty X] {N : ℕ} (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) (x : X) :
    0 < GibbsDistribution p0 Φ w x :=
  div_pos (mul_pos (hp0 x) (Real.exp_pos _)) (aux_me_Zpos p0 hp0 Φ w)

lemma aux_me_gibbs_sum {X : Type*} [Fintype X] [Nonempty X] {N : ℕ} (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) :
    ∑ x, GibbsDistribution p0 Φ w x = 1 := by
  unfold GibbsDistribution
  rw [← Finset.sum_div]
  exact div_self (aux_me_Zpos p0 hp0 Φ w).ne'

lemma aux_me_logratio {X : Type*} [Fintype X] [Nonempty X] {N : ℕ} (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) (x : X) :
    Real.log (GibbsDistribution p0 Φ w x / p0 x) =
      ∑ j, w j * Φ x j - Real.log (PartitionFunction p0 Φ w) := by
  have hZ := aux_me_Zpos p0 hp0 Φ w
  have hp := (hp0 x).ne'
  have : GibbsDistribution p0 Φ w x / p0 x =
      Real.exp (∑ j, w j * Φ x j) / PartitionFunction p0 Φ w := by
    unfold GibbsDistribution
    field_simp
  rw [this, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]

lemma aux_me_Gform {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ} (hm : 0 < m) (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) (w : Fin N → ℝ) :
    MaxEntDualObjective p0 Φ S lam w =
      ∑ j, w j * EmpiricalFeatureMean Φ S j - Real.log (PartitionFunction p0 Φ w) -
        lam * ∑ j, |w j| := by
  unfold MaxEntDualObjective EmpiricalFeatureMean
  simp_rw [aux_me_logratio p0 hp0 Φ w]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : ∑ i, (∑ j, w j * Φ (S i) j - Real.log (PartitionFunction p0 Φ w)) =
      ∑ i, ∑ j, w j * Φ (S i) j - (m : ℝ) * Real.log (PartitionFunction p0 Φ w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ∑ j, w j * (1 / (m : ℝ) * ∑ i, Φ (S i) j) =
      1 / (m : ℝ) * ∑ i, ∑ j, w j * Φ (S i) j := by
    rw [Finset.sum_comm (f := fun i j => w j * Φ (S i) j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    ring
  rw [h1, h2]
  field_simp

lemma aux_me_identity {X : Type*} [Fintype X] [Nonempty X] {N : ℕ} (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) (p : X → ℝ)
    (hp : p ∈ Simplex X) :
    RelativeEntropy p p0 = RelativeEntropy p (GibbsDistribution p0 Φ w) +
      ∑ j, w j * (∑ x, p x * Φ x j) - Real.log (PartitionFunction p0 Φ w) := by
  unfold RelativeEntropy
  have hpt : ∀ x, p x * Real.log (p x / p0 x) =
      p x * Real.log (p x / GibbsDistribution p0 Φ w x) +
        p x * (∑ j, w j * Φ x j - Real.log (PartitionFunction p0 Φ w)) := by
    intro x
    by_cases h0 : p x = 0
    · simp [h0]
    have hpx : 0 < p x := lt_of_le_of_ne (hp.1 x) (Ne.symm h0)
    have hq := aux_me_gibbs_pos p0 hp0 Φ w x
    rw [← aux_me_logratio p0 hp0 Φ w x, ← mul_add]
    congr 1
    rw [← Real.log_mul (div_pos hpx hq).ne' (div_pos hq (hp0 x)).ne']
    congr 1
    field_simp
  simp_rw [hpt]
  rw [Finset.sum_add_distrib]
  have : ∑ x, p x * (∑ j, w j * Φ x j - Real.log (PartitionFunction p0 Φ w)) =
      ∑ j, w j * (∑ x, p x * Φ x j) - Real.log (PartitionFunction p0 Φ w) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this]
  ring

lemma aux_me_gibbs_ineq {X : Type*} [Fintype X] (p q : X → ℝ) (hp : p ∈ Simplex X)
    (hq : ∀ x, 0 < q x) (hqs : ∑ x, q x = 1) : 0 ≤ RelativeEntropy p q := by
  unfold RelativeEntropy
  have key : ∀ x, p x - q x ≤ p x * Real.log (p x / q x) := by
    intro x
    by_cases h0 : p x = 0
    · simp [h0]; exact (hq x).le
    have hpx : 0 < p x := lt_of_le_of_ne (hp.1 x) (Ne.symm h0)
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hq x) hpx)
    have h2 : Real.log (p x / q x) = - Real.log (q x / p x) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have h3 : p x * (q x / p x - 1) = q x - p x := by field_simp
    nlinarith
  have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => key x)
  rw [Finset.sum_sub_distrib, hp.2, hqs, sub_self] at this
  exact this

lemma aux_me_weak {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ} (hm : 0 < m) (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) (w : Fin N → ℝ)
    (p : X → ℝ) (hp : p ∈ Simplex X)
    (hC : (fun j => ∑ x, p x * Φ x j) ∈ FeatureConstraintSet Φ S lam) :
    RelativeEntropy p (GibbsDistribution p0 Φ w) + MaxEntDualObjective p0 Φ S lam w ≤
      RelativeEntropy p p0 := by
  rw [aux_me_identity p0 hp0 Φ w p hp, aux_me_Gform hm p0 hp0 Φ S lam w]
  have hj : ∀ j, w j * EmpiricalFeatureMean Φ S j - lam * |w j| ≤ w j * (∑ x, p x * Φ x j) := by
    intro j
    have h1 : |∑ x, p x * Φ x j - EmpiricalFeatureMean Φ S j| ≤ lam := hC j
    have h2 : |w j * (∑ x, p x * Φ x j - EmpiricalFeatureMean Φ S j)| ≤ |w j| * lam := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h3 := neg_abs_le (w j * (∑ x, p x * Φ x j - EmpiricalFeatureMean Φ S j))
    nlinarith
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  linarith

lemma aux_me_ub {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ} (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) (w : Fin N → ℝ) :
    MaxEntDualObjective p0 Φ S lam w ≤
      (1 / (m : ℝ)) * ∑ i, (- Real.log (p0 (S i))) - lam * ∑ j, |w j| := by
  unfold MaxEntDualObjective
  have : ∀ i, Real.log (GibbsDistribution p0 Φ w (S i) / p0 (S i)) ≤ - Real.log (p0 (S i)) := by
    intro i
    have hq := aux_me_gibbs_pos p0 hp0 Φ w (S i)
    have hq1 : GibbsDistribution p0 Φ w (S i) ≤ 1 := by
      rw [← aux_me_gibbs_sum p0 hp0 Φ w]
      exact Finset.single_le_sum (f := GibbsDistribution p0 Φ w)
        (fun x _ => (aux_me_gibbs_pos p0 hp0 Φ w x).le) (Finset.mem_univ _)
    rw [Real.log_div hq.ne' (hp0 (S i)).ne']
    have := Real.log_nonpos hq.le hq1
    linarith
  have h2 : (1 / (m : ℝ)) * ∑ i, Real.log (GibbsDistribution p0 Φ w (S i) / p0 (S i)) ≤
      (1 / (m : ℝ)) * ∑ i, (- Real.log (p0 (S i))) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => this i) (by positivity)
  linarith

lemma aux_me_cont {X : Type*} [Fintype X] [Nonempty X] {N m : ℕ} (hm : 0 < m) (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) :
    Continuous (MaxEntDualObjective p0 Φ S lam) := by
  have e : MaxEntDualObjective p0 Φ S lam = fun w =>
      ∑ j, w j * EmpiricalFeatureMean Φ S j - Real.log (PartitionFunction p0 Φ w) -
        lam * ∑ j, |w j| := funext fun w => aux_me_Gform hm p0 hp0 Φ S lam w
  rw [e]
  have hZ : Continuous (fun w => PartitionFunction p0 Φ w) := by
    unfold PartitionFunction; fun_prop
  have hL : Continuous (fun w => Real.log (PartitionFunction p0 Φ w)) :=
    hZ.log (fun w => (aux_me_Zpos p0 hp0 Φ w).ne')
  fun_prop

lemma aux_me_slope (h : ℝ → ℝ) (d c : ℝ) (hd : HasDerivAt h d 0)
    (hb : ∀ t, h t - h 0 ≤ c * |t|) : |d| ≤ c := by
  have h1 := hd.tendsto_slope_zero_right
  have h2 := hd.tendsto_slope_zero_left
  have u : d ≤ c := by
    refine le_of_tendsto h1 (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
    simp only [zero_add, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht]
    have := hb t
    rw [abs_of_pos ht] at this
    linarith
  have l : -c ≤ d := by
    refine ge_of_tendsto h2 (eventually_nhdsWithin_of_forall fun t (ht : t < 0) => ?_)
    simp only [zero_add, smul_eq_mul]
    have := hb t
    rw [abs_of_neg ht] at this
    have ht' : 0 < -t := by linarith
    have : -c ≤ (-t)⁻¹ * (-(h t - h 0)) := by
      rw [le_inv_mul_iff₀ ht']
      linarith
    calc -c ≤ (-t)⁻¹ * (-(h t - h 0)) := this
      _ = t⁻¹ * (h t - h 0) := by rw [inv_neg]; ring
  exact abs_le.mpr ⟨l, u⟩

lemma aux_me_deriv {X : Type*} [Fintype X] [Nonempty X] {N : ℕ} (p0 : X → ℝ)
    (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (b w v : Fin N → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ j, (w j + t * v j) * b j -
        Real.log (PartitionFunction p0 Φ (fun j => w j + t * v j)))
      (∑ j, v j * b j - ∑ j, v j * ∑ x, GibbsDistribution p0 Φ w x * Φ x j) 0 := by
  set A : X → ℝ := fun x => ∑ j, w j * Φ x j with hA
  set B : X → ℝ := fun x => ∑ j, v j * Φ x j with hB
  have e1 : (fun t : ℝ => ∑ j, (w j + t * v j) * b j) =
      fun t => ∑ j, w j * b j + t * ∑ j, v j * b j := by
    funext t
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : (fun t : ℝ => PartitionFunction p0 Φ (fun j => w j + t * v j)) =
      fun t => ∑ x, p0 x * Real.exp (A x + t * B x) := by
    funext t
    unfold PartitionFunction
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    simp only [hA, hB]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlin : HasDerivAt (fun t : ℝ => ∑ j, w j * b j + t * ∑ j, v j * b j)
      (∑ j, v j * b j) 0 := (hasDerivAt_mul_const _).const_add _
  have hZ : HasDerivAt (fun t : ℝ => ∑ x, p0 x * Real.exp (A x + t * B x))
      (∑ x, p0 x * (Real.exp (A x + 0 * B x) * B x)) 0 :=
    HasDerivAt.fun_sum (fun x _ =>
      (((hasDerivAt_mul_const (B x)).const_add (A x)).exp).const_mul (p0 x))
  have hZ0 : (∑ x, p0 x * Real.exp (A x + 0 * B x)) = PartitionFunction p0 Φ w := by
    simp [hA, PartitionFunction]
  have hZne : (∑ x, p0 x * Real.exp (A x + 0 * B x)) ≠ 0 := by
    rw [hZ0]; exact (aux_me_Zpos p0 hp0 Φ w).ne'
  have hlog := hZ.log hZne
  have key : HasDerivAt (fun t : ℝ => (∑ j, w j * b j + t * ∑ j, v j * b j) -
      Real.log (∑ x, p0 x * Real.exp (A x + t * B x)))
      (∑ j, v j * b j - (∑ x, p0 x * (Real.exp (A x + 0 * B x) * B x)) /
        ∑ x, p0 x * Real.exp (A x + 0 * B x)) 0 := hlin.sub hlog
  convert key using 1
  · funext t
    rw [congrFun e1 t, congrFun e2 t]
  rw [hZ0]
  congr 1
  unfold GibbsDistribution
  simp only [hB, zero_mul, add_zero]
  rw [Finset.sum_div]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hA]
  ring

end FoundationsML.MaxEnt

open FoundationsML.MaxEnt

theorem solution {X : Type*} [Fintype X] {N : ℕ}
    (p0 : X → ℝ) (hp0 : ∀ x, 0 < p0 x) (Φ : X → Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hΦ : ∀ x j, |Φ x j| ≤ r)
    (m : ℕ) (hm : 0 < m) (S : Fin m → X) (lam : ℝ) (hlam : 0 < lam) :
    (↑(⨆ w : Fin N → ℝ, MaxEntDualObjective p0 Φ S lam w) : EReal) =
        sInf (Set.range (MaxEntPrimalObjective p0 Φ S lam)) ∧
      ∀ p_star : X → ℝ,
        IsLeast (Set.range (MaxEntPrimalObjective p0 Φ S lam)) (MaxEntPrimalObjective p0 Φ S lam p_star) →
        ∀ ε : ℝ, 0 < ε → ∀ w : Fin N → ℝ,
          |MaxEntDualObjective p0 Φ S lam w -
              ⨆ w' : Fin N → ℝ, MaxEntDualObjective p0 Φ S lam w'| < ε →
            RelativeEntropy p_star (GibbsDistribution p0 Φ w) ≤ ε := by
  classical
  have hX : Nonempty X := ⟨S ⟨0, hm⟩⟩
  have hGf : ∀ w, MaxEntDualObjective p0 Φ S lam w = ∑ j, w j * EmpiricalFeatureMean Φ S j -
      Real.log (PartitionFunction p0 Φ w) - lam * ∑ j, |w j| :=
    fun w => aux_me_Gform hm p0 hp0 Φ S lam w
  -- existence of a maximizer of the dual objective
  obtain ⟨ws, hws⟩ : ∃ ws, ∀ w, MaxEntDualObjective p0 Φ S lam w ≤
      MaxEntDualObjective p0 Φ S lam ws := by
    have hub := aux_me_ub p0 hp0 Φ S lam
    have hcont := aux_me_cont hm p0 hp0 Φ S lam
    have hG0 : MaxEntDualObjective p0 Φ S lam 0 ≤
        (1 / (m : ℝ)) * ∑ i, (- Real.log (p0 (S i))) := by
      have := hub 0
      simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, sub_zero] at this
      exact this
    set c : ℝ := (1 / (m : ℝ)) * ∑ i, (- Real.log (p0 (S i))) with hc
    set R := (c - MaxEntDualObjective p0 Φ S lam 0) / lam with hR
    have hR0 : 0 ≤ R := div_nonneg (by linarith) hlam.le
    obtain ⟨ws, -, hmax⟩ := (isCompact_closedBall (0 : Fin N → ℝ) R).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self hR0⟩ hcont.continuousOn
    rw [isMaxOn_iff] at hmax
    refine ⟨ws, fun w => ?_⟩
    by_cases hw : w ∈ Metric.closedBall (0 : Fin N → ℝ) R
    · exact hmax w hw
    · have hwR : R < ‖w‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw; exact hw
      have h1 : ‖w‖ ≤ ∑ j, |w j| := (pi_norm_le_iff_of_nonneg (by positivity)).mpr
        (fun j => by
          rw [Real.norm_eq_abs]
          exact Finset.single_le_sum (f := fun j => |w j|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j))
      have h2 := hub w
      have h3 := hmax 0 (Metric.mem_closedBall_self hR0)
      have h4 : lam * R = c - MaxEntDualObjective p0 Φ S lam 0 := by
        rw [hR]; field_simp
      have h5 : lam * R < lam * ∑ j, |w j| := mul_lt_mul_of_pos_left (lt_of_lt_of_le hwR h1) hlam
      linarith
  have hqpos := aux_me_gibbs_pos p0 hp0 Φ ws
  have hqsum := aux_me_gibbs_sum p0 hp0 Φ ws
  have hqS : GibbsDistribution p0 Φ ws ∈ Simplex X := ⟨fun x => (hqpos x).le, hqsum⟩
  -- directional first-order bound
  have hdir : ∀ v : Fin N → ℝ, |∑ j, v j * EmpiricalFeatureMean Φ S j -
      ∑ j, v j * ∑ x, GibbsDistribution p0 Φ ws x * Φ x j| ≤ lam * ∑ j, |v j| := by
    intro v
    apply aux_me_slope _ _ _ (aux_me_deriv p0 hp0 Φ (EmpiricalFeatureMean Φ S) ws v)
    intro t
    have h1 := hws (fun j => ws j + t * v j)
    rw [hGf, hGf] at h1
    simp only [zero_mul, add_zero]
    have h2 : ∑ j, |ws j + t * v j| ≤ ∑ j, |ws j| + |t| * ∑ j, |v j| := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      calc |ws j + t * v j| ≤ |ws j| + |t * v j| := abs_add_le _ _
        _ = |ws j| + |t| * |v j| := by rw [abs_mul]
    have h3 := mul_le_mul_of_nonneg_left h2 hlam.le
    linarith
  -- feasibility of the Gibbs distribution at the maximizer
  have hfeas : (fun j => ∑ x, GibbsDistribution p0 Φ ws x * Φ x j) ∈
      FeatureConstraintSet Φ S lam := by
    intro j
    have := hdir (Pi.single j 1)
    simp [Pi.single_apply, apply_ite (abs : ℝ → ℝ)] at this
    show |∑ x, GibbsDistribution p0 Φ ws x * Φ x j - EmpiricalFeatureMean Φ S j| ≤ lam
    rw [abs_sub_comm]; exact this
  -- complementary slackness
  have hslack : ∑ j, ws j * EmpiricalFeatureMean Φ S j -
      ∑ j, ws j * ∑ x, GibbsDistribution p0 Φ ws x * Φ x j = lam * ∑ j, |ws j| := by
    have hd := aux_me_deriv p0 hp0 Φ (EmpiricalFeatureMean Φ S) ws ws
    have hd2 : HasDerivAt (fun t : ℝ => (∑ j, (ws j + t * ws j) * EmpiricalFeatureMean Φ S j -
        Real.log (PartitionFunction p0 Φ (fun j => ws j + t * ws j))) -
          lam * ((1 + t) * ∑ j, |ws j|))
        ((∑ j, ws j * EmpiricalFeatureMean Φ S j -
          ∑ j, ws j * ∑ x, GibbsDistribution p0 Φ ws x * Φ x j) - lam * (1 * ∑ j, |ws j|)) 0 :=
      hd.sub ((((hasDerivAt_id' (x := (0:ℝ))).const_add 1).mul_const _).const_mul lam)
    have hmax : IsLocalMax (fun t : ℝ => (∑ j, (ws j + t * ws j) * EmpiricalFeatureMean Φ S j -
        Real.log (PartitionFunction p0 Φ (fun j => ws j + t * ws j))) -
          lam * ((1 + t) * ∑ j, |ws j|)) 0 := by
      filter_upwards [Ioi_mem_nhds (show (-1:ℝ) < 0 by norm_num)] with t ht
      have ht' : (0:ℝ) < 1 + t := by have := Set.mem_Ioi.mp ht; linarith
      have h1 := hws (fun j => ws j + t * ws j)
      rw [hGf, hGf] at h1
      have h2 : ∑ j, |ws j + t * ws j| = (1 + t) * ∑ j, |ws j| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show ws j + t * ws j = (1 + t) * ws j by ring, abs_mul, abs_of_pos ht']
      rw [h2] at h1
      simp only [zero_mul, add_zero, one_mul]
      linarith
    have := hmax.hasDerivAt_eq_zero hd2
    linarith
  have hRq : RelativeEntropy (GibbsDistribution p0 Φ ws) p0 = MaxEntDualObjective p0 Φ S lam ws := by
    have h1 := aux_me_identity p0 hp0 Φ ws (GibbsDistribution p0 Φ ws) hqS
    have h0 : RelativeEntropy (GibbsDistribution p0 Φ ws) (GibbsDistribution p0 Φ ws) = 0 := by
      unfold RelativeEntropy
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [div_self (hqpos x).ne', Real.log_one, mul_zero]
    rw [hGf]
    linarith
  have hFq : MaxEntPrimalObjective p0 Φ S lam (GibbsDistribution p0 Φ ws) =
      ((MaxEntDualObjective p0 Φ S lam ws : ℝ) : EReal) := by
    unfold MaxEntPrimalObjective
    rw [if_pos hqS, if_pos hfeas, add_zero, hRq]
  have hFlb : ∀ p, ((MaxEntDualObjective p0 Φ S lam ws : ℝ) : EReal) ≤
      MaxEntPrimalObjective p0 Φ S lam p := by
    intro p
    unfold MaxEntPrimalObjective
    split_ifs with h1 h2
    · rw [add_zero, EReal.coe_le_coe_iff]
      have := aux_me_weak hm p0 hp0 Φ S lam ws p h1 h2
      have := aux_me_gibbs_ineq p (GibbsDistribution p0 Φ ws) h1 hqpos hqsum
      linarith
    all_goals simp
  have hsup : (⨆ w : Fin N → ℝ, MaxEntDualObjective p0 Φ S lam w) =
      MaxEntDualObjective p0 Φ S lam ws :=
    le_antisymm (ciSup_le hws) (le_ciSup ⟨_, by rintro _ ⟨w, rfl⟩; exact hws w⟩ ws)
  have hinf : sInf (Set.range (MaxEntPrimalObjective p0 Φ S lam)) =
      ((MaxEntDualObjective p0 Φ S lam ws : ℝ) : EReal) :=
    le_antisymm (sInf_le ⟨_, hFq⟩) (le_sInf (by rintro _ ⟨p, rfl⟩; exact hFlb p))
  refine ⟨by rw [hsup, hinf], ?_⟩
  intro p_star hls ε hε w hw
  have hFs : MaxEntPrimalObjective p0 Φ S lam p_star =
      ((MaxEntDualObjective p0 Φ S lam ws : ℝ) : EReal) :=
    le_antisymm ((hls.2 (Set.mem_range_self (GibbsDistribution p0 Φ ws))).trans_eq hFq)
      (hFlb p_star)
  unfold MaxEntPrimalObjective at hFs
  split_ifs at hFs with h1 h2
  · rw [add_zero, EReal.coe_eq_coe_iff] at hFs
    have := aux_me_weak hm p0 hp0 Φ S lam w p_star h1 h2
    rw [hsup] at hw
    have := (abs_lt.mp hw).1
    linarith
  all_goals simp at hFs
