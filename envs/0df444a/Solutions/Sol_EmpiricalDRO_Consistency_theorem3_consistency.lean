-- Prove2me | solution 1 for EmpiricalDRO.Consistency.theorem3_consistency
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T05:22:12.148711+00:00
-- url     : https://prove2.me/submissions/50ef90d6-55a2-412d-9ad8-8a8bb2cdbbdf

-- Complete checked reconstruction of the full native empirical Burg-ball DRO consistency theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_EmpiricalDRO_Consistency_Setting
import Mathlib


-- Begin Canonical
section ModuleScope_Canonical

open MeasureTheory ProbabilityTheory Filter Topology
end ModuleScope_Canonical
-- End Canonical

-- Begin SequenceBasic
section ModuleScope_SequenceBasic

open scoped BigOperators
open Filter Topology
namespace EmpiricalDRO.Consistency.Proof

noncomputable def average (z : ℕ → ℝ) (n : ℕ) : ℝ := (∑ i ∈ Finset.range n, z i) / n

noncomputable def runningMax (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => max (runningMax a n) (a n)

noncomputable def maxSquare (z : ℕ → ℝ) (n : ℕ) : ℝ := runningMax (fun i => (z i)^2) n

lemma runningMax_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ runningMax a n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma le_runningMax (a : ℕ → ℝ) {i n : ℕ} (hi : i < n) : a i ≤ runningMax a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · exact (ih h).trans (le_max_left _ _)
    · have he : i=n := by omega
      subst i
      exact le_max_right _ _

lemma runningMax_le (a : ℕ → ℝ) (n : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i < n, a i ≤ b) : runningMax a n ≤ b := by
  induction n with
  | zero => exact hb
  | succ n ih => exact max_le (ih (fun i hi => h i (by omega))) (h n (by omega))

lemma maxSquare_nonneg (z : ℕ → ℝ) (n : ℕ) : 0 ≤ maxSquare z n := runningMax_nonneg _ _

lemma sq_le_maxSquare (z : ℕ → ℝ) {i n : ℕ} (hi : i < n) : (z i)^2 ≤ maxSquare z n :=
  le_runningMax (fun j => (z j)^2) hi

end EmpiricalDRO.Consistency.Proof
end ModuleScope_SequenceBasic
-- End SequenceBasic

-- Begin CesaroTerms
section ModuleScope_CesaroTerms

open scoped BigOperators
open Filter Topology
namespace EmpiricalDRO.Consistency.Proof

lemma term_div_succ_of_average {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (average a) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => a n / (n+1:ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => average a (n+1)) atTop (𝓝 L) :=
    h.comp (tendsto_add_atTop_nat 1)
  have hh := hs.sub ((tendsto_natCast_div_add_atTop (1:ℝ)).mul h)
  have he (n : ℕ) : average a (n+1) - ((n:ℝ)/(n+1))*average a n = a n/(n+1:ℝ) := by
    by_cases hn : n=0
    · subst n; simp [average]
    · have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
      have hn1 : (n:ℝ)+1≠0 := by positivity
      simp only [average,Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      field_simp
      ring
  simpa only [one_mul,sub_self,he] using hh

lemma runningMax_div_tendsto_zero {a : ℕ → ℝ} (ha : ∀ i, 0≤a i)
    (h : Tendsto (fun n : ℕ => a n/(n+1:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => runningMax a n/(n:ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun n => hb.trans_le (div_nonneg (runningMax_nonneg a n) (Nat.cast_nonneg n))
  · intro b hb
    have hb2 : 0 < b/2 := by positivity
    obtain ⟨K,hK⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 (b/2) hb2)
    let C : ℝ := ∑ i ∈ Finset.range K, a i
    have hC : 0≤C := Finset.sum_nonneg fun i _ => ha i
    have hc := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat C)).2 (b/2) hb2
    filter_upwards [hc, Filter.eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn1
    have hr : runningMax a n ≤ C+(b/2)*(n:ℝ) := by
      apply runningMax_le _ _ _ (by positivity)
      intro i hi
      by_cases hik : i<K
      · exact (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_range.mpr hik)).trans (le_add_of_nonneg_right (by positivity))
      · have hii := hK i (by omega)
        have hit : a i < (b/2)*((i:ℝ)+1) := (div_lt_iff₀ (by positivity)).mp hii
        have hin : (i:ℝ)+1≤n := by exact_mod_cast hi
        have hi2 := mul_le_mul_of_nonneg_left hin hb2.le
        linarith
    have hh := div_le_div_of_nonneg_right hr hn0.le
    rw [add_div,mul_div_cancel_right₀ _ hn0.ne'] at hh
    linarith

lemma maxSquare_div_tendsto_zero {z : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (average (fun i => (z i)^2)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => maxSquare z n/(n:ℝ)) atTop (𝓝 0) :=
  runningMax_div_tendsto_zero (fun i => sq_nonneg (z i)) (term_div_succ_of_average h)

end EmpiricalDRO.Consistency.Proof
end ModuleScope_CesaroTerms
-- End CesaroTerms

-- Begin DoubleStrongLaw
section ModuleScope_DoubleStrongLaw

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Topology
namespace EmpiricalDRO.Consistency.Proof

lemma double_strong_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hi : iIndepFun Z P) (hd : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (h2 : MemLp (Z 0) 2 P) :
    ∀ᵐ ω ∂P, Tendsto (average (fun i => Z i ω)) atTop (𝓝 (∫ ω', Z 0 ω' ∂P)) ∧
      Tendsto (fun n : ℕ => maxSquare (fun i => Z i ω) n/(n:ℝ)) atTop (𝓝 0) := by
  have hm : Integrable (Z 0) P := MemLp.integrable (by norm_num) h2
  have hsq : Integrable (fun ω => (Z 0 ω)^2) P := h2.integrable_sq
  have hi2 := hi.comp (fun _ => fun t : ℝ => t^2) (fun _ => measurable_id.pow_const 2)
  have hd2 : ∀ i, IdentDistrib (fun ω => (Z i ω)^2) (fun ω => (Z 0 ω)^2) P P :=
    fun i => (hd i).comp (measurable_id.pow_const 2)
  have h1 := strong_law_ae_real Z hm (fun _ _ h => hi.indepFun h) hd
  have h22 := strong_law_ae_real (fun i ω => (Z i ω)^2) hsq (fun _ _ h => hi2.indepFun h) hd2
  filter_upwards [h1,h22] with ω hω1 hω2
  exact ⟨hω1,maxSquare_div_tendsto_zero hω2⟩

lemma observed_strong_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] (ξ : ℕ → Ω → Ξ)
    (hi : iIndepFun ξ P) (hd : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    (f : Ξ → ℝ) (hf : Measurable f) (h2 : MemLp (fun ω => f (ξ 0 ω)) 2 P) :
    ∀ᵐ ω ∂P, Tendsto (average (fun i => f (ξ i ω))) atTop (𝓝 (∫ ω', f (ξ 0 ω') ∂P)) ∧
      Tendsto (fun n : ℕ => maxSquare (fun i => f (ξ i ω)) n/(n:ℝ)) atTop (𝓝 0) := by
  exact double_strong_law (fun i ω => f (ξ i ω)) (hi.comp (fun _ => f) (fun _ => hf))
    (fun i => (hd i).comp hf) h2

end EmpiricalDRO.Consistency.Proof
end ModuleScope_DoubleStrongLaw
-- End DoubleStrongLaw

-- Begin QuantileNonnegative
section ModuleScope_QuantileNonnegative

open MeasureTheory ProbabilityTheory
namespace EmpiricalDRO.Consistency.Proof

lemma quantile_nonnegative (α q : ℝ) (hα : α < 1)
    (hq : gaussianReal 0 1 {y : ℝ | y^2≤q}=ENNReal.ofReal (1-α)) : 0≤q := by
  by_contra hn
  have he : {y : ℝ | y^2≤q} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro y hy
    have hh := sq_nonneg y
    simp only [Set.mem_ofPred_eq] at hy
    linarith
  rw [he, measure_empty] at hq
  have hp : 0 < ENNReal.ofReal (1-α) := ENNReal.ofReal_pos.2 (by linarith)
  rw [← hq] at hp
  exact lt_irrefl _ hp

end EmpiricalDRO.Consistency.Proof
end ModuleScope_QuantileNonnegative
-- End QuantileNonnegative

-- Begin SquaredSqueeze
section ModuleScope_SquaredSqueeze

open Filter Topology
namespace EmpiricalDRO.Consistency.Proof

lemma tendsto_of_sq_error {y a e : ℕ → ℝ} {m : ℝ}
    (ha : Tendsto a atTop (𝓝 m)) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, (y n-a n)^2 ≤ e n) : Tendsto y atTop (𝓝 m) := by
  have hsq : Tendsto (fun n => (y n-a n)^2) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => sq_nonneg _) hbound he
  have habs := (Real.continuous_sqrt.tendsto 0).comp hsq
  have hd : Tendsto (fun n => y n-a n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero,Real.norm_eq_abs] using habs
  have hh := hd.add ha
  simpa only [sub_add_cancel, zero_add] using hh

end EmpiricalDRO.Consistency.Proof
end ModuleScope_SquaredSqueeze
-- End SquaredSqueeze

-- Begin BurgHellinger
section ModuleScope_BurgHellinger

open scoped BigOperators
namespace EmpiricalDRO.Consistency.Proof
open EmpiricalDRO.Coverage PhiDivRobust.Counterpart

 theorem ereal_sum_coe {I : Type*} (s : Finset I) (f : I → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, EReal.coe_add, ih]

 theorem burg_sqrt_bound {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t - 1)^2 ≤ -Real.log t + t - 1 := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht)
  rw [Real.log_sqrt ht.le] at h
  have hs := Real.sq_sqrt ht.le
  nlinarith

 theorem weighted_burg_bound {p u : ℝ} (hp : 0 ≤ p) (hu : 0 < u) :
    (((Real.sqrt p - Real.sqrt u)^2 : ℝ) : EReal) ≤ (u : EReal) * burg (p/u) := by
  by_cases ht : 0 < p/u
  · rw [burg, if_pos ht, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have h := mul_le_mul_of_nonneg_left (burg_sqrt_bound ht) hu.le
    have he : u * (Real.sqrt (p/u)-1)^2 = (Real.sqrt p-Real.sqrt u)^2 := by
      rw [Real.sqrt_div hp]
      have hs := Real.sq_sqrt hu.le
      have hn := ne_of_gt (Real.sqrt_pos.2 hu)
      field_simp
      nlinarith [Real.sq_sqrt hp]
    rwa [he] at h
  · rw [burg, if_neg ht, EReal.coe_mul_top_of_pos hu]
    exact le_top

 theorem uniform_feasible {n : ℕ} (hn : 0 < n) {rho : ℝ} (hrho : 0 ≤ rho) :
    (fun _ : Fin n => (1:ℝ)/n) ∈ probUncertaintySet burg (fun _ => (1:ℝ)/n) (rho/n) := by
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.2 hn
  refine ⟨fun _ => by positivity, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · simp only [phiDiv, div_self (ne_of_gt (div_pos one_pos hnR)), burg, show (0:ℝ)<1 by norm_num,
      if_pos, Real.log_one, neg_zero, zero_add, sub_self, EReal.coe_zero, mul_zero, Finset.sum_const_zero]
    exact EReal.coe_nonneg.2 (div_nonneg hrho hnR.le)

 theorem feasible_hellinger {n : ℕ} (hn : 0 < n) {rho : ℝ} {p : Fin n → ℝ}
    (hp : p ∈ probUncertaintySet burg (fun _ => (1:ℝ)/n) (rho/n)) :
    (∑ i, (Real.sqrt (p i) - Real.sqrt ((1:ℝ)/n))^2) ≤ rho/n := by
  have hu : 0 < (1:ℝ)/n := div_pos one_pos (Nat.cast_pos.2 hn)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => weighted_burg_bound (hp.1 i) hu)
  have h := hh.trans hp.2.2
  rw [← ereal_sum_coe] at h
  exact EReal.coe_le_coe_iff.mp h

end EmpiricalDRO.Consistency.Proof
end ModuleScope_BurgHellinger
-- End BurgHellinger

-- Begin FiniteDeviation
section ModuleScope_FiniteDeviation

open scoped BigOperators
namespace EmpiricalDRO.Consistency.Proof
open EmpiricalDRO.Coverage PhiDivRobust.Counterpart

 theorem sqrt_sum_bound {n : ℕ} (hn : 0 < n) {p : Fin n → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∑ i, (Real.sqrt (p i) + Real.sqrt ((1:ℝ)/n))^2 ≤ 4 := by
  have hu : 0 ≤ (1:ℝ)/n := by positivity
  have hh : ∑ i, (Real.sqrt (p i) + Real.sqrt ((1:ℝ)/n))^2 ≤ ∑ i, (2*p i+2*((1:ℝ)/n)) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [Real.sq_sqrt (hp0 i), Real.sq_sqrt hu, sq_nonneg (Real.sqrt (p i)-Real.sqrt ((1:ℝ)/n))]
  have hs : ∑ i : Fin n, (1:ℝ)/n = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [ne_of_gt (Nat.cast_pos.2 hn : 0 < (n:ℝ))]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,hp1,hs] at hh
  linarith

 theorem feasible_deviation_sq {n : ℕ} (hn : 0 < n) {rho : ℝ} (hrho : 0 ≤ rho)
    (z : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, (z i)^2 ≤ M)
    {p : Fin n → ℝ}
    (hp : p ∈ probUncertaintySet burg (fun _ => (1:ℝ)/n) (rho/n)) :
    ((∑ i, p i*z i) - (∑ i,z i)/(n:ℝ))^2 ≤ 4*rho*M/(n:ℝ) := by
  let u : ℝ := 1/(n:ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have he : (∑ i,p i*z i)-(∑ i,z i)/(n:ℝ) =
      ∑ i,(Real.sqrt (p i)-Real.sqrt u)*((Real.sqrt (p i)+Real.sqrt u)*z i) := by
    simp only [Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h1 := Real.sq_sqrt (hp.1 i)
    have h2 := Real.sq_sqrt hu
    dsimp [u] at *
    calc
      _ = (p i - 1/(n:ℝ))*z i := by ring
      _ = (Real.sqrt (p i)^2 - Real.sqrt (1/(n:ℝ))^2)*z i := by rw [h1,h2]
      _ = _ := by ring
  have hb : ∑ i, ((Real.sqrt (p i)+Real.sqrt u)*z i)^2 ≤ 4*M := by
    calc
      _ ≤ ∑ i,M*(Real.sqrt (p i)+Real.sqrt u)^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_pow, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hz i) (sq_nonneg _)
      _ = M*∑ i,(Real.sqrt (p i)+Real.sqrt u)^2 := (Finset.mul_sum _ _ _).symm
      _ ≤ M*4 := mul_le_mul_of_nonneg_left (sqrt_sum_bound hn hp.1 hp.2.1) hM
      _ = _ := mul_comm _ _
  have hH := feasible_hellinger hn hp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i=>Real.sqrt (p i)-Real.sqrt u) (fun i=>(Real.sqrt (p i)+Real.sqrt u)*z i)
  rw [he]
  calc
    _ ≤ _ := hcs
    _ ≤ (rho/(n:ℝ))*(4*M) := mul_le_mul hH hb (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (div_nonneg hrho (Nat.cast_nonneg _))
    _ = _ := by ring

end EmpiricalDRO.Consistency.Proof
end ModuleScope_FiniteDeviation
-- End FiniteDeviation

-- Begin RobustValues
section ModuleScope_RobustValues

open scoped BigOperators
namespace EmpiricalDRO.Consistency.Proof
open EmpiricalDRO.Coverage PhiDivRobust.Counterpart

 theorem extrema_sq_bound (S : Set ℝ) (hne : S.Nonempty) (m R : ℝ) (hR : 0 ≤ R)
    (h : ∀ x ∈ S, (x-m)^2 ≤ R) :
    (sInf S-m)^2 ≤ R ∧ (sSup S-m)^2 ≤ R := by
  have hb : ∀ x ∈ S, m-Real.sqrt R ≤ x ∧ x ≤ m+Real.sqrt R := by
    intro x hx
    have hh := h x hx
    have hs := Real.sq_sqrt hR
    have hp := Real.sqrt_nonneg R
    constructor <;> nlinarith
  have hlo : BddBelow S := ⟨m-Real.sqrt R, fun x hx => (hb x hx).1⟩
  have hup : BddAbove S := ⟨m+Real.sqrt R, fun x hx => (hb x hx).2⟩
  obtain ⟨x,hx⟩ := hne
  have hi1 : m-Real.sqrt R ≤ sInf S := le_csInf ⟨x,hx⟩ (fun y hy => (hb y hy).1)
  have hi2 : sInf S ≤ m+Real.sqrt R := (csInf_le hlo hx).trans (hb x hx).2
  have hs1 : m-Real.sqrt R ≤ sSup S := (hb x hx).1.trans (le_csSup hup hx)
  have hs2 : sSup S ≤ m+Real.sqrt R := csSup_le ⟨x,hx⟩ (fun y hy => (hb y hy).2)
  have hsq := Real.sq_sqrt hR
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hi2), mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hs2)]

 theorem robust_values_sq {n : ℕ} (hn : 0 < n) {rho : ℝ} (hrho : 0 ≤ rho)
    (z : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, (z i)^2 ≤ M) :
    (robustLower burg rho z - (∑ i,z i)/(n:ℝ))^2 ≤ 4*rho*M/(n:ℝ) ∧
    (GenEmpLik.Expansion.robustMean burg rho z - (∑ i,z i)/(n:ℝ))^2 ≤ 4*rho*M/(n:ℝ) := by
  apply extrema_sq_bound
  · exact ⟨_, Set.mem_image_of_mem _ (uniform_feasible hn hrho)⟩
  · positivity
  · rintro y ⟨p,hp,rfl⟩
    exact feasible_deviation_sq hn hrho z hM hz hp

end EmpiricalDRO.Consistency.Proof
end ModuleScope_RobustValues
-- End RobustValues

-- Begin RobustLimits
section ModuleScope_RobustLimits

open scoped BigOperators
open Filter Topology
namespace EmpiricalDRO.Consistency.Proof

lemma robust_limits (rho : ℝ) (hrho : 0≤rho) (z : ℕ → ℝ) (m : ℝ)
    (hmean : Tendsto (average z) atTop (𝓝 m))
    (hmax : Tendsto (fun n : ℕ => maxSquare z n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg rho
      (fun i : Fin n => z i)) atTop (𝓝 m) ∧
    Tendsto (fun n : ℕ => GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg rho
      (fun i : Fin n => z i)) atTop (𝓝 m) := by
  have he : Tendsto (fun n : ℕ => 4*rho*maxSquare z n/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using hmax.const_mul (4*rho)
  have hb : ∀ᶠ n in atTop,
      (EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg rho (fun i : Fin n=>z i)-average z n)^2 ≤ 4*rho*maxSquare z n/(n:ℝ) ∧
      (GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg rho (fun i : Fin n=>z i)-average z n)^2 ≤ 4*rho*maxSquare z n/(n:ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hh := robust_values_sq (by omega : 0<n) hrho (fun i : Fin n=>z i)
      (maxSquare_nonneg z n) (fun i => sq_le_maxSquare z i.isLt)
    simpa only [average,Fin.sum_univ_eq_sum_range] using hh
  exact ⟨tendsto_of_sq_error hmean he (hb.mono fun _ h=>h.1),
    tendsto_of_sq_error hmean he (hb.mono fun _ h=>h.2)⟩

end EmpiricalDRO.Consistency.Proof
end ModuleScope_RobustLimits
-- End RobustLimits

-- Begin NativeConsistency
section ModuleScope_NativeConsistency

open MeasureTheory ProbabilityTheory Filter Topology
namespace EmpiricalDRO.Consistency.Proof

lemma native_consistency {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] (ξ : ℕ → Ω → Ξ)
    (hi : iIndepFun ξ P) (hd : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    (f : Ξ → ℝ) (hf : Measurable f) (h2 : MemLp (fun ω => f (ξ 0 ω)) 2 P)
    (α q : ℝ) (hα : α < 1)
    (hq : gaussianReal 0 1 {y : ℝ | y^2≤q}=ENNReal.ofReal (1-α)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q/2)
        (fun i : Fin n => f (ξ i ω))) atTop (𝓝 (∫ ω', f (ξ 0 ω') ∂P)) ∧
      Tendsto (fun n : ℕ => GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q/2)
        (fun i : Fin n => f (ξ i ω))) atTop (𝓝 (∫ ω', f (ξ 0 ω') ∂P)) := by
  have hr : 0≤q/2 := div_nonneg (quantile_nonnegative α q hα hq) (by norm_num)
  filter_upwards [observed_strong_law ξ hi hd f hf h2] with ω hω
  exact robust_limits (q/2) hr (fun i => f (ξ i ω)) (∫ ω', f (ξ 0 ω') ∂P) hω.1 hω.2

end EmpiricalDRO.Consistency.Proof
end ModuleScope_NativeConsistency
-- End NativeConsistency

-- Begin RootAssembly
section ModuleScope_RootAssembly

open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Consistency

/-- Theorem 3, Lam, arXiv:1605.09349v1, p. 12: under the conditions of Theorem 2 (i.i.d. data,
`0 < Var₀(h(x;ξ)) < ∞`, `Z₀(x) = E₀[h(x;ξ)]` finite), for a fixed decision `x`, both empirical
DRO values `Z_n(x)` (min) and `Z̄_n(x)` (max) over the empirical Burg ball `U_n(χ²_{1,1−α}/(2n))`
converge almost surely to `Z₀(x)`. The sample `ξ_1, …, ξ_n` is `ξ 0, …, ξ (n-1)`, and `q` is the
`(1−α)`-quantile of `χ²₁` (the law of `Y²`, `Y ∼ N(0,1)`). -/
theorem theorem3_consistency {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ξ : Type*} [MeasurableSpace Ξ]
    (ξ : ℕ → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → Ξ → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hhx : Measurable (h x))
    (hL2 : MemLp (fun ω => h x (ξ 0 ω)) 2 P)
    (hvar : 0 < variance (fun ω => h x (ξ 0 ω)) P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (q : ℝ)
    (hq : gaussianReal 0 1 {y : ℝ | y ^ 2 ≤ q} = ENNReal.ofReal (1 - α)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => h x (ξ i ω))) atTop
          (𝓝 (∫ ω', h x (ξ 0 ω') ∂P)) ∧
        Tendsto (fun n : ℕ =>
            GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => h x (ξ i ω))) atTop
          (𝓝 (∫ ω', h x (ξ 0 ω') ∂P)) := by
  have _measurable := hξ
  have _variance := hvar
  have _alpha := hα0
  exact Proof.native_consistency ξ hindep hident (h x) hhx hL2 α q hα1 hq

end EmpiricalDRO.Consistency
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
section ModuleScope_Solution

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ξ : Type*} [MeasurableSpace Ξ]
    (ξ : ℕ → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → Ξ → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hhx : Measurable (h x))
    (hL2 : MemLp (fun ω => h x (ξ 0 ω)) 2 P)
    (hvar : 0 < variance (fun ω => h x (ξ 0 ω)) P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (q : ℝ)
    (hq : gaussianReal 0 1 {y : ℝ | y ^ 2 ≤ q} = ENNReal.ofReal (1 - α)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => h x (ξ i ω))) atTop
          (𝓝 (∫ ω', h x (ξ 0 ω') ∂P)) ∧
        Tendsto (fun n : ℕ =>
            GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => h x (ξ i ω))) atTop
          (𝓝 (∫ ω', h x (ξ 0 ω') ∂P)) := by
  exact EmpiricalDRO.Consistency.theorem3_consistency ξ hξ hindep hident h x hhx hL2 hvar α hα0 hα1 q hq
end ModuleScope_Solution
-- End Solution
