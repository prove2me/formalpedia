-- Prove2me | solution 1 for GaussTesting.lemma_2_14
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T16:43:56.846799+00:00
-- url     : https://prove2.me/submissions/aed4b2d7-20cb-43ae-bc5f-19d15c64229d

import Definitions.Def_GaussTesting_threshold


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GaussTesting
namespace BernoulliProof
noncomputable section

def mass (p : ℝ) (k j : ℕ) : ℝ := p^j*(1-p)^(k-j)
def weight (p : ℝ) (k j : ℕ) : ℝ := (k.choose j : ℝ)*mass p k j
def affinity (p q : ℝ) : ℝ := Real.sqrt (p*q)+Real.sqrt ((1-p)*(1-q))

lemma mass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (k j : ℕ) : 0 ≤ mass p k j := by
  unfold mass
  positivity

lemma mass_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k j : ℕ) : 0 < mass p k j := by
  unfold mass
  positivity

lemma log_mass {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k j : ℕ) :
    Real.log (mass p k j)=(j:ℝ)*Real.log p+((k-j:ℕ):ℝ)*Real.log (1-p) := by
  rw [mass,Real.log_mul (pow_pos hp _).ne' (pow_pos (sub_pos.mpr hp1) _).ne',
    Real.log_pow,Real.log_pow]

lemma threshold_logs {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    threshold p q=(Real.log (1-p)-Real.log (1-q))/
      (Real.log q+Real.log (1-p)-(Real.log p+Real.log (1-q))) := by
  have hq0 : 0 < q := lt_trans hp hpq
  have hp1 : p < 1 := lt_trans hpq hq
  rw [threshold,if_pos ⟨hp.ne',hq.ne⟩,
    Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr hq).ne',
    Real.log_div (mul_pos hq0 (sub_pos.mpr hp1)).ne'
      (mul_pos hp (sub_pos.mpr hq)).ne',
    Real.log_mul hq0.ne' (sub_pos.mpr hp1).ne',
    Real.log_mul hp.ne' (sub_pos.mpr hq).ne']

lemma likelihood_comparison {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1)
    (k j : ℕ) (hk : 0 < k) (hj : j ≤ k) :
    (threshold p q ≤ (j:ℝ)/k → mass p k j ≤ mass q k j) ∧
    ((j:ℝ)/k ≤ threshold p q → mass q k j ≤ mass p k j) := by
  have hq0 : 0 < q := lt_trans hp hpq
  have hp1 : p < 1 := lt_trans hpq hq
  have hlp : Real.log p < Real.log q := Real.log_lt_log hp hpq
  have hlq : Real.log (1-q) < Real.log (1-p) :=
    Real.log_lt_log (sub_pos.mpr hq) (by linarith)
  let a := Real.log q+Real.log (1-p)-(Real.log p+Real.log (1-q))
  let b := Real.log (1-p)-Real.log (1-q)
  have ha : 0 < a := by dsimp [a];linarith
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log (mass q k j)-Real.log (mass p k j)=(j:ℝ)*a-(k:ℝ)*b := by
    rw [log_mass hq0 hq,log_mass hp hp1,Nat.cast_sub hj]
    dsimp [a,b]
    ring
  rw [threshold_logs hp hpq hq]
  change (b/a ≤ (j:ℝ)/k → _) ∧ ((j:ℝ)/k ≤ b/a → _)
  constructor
  · intro ht
    have ht' := (div_le_div_iff₀ ha hkR).mp ht
    apply (Real.log_le_log_iff (mass_pos hp hp1 k j) (mass_pos hq0 hq k j)).mp
    linarith
  · intro ht
    have ht' := (div_le_div_iff₀ hkR ha).mp ht
    apply (Real.log_le_log_iff (mass_pos hq0 hq k j) (mass_pos hp hp1 k j)).mp
    linarith

lemma sqrt_nat_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : Real.sqrt (a^n)=Real.sqrt a^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg ha n),ih,pow_succ]

lemma sqrt_mass_product {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (k j : ℕ) :
    Real.sqrt (mass p k j*mass q k j)=
      Real.sqrt (p*q)^j*Real.sqrt ((1-p)*(1-q))^(k-j) := by
  have he : mass p k j*mass q k j=(p*q)^j*((1-p)*(1-q))^(k-j) := by
    simp only [mass,mul_pow]
    ring
  rw [he,Real.sqrt_mul (by positivity),sqrt_nat_pow _ (by positivity),sqrt_nat_pow _ (by positivity)]

lemma le_sqrt_product {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ≤ Real.sqrt (a*b) := by
  have hb : 0 ≤ b := le_trans ha hab
  have hs := Real.sq_sqrt (mul_nonneg ha hb)
  have hn := Real.sqrt_nonneg (a*b)
  nlinarith

theorem filtered_weight_le_affinity {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) (s : Finset ℕ)
    (hs : s⊆Finset.range (k+1)) (hcmp : ∀ j∈s,mass p k j ≤ mass q k j) :
    (∑ j∈s,weight p k j) ≤ affinity p q^k := by
  calc
    _ ≤ ∑ j∈s,(k.choose j:ℝ)*Real.sqrt (mass p k j*mass q k j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (le_sqrt_product (mass_nonneg hp hp1 k j) (hcmp j hj)) (Nat.cast_nonneg _)
    _ ≤ ∑ j∈Finset.range (k+1),(k.choose j:ℝ)*Real.sqrt (mass p k j*mass q k j) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hs (by intros;positivity)
    _ = affinity p q^k := by
      simp_rw [sqrt_mass_product hp hp1 hq hq1]
      rw [affinity,add_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma affinity_symm (p q : ℝ) : affinity p q=affinity q p := by
  simp only [affinity,mul_comm]

theorem interior_errors {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1)
    (k : ℕ) (hk : 0 < k) :
    (∑ j∈(Finset.range (k+1)).filter (fun j : ℕ => threshold p q < (j:ℝ)/k),weight p k j) ≤ affinity p q^k ∧
    (∑ j∈(Finset.range (k+1)).filter (fun j : ℕ => (j:ℝ)/k ≤ threshold p q),weight q k j) ≤ affinity p q^k := by
  have hq0 : 0 ≤ q := le_trans hp.le hpq.le
  have hp1 : p ≤ 1 := le_trans hpq.le hq.le
  constructor
  · apply filtered_weight_le_affinity hp.le hp1 hq0 hq.le k _ (Finset.filter_subset _ _)
    intro j hj
    obtain ⟨hj,ht⟩ := Finset.mem_filter.mp hj
    exact (likelihood_comparison hp hpq hq k j hk (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj))).1 ht.le
  · rw [affinity_symm p q]
    apply filtered_weight_le_affinity hq0 hq.le hp.le hp1 k _ (Finset.filter_subset _ _)
    intro j hj
    obtain ⟨hj,ht⟩ := Finset.mem_filter.mp hj
    exact (likelihood_comparison hp hpq hq k j hk (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).2 ht

theorem affinity_le_exp {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    affinity p q ≤ Real.exp (-((Real.sqrt q-Real.sqrt p)^2)/2) := by
  have hp' := Real.sq_sqrt hp
  have hq' := Real.sq_sqrt hq
  have hp'' := Real.sq_sqrt (sub_nonneg.mpr hp1)
  have hq'' := Real.sq_sqrt (sub_nonneg.mpr hq1)
  have hs : affinity p q ≤ 1-(Real.sqrt q-Real.sqrt p)^2/2 := by
    rw [affinity,Real.sqrt_mul hp,Real.sqrt_mul (sub_nonneg.mpr hp1)]
    nlinarith [sq_nonneg (Real.sqrt (1-p)-Real.sqrt (1-q))]
  exact hs.trans (by linarith [Real.add_one_le_exp (-((Real.sqrt q-Real.sqrt p)^2)/2)])

theorem affinity_pow_le_exp {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    affinity p q^k ≤ Real.exp (-(k:ℝ)*(Real.sqrt q-Real.sqrt p)^2/2) := by
  have hnonneg : 0 ≤ affinity p q := by unfold affinity;positivity
  have h := pow_le_pow_left₀ hnonneg (affinity_le_exp hp hp1 hq hq1) k
  rw [←Real.exp_nat_mul] at h
  convert h using 1 <;> congr 1 <;> ring

lemma gap_pos {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) :
    0 < (Real.sqrt q-Real.sqrt p)^2 := by
  have h := Real.sqrt_lt_sqrt hp hpq
  exact sq_pos_of_pos (sub_pos.mpr h)

theorem exp_sample_bound {δ d : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hd : 0 < d)
    (k : ℕ) (hk : 8*Real.log (1/δ)/d ≤ k) :
    0 < k ∧ Real.exp (-(k:ℝ)*d/8) ≤ δ := by
  have hlog : 0 < Real.log (1/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by simpa using hδ1))
  have hb : 8*Real.log (1/δ) ≤ (k:ℝ)*d := (div_le_iff₀ hd).mp hk
  have hkR : (0:ℝ) < k := by nlinarith
  refine ⟨by exact_mod_cast hkR,?_⟩
  have hl : Real.log (1/δ) = -Real.log δ := by simp [Real.log_div]
  rw [← Real.exp_log hδ]
  apply Real.exp_le_exp.mpr
  rw [hl] at hb
  linarith

end
end BernoulliProof
end GaussTesting


set_option autoImplicit false

noncomputable section
namespace GaussTesting.BernoulliTail
open Finset

/-- The literal summand used by the public Lemma 2.14. -/
def mass (k j : ℕ) (p : ℝ) : ℝ :=
  (k.choose j:ℝ)*p^j*(1-p)^(k-j)

lemma mass_nonneg (k j : ℕ) (p : ℝ) (hp:0 ≤ p) (hp1:p ≤ 1) : 0 ≤ mass k j p := by
  unfold mass
  positivity

lemma exp_neg_nat (j : ℕ) : Real.exp (-(j:ℝ))=(Real.exp (-1))^j := by
  calc
    Real.exp (-(j:ℝ))=Real.exp ((j:ℝ)*(-1)) := by congr 1;ring
    _ = _ := Real.exp_nat_mul (-1) j

lemma exp_neg_one_le : Real.exp (-1) ≤ (3:ℝ)/8 := by
  rw [Real.exp_neg,← one_div]
  have he:0<Real.exp 1 := Real.exp_pos 1
  apply (div_le_iff₀ he).mpr
  nlinarith [Real.exp_one_gt_d9]

lemma tilted_binomial (k : ℕ) (p : ℝ) :
    (∑j∈range (k+1),mass k j p*(Real.exp (-1))^j)=(p*Real.exp (-1)+(1-p))^k := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  unfold mass
  rw [mul_pow]
  ring

/-- Finite exponential tilting, proved directly on the public binomial sum. -/
lemma lower_tail_tilt (p : ℝ) (hp:0 ≤ p) (hp1:p ≤ 1) (k : ℕ) (hk:1 ≤ k) :
    (∑j∈(range (k+1)).filter (fun j:ℕ=>(j:ℝ)/k ≤ p/2),mass k j p) ≤
      Real.exp ((k:ℝ)*p/2)*(p*Real.exp (-1)+(1-p))^k := by
  let S := (range (k+1)).filter (fun j:ℕ=>(j:ℝ)/k ≤ p/2)
  have hkp:0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have h1:(∑j∈S,mass k j p) ≤
      Real.exp ((k:ℝ)*p/2)*(∑j∈S,mass k j p*(Real.exp (-1))^j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hc:(j:ℝ) ≤ (p/2)*(k:ℝ) := (div_le_iff₀ hkp).mp (Finset.mem_filter.mp hj).2
    have he:1 ≤ Real.exp ((k:ℝ)*p/2-(j:ℝ)) := Real.one_le_exp_iff.mpr (by nlinarith)
    have hw:=mass_nonneg k j p hp hp1
    calc
      mass k j p ≤ mass k j p*Real.exp ((k:ℝ)*p/2-(j:ℝ)) := by nlinarith
      _ = _ := by
        rw [sub_eq_add_neg,Real.exp_add,exp_neg_nat]
        ring
  have h2:(∑j∈S,mass k j p*(Real.exp (-1))^j) ≤
      ∑j∈range (k+1),mass k j p*(Real.exp (-1))^j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j hj hnj=>
      mul_nonneg (mass_nonneg k j p hp hp1) (by positivity))
  exact h1.trans ((mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans_eq
    (by rw [tilted_binomial]))

/-- Lower Chernoff bound with the constant needed for the endpoint cases. -/
theorem lower (p : ℝ) (hp:0 ≤ p) (hp1:p ≤ 1) (k : ℕ) (hk:1 ≤ k) :
    (∑j∈(range (k+1)).filter (fun j:ℕ=>(j:ℝ)/k ≤ p/2),
      (k.choose j:ℝ)*p^j*(1-p)^(k-j)) ≤ Real.exp (-((k:ℝ)*p)/8) := by
  have hb:0 ≤ p*Real.exp (-1)+(1-p) := by positivity
  have he:p*Real.exp (-1)+(1-p) ≤ Real.exp (-(5*p/8)) := by
    have h0:=Real.add_one_le_exp (-(5*p/8))
    have h1:=exp_neg_one_le
    nlinarith
  have hh:=pow_le_pow_left₀ hb he k
  have heq:(Real.exp (-(5*p/8)))^k=Real.exp ((k:ℝ)*(-(5*p/8))) :=
    (Real.exp_nat_mul _ _).symm
  rw [heq] at hh
  have hpos:0 ≤ Real.exp ((k:ℝ)*p/2) := (Real.exp_pos _).le
  calc
    _ ≤ Real.exp ((k:ℝ)*p/2)*(p*Real.exp (-1)+(1-p))^k := lower_tail_tilt p hp hp1 k hk
    _ ≤ Real.exp ((k:ℝ)*p/2)*Real.exp ((k:ℝ)*(-(5*p/8))) := mul_le_mul_of_nonneg_left hh hpos
    _ = _ := by rw [← Real.exp_add];congr 1;ring

lemma mass_reflect (p : ℝ) (k j : ℕ) (hj:j ≤ k) :
    mass k (k-j) p=mass k j (1-p) := by
  have hsub:k-(k-j)=j := by omega
  have hq:1-(1-p)=p := by ring
  simp only [mass,Nat.choose_symm hj,hsub,hq]
  ring

/-- The reflected upper tail, in the strict convention of public Lemma 2.14. -/
theorem upper (p : ℝ) (hp:0 ≤ p) (hp1:p ≤ 1) (k : ℕ) (hk:1 ≤ k) :
    (∑j∈(range (k+1)).filter (fun j:ℕ=>(1+p)/2 < (j:ℝ)/k),
      (k.choose j:ℝ)*p^j*(1-p)^(k-j)) ≤ Real.exp (-((k:ℝ)*(1-p))/8) := by
  let S := range (k+1)
  have hkp:0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hq:0 ≤ 1-p := sub_nonneg.mpr hp1
  have hq1:1-p ≤ 1 := by linarith
  have hreflect:=Finset.sum_range_reflect
    (fun j=>if (1+p)/2 < (j:ℝ)/k then mass k j p else 0) (k+1)
  have heq:(∑j∈S.filter (fun j:ℕ=>(1+p)/2 < (j:ℝ)/k),mass k j p)=
      ∑j∈S,if (1+p)/2 < ((k-j:ℕ):ℝ)/k then mass k (k-j) p else 0 := by
    rw [Finset.sum_filter]
    simpa only [Nat.add_sub_cancel_right] using hreflect.symm
  calc
    _ = ∑j∈S.filter (fun j:ℕ=>(1+p)/2 < (j:ℝ)/k),mass k j p := rfl
    _ = _ := heq
    _ ≤ ∑j∈S,if (j:ℝ)/k ≤ (1-p)/2 then mass k j (1-p) else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk:j ≤ k := by have hmem:=Finset.mem_range.mp hj;omega
      have hm:=mass_reflect p k j hjk
      by_cases hc:(1+p)/2 < ((k-j:ℕ):ℝ)/k
      · have hlt:= (lt_div_iff₀ hkp).mp hc
        have hs:((k-j:ℕ):ℝ)=(k:ℝ)-(j:ℝ) := Nat.cast_sub hjk
        rw [hs] at hlt
        have hl:(j:ℝ)/k ≤ (1-p)/2 := (div_le_iff₀ hkp).mpr (by nlinarith)
        rw [if_pos hc,if_pos hl,hm]
      · rw [if_neg hc]
        split_ifs
        · exact mass_nonneg k j (1-p) hq hq1
        · exact le_rfl
    _ = ∑j∈S.filter (fun j:ℕ=>(j:ℝ)/k ≤ (1-p)/2),mass k j (1-p) :=
      (Finset.sum_filter ..).symm
    _ ≤ _ := lower (1-p) hq hq1 k hk

/-- Convert the endpoint exponential bound to the requested failure level. -/
lemma exp_le_delta (rate δ : ℝ) (hr:0<rate) (hd:0<δ) (k : ℕ)
    (hk:8*Real.log (1/δ)/rate ≤ (k:ℝ)) :
    Real.exp (-((k:ℝ)*rate)/8) ≤ δ := by
  have hlog:Real.log (1/δ)= -Real.log δ := by rw [one_div,Real.log_inv]
  have hh:8*Real.log (1/δ) ≤ (k:ℝ)*rate := (div_le_iff₀ hr).mp hk
  rw [hlog] at hh
  calc
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (by nlinarith)
    _ = δ := Real.exp_log hd

lemma mass_zero (k j : ℕ) : mass k j 0=if j=0 then 1 else 0 := by
  by_cases hj:j=0 <;> simp [mass,hj]

lemma mass_one (k j : ℕ) (hj:j ≤ k) : mass k j 1=if j=k then 1 else 0 := by
  by_cases he:j=k
  · subst j
    simp [mass]
  · have hs:k-j ≠ 0 := by omega
    simp [mass,he,hs]

lemma zero_mean_upper (θ : ℝ) (hθ:0 ≤ θ) (k : ℕ) :
    (∑j∈(range (k+1)).filter (fun j:ℕ=>θ < (j:ℝ)/k),
      (k.choose j:ℝ)*(0:ℝ)^j*(1-0)^(k-j))=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  change mass k j 0=0
  rw [mass_zero]
  have hne:j ≠ 0 := by
    intro he
    have hc:θ < (j:ℝ)/k := (Finset.mem_filter.mp hj).2
    simp only [he,Nat.cast_zero,zero_div] at hc
    linarith
  simp [hne]

lemma one_mean_lower (θ : ℝ) (hθ:θ<1) (k : ℕ) (hk:1 ≤ k) :
    (∑j∈(range (k+1)).filter (fun j:ℕ=>(j:ℝ)/k ≤ θ),
      (k.choose j:ℝ)*(1:ℝ)^j*(1-1)^(k-j))=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  change mass k j 1=0
  have hjk:j ≤ k := by have hmem:=Finset.mem_range.mp (Finset.mem_filter.mp hj).1;omega
  rw [mass_one k j hjk]
  have hne:j ≠ k := by
    intro he
    have hc:(j:ℝ)/k ≤ θ := (Finset.mem_filter.mp hj).2
    have hk0:(k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    rw [he,div_self hk0] at hc
    linarith
  simp [hne]

end GaussTesting.BernoulliTail


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GaussTesting
namespace BernoulliProof

theorem zero_error (q : ℝ) (hq : 0 < q) (k : ℕ) :
    (∑ j∈(Finset.range (k+1)).filter (fun j : ℕ => threshold 0 q < (j:ℝ)/k),
      (k.choose j:ℝ)*0^j*(1-0)^(k-j))=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have ht := (Finset.mem_filter.mp hj).2
  have hj0 : j≠0 := by
    intro hj0
    subst j
    simp only [threshold,ne_eq,not_true_eq_false,false_and,if_false,Nat.cast_zero,zero_div,add_zero] at ht
    linarith
  simp [zero_pow hj0]

theorem one_error (p : ℝ) (hp : p < 1) (k : ℕ) (hk : 0 < k) :
    (∑ j∈(Finset.range (k+1)).filter (fun j : ℕ => (j:ℝ)/k ≤ threshold p 1),
      (k.choose j:ℝ)*1^j*(1-1)^(k-j))=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hj,ht⟩ := Finset.mem_filter.mp hj
  have hjk : j≤k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hjne : j≠k := by
    intro he
    subst j
    simp only [threshold,ne_eq,not_true_eq_false,and_false,if_false,div_self hk0] at ht
    linarith
  have hsub : k-j≠0 := by omega
  simp [zero_pow hsub]

theorem lemma_2_14 :
    ∃ A : ℝ, 0 < A ∧ ∀ (p₁ p₂ δ : ℝ) (k : ℕ), 0 ≤ p₁ → p₁ < p₂ → p₂ ≤ 1 → 0 < δ → δ < 1 →
      A*Real.log (1/δ)/(Real.sqrt p₂-Real.sqrt p₁)^2 ≤ k →
      (∑ j∈(Finset.range (k+1)).filter (fun j : ℕ => threshold p₁ p₂ < (j:ℝ)/k),
          (k.choose j:ℝ)*p₁^j*(1-p₁)^(k-j)) ≤ δ ∧
      (∑ j∈(Finset.range (k+1)).filter (fun j : ℕ => (j:ℝ)/k ≤ threshold p₁ p₂),
          (k.choose j:ℝ)*p₂^j*(1-p₂)^(k-j)) ≤ δ := by
  refine ⟨8,by norm_num,?_⟩
  intro p q δ k hp hpq hq hδ hδ1 hbound
  have hq0 : 0 < q := lt_of_le_of_lt hp hpq
  have hp1 : p < 1 := lt_of_lt_of_le hpq hq
  have hd := gap_pos hp hpq
  obtain ⟨hk,herr⟩ := exp_sample_bound hδ hδ1 hd k hbound
  by_cases hp0 : p=0
  · subst p
    constructor
    · rw [zero_error q hq0 k]
      exact hδ.le
    · have h := BernoulliTail.lower q hq0.le hq k hk
      simp only [threshold,ne_eq,not_true_eq_false,false_and,if_false,add_zero]
      apply h.trans
      simpa only [Real.sqrt_zero,sub_zero,Real.sq_sqrt hq0.le,neg_mul] using herr
  · by_cases hq1 : q=1
    · subst q
      constructor
      · have h := BernoulliTail.upper p hp hp1.le k hk
        simp only [threshold,ne_eq,not_true_eq_false,and_false,if_false]
        apply h.trans
        apply le_trans (Real.exp_le_exp.mpr ?_) herr
        have hs0 := Real.sqrt_nonneg p
        have hs1 : Real.sqrt p ≤ 1 := by
          exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by simpa using hp1.le⟩
        have hs := Real.sq_sqrt hp
        have hgap : (Real.sqrt 1-Real.sqrt p)^2 ≤ 1-p := by
          simp only [Real.sqrt_one]
          nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
        have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
        have hm := neg_le_neg (mul_le_mul_of_nonneg_left hgap hk0)
        simpa only [neg_mul] using div_le_div_of_nonneg_right hm (by norm_num : (0:ℝ) ≤ 8)
      · rw [one_error p hp1 k hk]
        exact hδ.le
    · have hqi : q < 1 := lt_of_le_of_ne hq hq1
      have hi := interior_errors (lt_of_le_of_ne hp (Ne.symm hp0)) hpq hqi k hk
      have he := affinity_pow_le_exp hp hp1.le hq0.le hq k
      have hscale : Real.exp (-(k:ℝ)*(Real.sqrt q-Real.sqrt p)^2/2) ≤
          Real.exp (-(k:ℝ)*(Real.sqrt q-Real.sqrt p)^2/8) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (k:ℝ)*(Real.sqrt q-Real.sqrt p)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
        linarith
      have hfinal := he.trans (hscale.trans herr)
      exact ⟨by simpa only [weight,mass,mul_assoc] using hi.1.trans hfinal,
        by simpa only [weight,mass,mul_assoc] using hi.2.trans hfinal⟩

end BernoulliProof
end GaussTesting

open GaussTesting

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ (p₁ p₂ δ : ℝ) (k : ℕ), 0 ≤ p₁ → p₁ < p₂ → p₂ ≤ 1 → 0 < δ → δ < 1 →
      A * Real.log (1 / δ) / (Real.sqrt p₂ - Real.sqrt p₁) ^ 2 ≤ k →
      (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => threshold p₁ p₂ < (j : ℝ) / k),
          (k.choose j : ℝ) * p₁ ^ j * (1 - p₁) ^ (k - j)) ≤ δ ∧
      (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => (j : ℝ) / k ≤ threshold p₁ p₂),
          (k.choose j : ℝ) * p₂ ^ j * (1 - p₂) ^ (k - j)) ≤ δ  := GaussTesting.BernoulliProof.lemma_2_14
