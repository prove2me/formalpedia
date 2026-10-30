-- Prove2me | solution 1 for CorrClusterExp.IBR.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T09:55:20.16744+00:00
-- url     : https://prove2.me/submissions/802b0b29-b690-4960-947f-3cb1d249ce09

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting
open Matrix Finset
namespace Queelius.ClusterRelaxation
open CorrClusterExp.IBR
noncomputable def bern (q : ℝ) (b : Bool) : ℝ := if b then q else 1-q
noncomputable def independentLaw {n : ℕ} (q : ℝ) (z : Fin n → Bool) : ℝ := ∏ i,bern q (z i)
lemma independent_experiment {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsExperiment q (independentLaw (n:=n) q) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro z
    apply Finset.prod_nonneg
    intro i _
    cases h : z i <;> simp [bern,h] <;> linarith
  · unfold independentLaw
    rw [← Fintype.prod_sum]
    simp [bern]
  · intro i
    let K : Fin n → Bool → ℝ := fun j b => bern q b*(if j=i then (if b=true then 1 else 0) else 1)
    have he (z : Fin n → Bool) : (if z i=true then independentLaw q z else 0)=∏ j,K j (z j) := by
      dsimp [K]
      rw [Finset.prod_mul_distrib]
      rw [Finset.prod_ite_eq']
      simp only [Finset.mem_univ,ite_true]
      by_cases h : z i=true <;> simp [h,independentLaw]
    simp_rw [he]
    rw [← Fintype.prod_sum]
    have hs (j : Fin n) : (∑ b : Bool,K j b)=if j=i then q else 1 := by
      by_cases hj : j=i <;> simp [K,hj,bern]
    simp_rw [hs]
    simp
lemma covariance_entry {n : ℕ} (q : ℝ) (P : (Fin n → Bool) → ℝ) (hP : IsExperiment q P)
    (i k : Fin n) :
    (∑ z,P z*((if z i=true then 1 else 0)-q)*((if z k=true then 1 else 0)-q))=
      (∑ z,if z i=true ∧ z k=true then P z else 0)-q^2 := by
  have he (z : Fin n → Bool) : P z*((if z i=true then 1 else 0)-q)*((if z k=true then 1 else 0)-q)=
      (if z i=true ∧ z k=true then P z else 0)-q*(if z i=true then P z else 0)-
        q*(if z k=true then P z else 0)+q^2*P z := by
    by_cases hi : z i=true <;> by_cases hk : z k=true <;> simp [hi,hk] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hP.2.1,hP.2.2 i,hP.2.2 k]
  ring
lemma correlation_psd {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (P : (Fin n → Bool) → ℝ) (hP : IsExperiment q P) : (corr q P).PosSemidef := by
  classical
  let v := fun z : Fin n → Bool => fun i => (if z i=true then (1:ℝ) else 0)-q
  have he : corr q P=(1/(q*(1-q))) • ∑ z,P z • Matrix.vecMulVec (v z) (star (v z)) := by
    ext i k
    simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Matrix.vecMulVec_apply,Pi.star_apply,star_trivial]
    have hentry : (∑ z,P z*(v z i*v z k))=(∑ z,if z i=true ∧ z k=true then P z else 0)-q^2 := by
      simpa only [v,mul_assoc] using covariance_entry q P hP i k
    change ((∑ z,if z i=true ∧ z k=true then P z else 0)-q^2)/(q*(1-q))=
      (1/(q*(1-q)))*(∑ z,P z*(v z i*v z k))
    rw [hentry]
    ring
  rw [he]
  apply Matrix.PosSemidef.smul
  · apply Matrix.posSemidef_sum
    intro z _
    exact (Matrix.posSemidef_vecMulVec_self_star (v z)).smul (hP.1 z)
  · exact one_div_nonneg.mpr (mul_nonneg hq0.le (sub_nonneg.mpr hq1.le))
lemma correlation_diagonal {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (P : (Fin n → Bool) → ℝ) (hP : IsExperiment q P) (i : Fin n) : corr q P i i=1 := by
  unfold corr
  simp only [and_self,hP.2.2 i]
  have hq : q*(1-q) ≠ 0 := mul_ne_zero hq0.ne' (sub_pos.mpr hq1).ne'
  apply (div_eq_one_iff_eq hq).mpr
  ring
lemma correlation_valid {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (P : (Fin n → Bool) → ℝ) (hP : IsExperiment q P) : IsCorrMatrix (corr q P) :=
  ⟨correlation_psd q hq0 hq1 P hP,correlation_diagonal q hq0 hq1 P hP⟩
lemma box_compact {n : ℕ} (w : Fin n → ℝ) : IsCompact (box w) := by
  have he : box w=Set.Icc (0 : Fin n → ℝ) w := by
    ext y
    simp only [CorrClusterExp.IBR.box,Set.mem_setOf_eq,Set.mem_Icc,Pi.le_def,Pi.zero_apply,forall_and]
  rw [he]
  exact isCompact_Icc
lemma quadratic_continuous {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun y => y ⬝ᵥ (S *ᵥ y)) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
lemma worst_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i,0 ≤ w i) : 0 ≤ worstCase S w := by
  apply le_csSup ((box_compact w).bddAbove_image (quadratic_continuous S).continuousOn)
  refine ⟨0,fun i => ⟨le_rfl,hw i⟩,?_⟩
  simp
lemma relaxation {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (w : Fin n → ℝ)
    (hw : ∀ i,0 ≤ w i) : VLB w ≤ VOPT q w := by
  unfold VLB VOPT
  have hb : BddBelow ((fun S : Matrix (Fin n) (Fin n) ℝ => worstCase S w) '' {S | IsCorrMatrix S}) := by
    refine ⟨0,?_⟩
    rintro _ ⟨S,hS,rfl⟩
    exact worst_nonneg S w hw
  apply le_csInf
  · exact ⟨_,⟨independentLaw q,independent_experiment q hq0.le hq1.le,rfl⟩⟩
  · rintro _ ⟨P,hP,rfl⟩
    exact csInf_le hb ⟨corr q P,correlation_valid q hq0 hq1 P hP,rfl⟩
end Queelius.ClusterRelaxation

namespace Queelius.ClusterRelaxation
open CorrClusterExp.IBR
lemma independent_joint {n : ℕ} (q : ℝ) (i k : Fin n) (hik : i ≠ k) :
    (∑ z : Fin n → Bool,if z i=true ∧ z k=true then independentLaw q z else 0)=q^2 := by
  classical
  let K : Fin n → Bool → ℝ := fun j b => bern q b*
    (if j=i then (if b=true then 1 else 0) else 1)*
    (if j=k then (if b=true then 1 else 0) else 1)
  have he (z : Fin n → Bool) :
      (if z i=true ∧ z k=true then independentLaw q z else 0)=∏ j,K j (z j) := by
    dsimp [K]
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.prod_ite_eq']
    simp only [Finset.mem_univ,ite_true]
    by_cases hi : z i=true <;> by_cases hk : z k=true <;> simp [hi,hk,independentLaw]
  simp_rw [he]
  rw [← Fintype.prod_sum]
  have hs (j : Fin n) : (∑ b : Bool,K j b)=
      (if j=i then q else 1)*(if j=k then q else 1) := by
    by_cases hji : j=i
    · subst j;simp [K,bern,hik]
    · by_cases hjk : j=k
      · subst j;simp [K,bern,hji]
      · simp [K,bern,hji,hjk]
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq',sq]
lemma independent_corr {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    corr q (independentLaw (n:=n) q)=1 := by
  ext i k
  by_cases hik : i=k
  · subst k
    simpa using correlation_diagonal q hq0 hq1 (independentLaw q)
      (independent_experiment q hq0.le hq1.le) i
  · simp only [corr,independent_joint q i k hik,sub_self,zero_div]
    simp [Matrix.one_apply,hik]
lemma worst_identity {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) :
    worstCase (1 : Matrix (Fin n) (Fin n) ℝ) w=∑ i,w i^2 := by
  have he (y : Fin n → ℝ) : y ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y)=∑ i,y i^2 := by
    simp [dotProduct,pow_two]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0,⟨0,fun i => ⟨le_rfl,hw i⟩,by simp⟩⟩
    · rintro _ ⟨y,hy,rfl⟩
      change (y ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y)) ≤ _
      rw [he]
      apply Finset.sum_le_sum
      intro i _
      nlinarith [(hy i).1,(hy i).2,hw i]
  · apply le_csSup ((box_compact w).bddAbove_image (quadratic_continuous 1).continuousOn)
    refine ⟨w,fun i => ⟨hw i,le_rfl⟩,he w⟩
lemma optimum_upper {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) : VOPT q w ≤ ∑ i,w i^2 := by
  have hb : BddBelow ((fun P => worstCase (corr q P) w) '' {P | IsExperiment q P}) := by
    refine ⟨0,?_⟩
    rintro _ ⟨P,hP,rfl⟩
    exact worst_nonneg _ w hw
  have he := csInf_le hb ⟨independentLaw q,independent_experiment q hq0.le hq1.le,rfl⟩
  simpa only [VOPT,independent_corr q hq0 hq1,worst_identity w hw] using he
end Queelius.ClusterRelaxation

namespace Queelius.ClusterRelaxation
open CorrClusterExp.IBR
noncomputable def corner {n : ℕ} (w : Fin n → ℝ) (z : Fin n → Bool) : Fin n → ℝ :=
  fun i => if z i=true then w i else 0
lemma corner_mem {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) (z : Fin n → Bool) :
    corner w z ∈ box w := by
  intro i
  by_cases h : z i=true <;> simp [corner,h,hw i]
lemma corner_moment {n : ℕ} (w : Fin n → ℝ) (i k : Fin n) :
    (∑ z : Fin n → Bool,independentLaw (1/2) z*corner w z i*corner w z k)=
      (1/4)*w i*w k+(if i=k then (1/4)*w i*w k else 0) := by
  classical
  by_cases hik : i=k
  · subst k
    have he (z : Fin n → Bool) : independentLaw (1/2) z*corner w z i*corner w z i=
        (if z i=true then independentLaw (1/2) z else 0)*w i^2 := by
      by_cases hi : z i=true <;> simp [corner,hi] <;> ring
    simp_rw [he]
    rw [← Finset.sum_mul,(independent_experiment (n:=n) (1/2) (by norm_num) (by norm_num)).2.2 i]
    simp only [ite_true]
    ring
  · have he (z : Fin n → Bool) : independentLaw (1/2) z*corner w z i*corner w z k=
        (if z i=true ∧ z k=true then independentLaw (1/2) z else 0)*(w i*w k) := by
      by_cases hi : z i=true <;> by_cases hk : z k=true <;> simp [corner,hi,hk] <;> ring
    simp_rw [he]
    rw [← Finset.sum_mul,independent_joint (1/2) i k hik]
    simp only [if_neg hik]
    ring
lemma corner_expectation {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsCorrMatrix S)
    (w : Fin n → ℝ) :
    (∑ z : Fin n → Bool,independentLaw (1/2) z*(corner w z ⬝ᵥ (S *ᵥ corner w z)))=
      (1/4)*(w ⬝ᵥ (S *ᵥ w))+(1/4)*∑ i,w i^2 := by
  classical
  have he : (∑ z : Fin n → Bool,independentLaw (1/2) z*(corner w z ⬝ᵥ (S *ᵥ corner w z)))=
      ∑ i : Fin n,∑ k : Fin n,S i k*(∑ z : Fin n → Bool,
        independentLaw (1/2) z*corner w z i*corner w z k) := by
    change (∑ z : Fin n → Bool,independentLaw (1/2) z*(∑ i : Fin n,corner w z i*(∑ k : Fin n,S i k*corner w z k))) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he]
  simp_rw [corner_moment,mul_add,Finset.sum_add_distrib]
  have hd (i : Fin n) : (∑ k : Fin n,S i k*(if i=k then (1/4)*w i*w k else 0))=(1/4)*w i^2 := by
    simp [mul_ite,hS.2 i,pow_two,mul_assoc]
  simp_rw [hd]
  rw [← Finset.mul_sum]
  congr 1
  change (∑ i : Fin n,∑ k : Fin n,S i k*((1/4)*w i*w k)) =
    (1/4)*(∑ i : Fin n,w i*(∑ k : Fin n,S i k*w k))
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring
lemma quarter_bound {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsCorrMatrix S)
    (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) : (1/4)*∑ i,w i^2 ≤ worstCase S w := by
  have hP := independent_experiment (n:=n) (1/2) (by norm_num) (by norm_num)
  have hb : (∑ z : Fin n → Bool,independentLaw (1/2) z*(corner w z ⬝ᵥ (S *ᵥ corner w z))) ≤
      worstCase S w := by
    calc
      _ ≤ ∑ z : Fin n → Bool,independentLaw (1/2) z*worstCase S w := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (hP.1 z)
        exact le_csSup ((box_compact w).bddAbove_image (quadratic_continuous S).continuousOn)
          ⟨corner w z,corner_mem w hw z,rfl⟩
      _ = _ := by rw [← Finset.sum_mul,hP.2.1,one_mul]
  rw [corner_expectation S hS w] at hb
  have hp : 0 ≤ w ⬝ᵥ (S *ᵥ w) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hS.1).2 w
    simpa only [star_trivial] using h
  linarith
lemma coordinate_bound {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : IsCorrMatrix S)
    (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) (j : Fin n) : w j^2 ≤ worstCase S w := by
  classical
  let y : Fin n → ℝ := Pi.single j (w j)
  have hy : y ∈ box w := by
    intro i
    by_cases hi : i=j
    · subst i;simp [y,hw j]
    · simp [y,Pi.single_eq_of_ne hi,hw i]
  have he : y ⬝ᵥ (S *ᵥ y)=w j^2 := by
    simp [y,Pi.single_apply,Matrix.mulVec,dotProduct,mul_ite,ite_mul,hS.2 j,pow_two]
  rw [← he]
  exact le_csSup ((box_compact w).bddAbove_image (quadratic_continuous S).continuousOn) ⟨y,hy,rfl⟩
lemma relaxation_lower {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) (j : Fin n) :
    max (w j^2) ((1/4)*∑ i,w i^2) ≤ VLB w := by
  unfold VLB
  apply le_csInf
  · refine ⟨worstCase (1 : Matrix (Fin n) (Fin n) ℝ) w,1,?_,rfl⟩
    exact ⟨Matrix.PosSemidef.one,fun i => by simp⟩
  · rintro _ ⟨S,hS,rfl⟩
    exact max_le (coordinate_bound S hS w hw j) (quarter_bound S hS w hw)
end Queelius.ClusterRelaxation
namespace CorrClusterExp.IBR
 theorem _root_.solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (hn : 0 < n)
    (w : Fin n → ℝ) (hw0 : ∀ i,0 ≤ w i) (hw : Antitone w) :
    max (w ⟨0,hn⟩^2) ((1/4)*∑ i,w i^2) ≤ VLB w ∧
      VLB w ≤ VOPT q w ∧ VOPT q w ≤ ∑ i,w i^2 := by
  exact ⟨Queelius.ClusterRelaxation.relaxation_lower w hw0 ⟨0,hn⟩,
    Queelius.ClusterRelaxation.relaxation q hq0 (by linarith) w hw0,
    Queelius.ClusterRelaxation.optimum_upper q hq0 (by linarith) w hw0⟩
end CorrClusterExp.IBR

namespace Queelius.ClusterRelaxation
open CorrClusterExp.IBR
lemma relaxation_api (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (w : Fin n → ℝ)
    (hw0 : ∀ i,0 ≤ w i) : VLB w ≤ VOPT q w := by
  exact relaxation q hq0 (by linarith) w hw0
end Queelius.ClusterRelaxation
