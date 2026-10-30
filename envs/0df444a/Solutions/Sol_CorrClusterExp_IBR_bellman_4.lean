-- Prove2me | solution 1 for CorrClusterExp.IBR.bellman_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T12:41:10.572988+00:00
-- url     : https://prove2.me/submissions/cdd7252b-9c93-4a3b-9aaf-3aaf3b4a5c33

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
 theorem _root_.prior_variance_bounds (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (hn : 0 < n)
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

namespace Queelius.ClusterPartitions
open CorrClusterExp.IBR Queelius.ClusterRelaxation
lemma grouped_ones (n k : ℕ) : KGrouped k (Composition.ones n) := by
  intro h hh
  exact ⟨h*k,by simpa [Composition.ones_sizeUpTo,Nat.min_eq_left hh.le]⟩
lemma dp_nonneg {n : ℕ} (q : ℝ) (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) : 0 ≤ VDP q w := by
  unfold VDP
  apply le_ciInf
  intro c
  exact worst_nonneg _ w hw
lemma grouped_nonneg {n : ℕ} (q : ℝ) (k : ℕ) (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) : 0 ≤ Vk q k w := by
  letI : Nonempty {c : Composition n // KGrouped k c} := ⟨⟨Composition.ones n,grouped_ones n k⟩⟩
  unfold Vk
  apply le_ciInf
  intro c
  exact worst_nonneg _ w hw
lemma dp_le_grouped {n : ℕ} (q : ℝ) (k : ℕ) (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) :
    VDP q w ≤ Vk q k w := by
  have hb : BddBelow (Set.range (fun c : Composition n => VIBR q w c)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨c,rfl⟩
    exact worst_nonneg _ w hw
  letI : Nonempty {c : Composition n // KGrouped k c} := ⟨⟨Composition.ones n,grouped_ones n k⟩⟩
  unfold Vk VDP
  apply le_ciInf
  intro c
  exact ciInf_le hb c.1
lemma frac_singleton (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (z : Fin 1 → Bool) :
    fracLaw q 1 z=∏ i,bern q (z i) := by
  have hf : ⌊q⌋₊=0 := Nat.floor_eq_zero.mpr hq1
  have hc : ⌈q⌉₊=1 := by
    have h1 : ⌈q⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using hq1.le)
    have h0 : 0 < ⌈q⌉₊ := Nat.ceil_pos.mpr hq0
    omega
  have hs : (Finset.univ.filter (fun i : Fin 1 => z i=true)).card=if z 0=true then 1 else 0 := by
    have he (i : Fin 1) : z i=z 0 := congrArg z (Subsingleton.elim i 0)
    by_cases hz : z 0=true <;> simp [he,hz]
  unfold fracLaw
  simp only [Nat.cast_one,mul_one,hf,hc,hs,Nat.choose_zero_right,Nat.choose_self]
  by_cases hz : z 0=true <;> simp [hz,bern]
lemma singleton_product (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) (hm : m=1)
    (z : Fin m → Bool) : fracLaw q m z=∏ i,bern q (z i) := by
  subst m
  exact frac_singleton q hq0 hq1 z
lemma ibr_ones {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ibrLaw q (Composition.ones n)=independentLaw q := by
  funext z
  unfold ibrLaw independentLaw
  calc
    _ = ∏ j : Fin (Composition.ones n).length,∏ i,bern q (z ((Composition.ones n).embedding j i)) := by
      apply Finset.prod_congr rfl
      intro j _
      exact singleton_product q hq0 hq1 _ (Composition.ones_blocksFun n j) _
    _ = _ := Composition.prod_prod_apply_embedding (fun i => bern q (z i)) (Composition.ones n)
lemma ibr_ones_variance {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) :
    IsExperiment q (ibrLaw q (Composition.ones n)) ∧
      VIBR q w (Composition.ones n)=∑ i,w i^2 := by
  rw [ibr_ones q hq0 hq1]
  refine ⟨independent_experiment q hq0.le hq1.le,?_⟩
  unfold VIBR
  rw [ibr_ones q hq0 hq1,independent_corr q hq0 hq1,worst_identity w hw]
lemma dp_upper {n : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) : VDP q w ≤ ∑ i,w i^2 := by
  have hb : BddBelow (Set.range (fun c : Composition n => VIBR q w c)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨c,rfl⟩
    exact worst_nonneg _ w hw
  have he := ciInf_le hb (Composition.ones n)
  simpa only [VDP,(ibr_ones_variance q hq0 hq1 w hw).2] using he
lemma ratio_relaxation_and_grouped (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ)
    (hn : 0 < n) (w : Fin n → ℝ) (hw0 : ∀ i,0 ≤ w i) (hw1 : 0 < w ⟨0,hn⟩) :
    VDP q w/VOPT q w ≤ VDP q w/VLB w ∧
      VDP q w/VLB w ≤ ⨅ k : ℕ+,Vk q k w/VLB w := by
  have hl := relaxation_lower w hw0 ⟨0,hn⟩
  have hp : 0 < VLB w := lt_of_lt_of_le (sq_pos_of_pos hw1) ((le_max_left _ _).trans hl)
  refine ⟨div_le_div_of_nonneg_left (dp_nonneg q w hw0) hp (relaxation_api q hq0 hq n w hw0),?_⟩
  apply le_ciInf
  intro k
  exact div_le_div_of_nonneg_right (dp_le_grouped q k w hw0) hp.le
end Queelius.ClusterPartitions

namespace CorrClusterExp.IBR
 theorem _root_.prior_ratios (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (hn : 0 < n)
    (w : Fin n → ℝ) (hw0 : ∀ i,0 ≤ w i) (hw : Antitone w) (hw1 : 0 < w ⟨0,hn⟩) :
    VDP q w/VOPT q w ≤ VDP q w/VLB w ∧
      VDP q w/VLB w ≤ ⨅ k : ℕ+,Vk q k w/VLB w := by
  exact Queelius.ClusterPartitions.ratio_relaxation_and_grouped q hq0 hq n hn w hw0 hw1
end CorrClusterExp.IBR

namespace Queelius.ClusterFractional
open CorrClusterExp.IBR
noncomputable def treated {m : ℕ} (z : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => z i=true)
noncomputable def assignmentEquiv (m : ℕ) : (Fin m → Bool) ≃ Finset (Fin m) := by
  classical
  exact {
    toFun := treated
    invFun := fun s i => decide (i ∈ s)
    left_inv := by intro z;funext i;cases hz : z i <;> simp [treated,hz]
    right_inv := by intro s;ext i;simp [treated]
  }
lemma layer_count (m k : ℕ) :
    (∑ z : Fin m → Bool,if (treated z).card=k then (1:ℝ) else 0)=(m.choose k:ℝ) := by
  classical
  have he := (assignmentEquiv m).sum_comp (fun s : Finset (Fin m) => if s.card=k then (1:ℝ) else 0)
  change (∑ z : Fin m → Bool,if ((assignmentEquiv m) z).card=k then (1:ℝ) else 0)=_
  rw [he]
  simp only [Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,add_zero,nsmul_eq_mul,mul_one]
  rw [Finset.univ_filter_card_eq,Finset.card_powersetCard]
  simp
noncomputable def uniformCard (m k : ℕ) (z : Fin m → Bool) : ℝ :=
  if (treated z).card=k then 1/(m.choose k:ℝ) else 0
lemma uniform_nonneg (m k : ℕ) (z : Fin m → Bool) : 0 ≤ uniformCard m k z := by
  unfold uniformCard;split_ifs <;> positivity
lemma uniform_mass (m k : ℕ) (hk : k ≤ m) :
    (∑ z : Fin m → Bool,uniformCard m k z)=1 := by
  classical
  have he (z : Fin m → Bool) : uniformCard m k z=
      (if (treated z).card=k then (1:ℝ) else 0)/(m.choose k:ℝ) := by
    unfold uniformCard;split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_div,layer_count,div_self]
  exact_mod_cast (Nat.choose_pos hk).ne'
lemma uniform_size (m k : ℕ) (hk : k ≤ m) :
    (∑ z : Fin m → Bool,((treated z).card:ℝ)*uniformCard m k z)=(k:ℝ) := by
  have he (z : Fin m → Bool) : ((treated z).card:ℝ)*uniformCard m k z=(k:ℝ)*uniformCard m k z := by
    unfold uniformCard;split_ifs with hz
    · rw [hz]
    · simp
  simp_rw [he]
  rw [← Finset.mul_sum,uniform_mass m k hk,mul_one]
lemma treated_sum {m : ℕ} (z : Fin m → Bool) :
    (treated z).card=∑ i : Fin m,if z i=true then 1 else 0 := by
  classical
  simp [treated,Finset.sum_ite]
def relabel (m : ℕ) (e : Fin m ≃ Fin m) : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun z := z ∘ e
  invFun z := z ∘ e.symm
  left_inv z := by funext i;simp
  right_inv z := by funext i;simp
lemma treated_relabel (m : ℕ) (e : Fin m ≃ Fin m) (z : Fin m → Bool) :
    (treated (relabel m e z)).card=(treated z).card := by
  rw [treated_sum,treated_sum]
  exact e.sum_comp (fun i => if z i=true then 1 else 0)
lemma uniform_relabel (m k : ℕ) (e : Fin m ≃ Fin m) (z : Fin m → Bool) :
    uniformCard m k (relabel m e z)=uniformCard m k z := by
  unfold uniformCard;rw [treated_relabel]
lemma uniform_marginal_equal (m k : ℕ) (i j : Fin m) :
    (∑ z : Fin m → Bool,if z i=true then uniformCard m k z else 0)=
      ∑ z : Fin m → Bool,if z j=true then uniformCard m k z else 0 := by
  classical
  let e := Equiv.swap i j
  have he := (relabel m e).sum_comp (fun z => if z i=true then uniformCard m k z else 0)
  have hh (z : Fin m → Bool) : (if relabel m e z i=true then uniformCard m k (relabel m e z) else 0)=
      (if z j=true then uniformCard m k z else 0) := by
    rw [uniform_relabel]
    simp [relabel,e,Equiv.swap_apply_left]
  simp_rw [hh] at he
  exact he.symm
end Queelius.ClusterFractional

namespace Queelius.ClusterFractional
open CorrClusterExp.IBR
lemma uniform_marginal (m k : ℕ) (hk : k ≤ m) (i : Fin m) :
    (∑ z : Fin m → Bool,if z i=true then uniformCard m k z else 0)=(k:ℝ)/m := by
  classical
  have he (z : Fin m → Bool) : (∑ j : Fin m,if z j=true then uniformCard m k z else 0)=
      ((treated z).card:ℝ)*uniformCard m k z := by simp [treated,Finset.sum_ite]
  have hs : (m:ℝ)*(∑ z : Fin m → Bool,if z i=true then uniformCard m k z else 0)=(k:ℝ) := by
    calc
      _ = (∑ j : Fin m,∑ z : Fin m → Bool,if z j=true then uniformCard m k z else 0) := by
        simp_rw [uniform_marginal_equal m k _ i]
        simp
      _ = (∑ z : Fin m → Bool,∑ j : Fin m,if z j=true then uniformCard m k z else 0) := Finset.sum_comm
      _ = _ := by simp_rw [he];exact uniform_size m k hk
  apply (eq_div_iff (by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne' : (m:ℝ) ≠ 0)).mpr
  nlinarith
lemma uniform_experiment (m k : ℕ) (hk : k ≤ m) :
    IsExperiment ((k:ℝ)/m) (uniformCard m k) :=
  ⟨uniform_nonneg m k,uniform_mass m k hk,uniform_marginal m k hk⟩
lemma mixture_experiment {m : ℕ} (q r p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P R : (Fin m → Bool) → ℝ) (hP : IsExperiment q P) (hR : IsExperiment r R) :
    IsExperiment (p*q+(1-p)*r) (fun z => p*P z+(1-p)*R z) := by
  classical
  refine ⟨fun z => add_nonneg (mul_nonneg hp0 (hP.1 z))
    (mul_nonneg (sub_nonneg.mpr hp1) (hR.1 z)),?_,?_⟩
  · rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hP.2.1,hR.2.1]
    ring
  · intro i
    have he (z : Fin m → Bool) : (if z i=true then p*P z+(1-p)*R z else 0)=
        p*(if z i=true then P z else 0)+(1-p)*(if z i=true then R z else 0) := by
      split_ifs <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hP.2.2 i,hR.2.2 i]
lemma rounding_mixture (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (⌈x⌉₊:ℝ)-x ∧ (⌈x⌉₊:ℝ)-x ≤ 1 ∧
      ((⌈x⌉₊:ℝ)-x)*(⌊x⌋₊:ℝ)+(1-((⌈x⌉₊:ℝ)-x))*(⌈x⌉₊:ℝ)=x := by
  have hl := Nat.floor_le hx
  have hu := Nat.le_ceil x
  have ht := Nat.ceil_lt_add_one hx
  refine ⟨by linarith,by linarith,?_⟩
  by_cases he : ⌈x⌉₊=⌊x⌋₊
  · have hc : (⌈x⌉₊:ℝ)=(⌊x⌋₊:ℝ) := by exact_mod_cast he
    nlinarith
  · have hstep : ⌈x⌉₊=⌊x⌋₊+1 := by
      have h0 := Nat.floor_le_ceil x
      have h1 := Nat.ceil_le_floor_add_one x
      omega
    have hc : (⌈x⌉₊:ℝ)=(⌊x⌋₊:ℝ)+1 := by exact_mod_cast hstep
    nlinarith
lemma frac_mixture (q : ℝ) (m : ℕ) (z : Fin m → Bool) :
    fracLaw q m z=((⌈q*m⌉₊:ℝ)-q*m)*uniformCard m ⌊q*m⌋₊ z+
      (1-((⌈q*m⌉₊:ℝ)-q*m))*uniformCard m ⌈q*m⌉₊ z := by
  classical
  unfold fracLaw uniformCard treated
  dsimp only
  split_ifs <;> ring
lemma frac_experiment (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    IsExperiment q (fracLaw q m) := by
  have hx : 0 ≤ q*(m:ℝ) := mul_nonneg hq0 (Nat.cast_nonneg m)
  have hxm : q*(m:ℝ) ≤ m := mul_le_of_le_one_left (Nat.cast_nonneg m) hq1
  have hfl : ⌊q*(m:ℝ)⌋₊ ≤ m := Nat.floor_le_of_le hxm
  have hce : ⌈q*(m:ℝ)⌉₊ ≤ m := Nat.ceil_le.mpr hxm
  obtain ⟨hp0,hp1,hmean⟩ := rounding_mixture (q*m) hx
  have hmix := mixture_experiment ((⌊q*m⌋₊:ℝ)/m) ((⌈q*m⌉₊:ℝ)/m)
    ((⌈q*m⌉₊:ℝ)-q*m) hp0 hp1 _ _ (uniform_experiment m _ hfl) (uniform_experiment m _ hce)
  have hm : fracLaw q m=(fun z => ((⌈q*m⌉₊:ℝ)-q*m)*uniformCard m ⌊q*m⌋₊ z+
      (1-((⌈q*m⌉₊:ℝ)-q*m))*uniformCard m ⌈q*m⌉₊ z) := funext (frac_mixture q m)
  rw [hm]
  refine ⟨hmix.1,hmix.2.1,?_⟩
  intro i
  have hn : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
  have h := hmix.2.2 i
  rw [show ((⌈q*m⌉₊:ℝ)-q*m)*((⌊q*m⌋₊:ℝ)/m)+
      (1-((⌈q*m⌉₊:ℝ)-q*m))*((⌈q*m⌉₊:ℝ)/m)=q by
        rw [← mul_div_assoc,← mul_div_assoc,← add_div,hmean,mul_div_cancel_right₀ q hn]] at h
  exact h
end Queelius.ClusterFractional

namespace Queelius.ClusterFractional
open CorrClusterExp.IBR
noncomputable def blockEquiv {n : ℕ} (c : Composition n) :
    (Fin n → Bool) ≃ (∀ j : Fin c.length,Fin (c.blocksFun j) → Bool) :=
  (Equiv.arrowCongr c.blocksFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun j (_ : Fin (c.blocksFun j)) => Bool))
lemma blockEquiv_apply {n : ℕ} (c : Composition n) (z : Fin n → Bool)
    (j : Fin c.length) (i : Fin (c.blocksFun j)) : blockEquiv c z j i=z (c.embedding j i) := rfl
lemma sum_blocks_product {n : ℕ} (c : Composition n)
    (P : ∀ j : Fin c.length,(Fin (c.blocksFun j) → Bool) → ℝ) :
    (∑ z : Fin n → Bool,∏ j,P j (fun i => z (c.embedding j i)))=
      ∏ j,∑ u : Fin (c.blocksFun j) → Bool,P j u := by
  classical
  have he := (blockEquiv c).sum_comp (fun u => ∏ j,P j (u j))
  calc
    _ = ∑ u : ∀ j : Fin c.length,Fin (c.blocksFun j) → Bool,∏ j,P j (u j) := he
    _ = _ := (Fintype.prod_sum _).symm
lemma product_expectation_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ j,Fintype (A j)] (P : ∀ j,A j → ℝ)
    (hP : ∀ j,∑ a,P j a=1) (j : ι) (g : A j → ℝ) :
    (∑ u : ∀ l,A l,(∏ l,P l (u l))*g (u j))=∑ a,P j a*g a := by
  classical
  let G : ∀ l,A l → ℝ := Function.update (fun l (_ : A l) => (1:ℝ)) j g
  have hg (u : ∀ l,A l) : (∏ l,G l (u l))=g (u j) := by
    calc
      _ = G j (u j) := by
        apply Finset.prod_eq_single j
        · intro l _ hlj;simp [G,Function.update_of_ne hlj]
        · intro hj;exact False.elim (hj (Finset.mem_univ j))
      _ = _ := by simp [G]
  calc
    _ = ∑ u : ∀ l,A l,∏ l,P l (u l)*G l (u l) := by
      apply Finset.sum_congr rfl
      intro u _;rw [Finset.prod_mul_distrib,hg]
    _ = ∏ l,∑ a,P l a*G l a := (Fintype.prod_sum (fun l a => P l a*G l a)).symm
    _ = ∑ a,P j a*G j a := by
      apply Finset.prod_eq_single j
      · intro l _ hlj;simp [G,Function.update_of_ne hlj,hP l]
      · intro hj;exact False.elim (hj (Finset.mem_univ j))
    _ = _ := by simp [G]
lemma ibr_mass {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n) :
    (∑ z : Fin n → Bool,ibrLaw q c z)=1 := by
  unfold ibrLaw
  rw [sum_blocks_product]
  simp only [(frac_experiment q hq0 hq1 _).2.1,Finset.prod_const_one]
lemma ibr_experiment {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n) :
    IsExperiment q (ibrLaw q c) := by
  classical
  refine ⟨?_,ibr_mass q hq0 hq1 c,?_⟩
  · intro z;apply Finset.prod_nonneg;intro j _
    exact (frac_experiment q hq0 hq1 _).1 _
  · intro i
    let j := c.index i
    let k := c.invEmbedding i
    have he (z : Fin n → Bool) : (if z i=true then ibrLaw q c z else 0)=
        (∏ l,fracLaw q (c.blocksFun l) (blockEquiv c z l))*
          (if blockEquiv c z j k=true then (1:ℝ) else 0) := by
      have hv (l : Fin c.length) : blockEquiv c z l=(fun a => z (c.embedding l a)) := by funext a;rfl
      simp_rw [hv]
      simp only [Composition.embedding_comp_inv,j,k]
      by_cases hz : z i=true <;> simp [hz,ibrLaw]
    simp_rw [he]
    have hchange := (blockEquiv c).sum_comp (fun u =>
      (∏ l,fracLaw q (c.blocksFun l) (u l))*(if u j k=true then (1:ℝ) else 0))
    rw [hchange]
    rw [product_expectation_single (fun l => fracLaw q (c.blocksFun l))
      (fun l => (frac_experiment q hq0 hq1 (c.blocksFun l)).2.1) j
      (fun u => if u k=true then (1:ℝ) else 0)]
    have hm := (frac_experiment q hq0 hq1 (c.blocksFun j)).2.2 k
    convert hm using 1
    apply Finset.sum_congr rfl
    intro u _;split_ifs <;> simp
end Queelius.ClusterFractional

namespace CorrClusterExp.IBR
theorem _root_.frac_projection (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (hn : 2 ≤ n) :
    IsExperiment q (fracLaw q n) := by
  exact Queelius.ClusterFractional.frac_experiment q hq0.le (by linarith) n
theorem _root_.prior_experiment (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (c : Composition n)
    (w : Fin n → ℝ) (hw0 : ∀ i,0 ≤ w i) : IsExperiment q (ibrLaw q c) := by
  exact Queelius.ClusterFractional.ibr_experiment q hq0.le (by linarith) c
end CorrClusterExp.IBR

namespace Queelius.ClusterFractional
open CorrClusterExp.IBR
lemma product_expectation_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ l,Fintype (A l)] (P : ∀ l,A l → ℝ)
    (hP : ∀ l,∑ a,P l a=1) (j k : ι) (hjk : j ≠ k) (g : A j → ℝ) (h : A k → ℝ) :
    (∑ u : ∀ l,A l,(∏ l,P l (u l))*g (u j)*h (u k))=
      (∑ a,P j a*g a)*(∑ a,P k a*h a) := by
  classical
  let U : ∀ l,A l → ℝ := Function.update (fun l (_ : A l) => (1:ℝ)) j g
  let V : ∀ l,A l → ℝ := Function.update (fun l (_ : A l) => (1:ℝ)) k h
  have hU (u : ∀ l,A l) : (∏ l,U l (u l))=g (u j) := by
    rw [Finset.prod_eq_single j]
    · simp [U]
    · intro l _ hlj;simp [U,Function.update_of_ne hlj]
    · intro hj;exact False.elim (hj (Finset.mem_univ j))
  have hV (u : ∀ l,A l) : (∏ l,V l (u l))=h (u k) := by
    rw [Finset.prod_eq_single k]
    · simp [V]
    · intro l _ hlk;simp [V,Function.update_of_ne hlk]
    · intro hk;exact False.elim (hk (Finset.mem_univ k))
  calc
    _ = ∑ u : ∀ l,A l,∏ l,P l (u l)*U l (u l)*V l (u l) := by
      apply Finset.sum_congr rfl
      intro u _;rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,hU,hV]
    _ = ∏ l,∑ a,P l a*U l a*V l a := (Fintype.prod_sum (fun l a => P l a*U l a*V l a)).symm
    _ = ∏ l,((if l=j then (∑ a,P j a*g a) else 1)*(if l=k then (∑ a,P k a*h a) else 1)) := by
      apply Finset.prod_congr rfl
      intro l _
      by_cases hlj : l=j
      · subst l;simp [U,V,hjk,Function.update_of_ne]
      · by_cases hlk : l=k
        · subst l;simp [U,V,hjk.symm,Function.update_of_ne]
        · simp [U,V,hlj,hlk,Function.update_of_ne,hP l]
    _ = _ := by rw [Finset.prod_mul_distrib];simp
lemma block_pair_moment {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n)
    (j : Fin c.length) (a b : Fin (c.blocksFun j)) :
    (∑ z : Fin n → Bool,if z (c.embedding j a)=true ∧ z (c.embedding j b)=true then ibrLaw q c z else 0)=
      ∑ u : Fin (c.blocksFun j) → Bool,if u a=true ∧ u b=true then fracLaw q (c.blocksFun j) u else 0 := by
  classical
  have he (z : Fin n → Bool) : (if z (c.embedding j a)=true ∧ z (c.embedding j b)=true then ibrLaw q c z else 0)=
      (∏ l,fracLaw q (c.blocksFun l) (blockEquiv c z l))*
        (if blockEquiv c z j a=true ∧ blockEquiv c z j b=true then (1:ℝ) else 0) := by
    have hv (l : Fin c.length) : blockEquiv c z l=(fun a => z (c.embedding l a)) := by funext a;rfl
    simp_rw [hv]
    split_ifs <;> simp [ibrLaw]
  simp_rw [he]
  rw [(blockEquiv c).sum_comp (fun u => (∏ l,fracLaw q (c.blocksFun l) (u l))*
    (if u j a=true ∧ u j b=true then (1:ℝ) else 0))]
  rw [product_expectation_single (fun l => fracLaw q (c.blocksFun l))
    (fun l => (frac_experiment q hq0 hq1 (c.blocksFun l)).2.1) j
    (fun u => if u a=true ∧ u b=true then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl;intro u _;split_ifs <;> simp
lemma cross_pair_moment {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n)
    (j k : Fin c.length) (hjk : j ≠ k) (a : Fin (c.blocksFun j)) (b : Fin (c.blocksFun k)) :
    (∑ z : Fin n → Bool,if z (c.embedding j a)=true ∧ z (c.embedding k b)=true then ibrLaw q c z else 0)=q^2 := by
  classical
  have he (z : Fin n → Bool) : (if z (c.embedding j a)=true ∧ z (c.embedding k b)=true then ibrLaw q c z else 0)=
      (∏ l,fracLaw q (c.blocksFun l) (blockEquiv c z l))*
        (if blockEquiv c z j a=true then (1:ℝ) else 0)*(if blockEquiv c z k b=true then (1:ℝ) else 0) := by
    have hv (l : Fin c.length) : blockEquiv c z l=(fun a => z (c.embedding l a)) := by funext a;rfl
    simp_rw [hv]
    by_cases ha : z (c.embedding j a)=true <;> by_cases hb : z (c.embedding k b)=true <;> simp [ha,hb,ibrLaw]
  simp_rw [he]
  rw [(blockEquiv c).sum_comp (fun u => (∏ l,fracLaw q (c.blocksFun l) (u l))*
    (if u j a=true then (1:ℝ) else 0)*(if u k b=true then (1:ℝ) else 0))]
  rw [product_expectation_two (fun l => fracLaw q (c.blocksFun l))
    (fun l => (frac_experiment q hq0 hq1 (c.blocksFun l)).2.1) j k hjk
    (fun u => if u a=true then (1:ℝ) else 0) (fun u => if u b=true then (1:ℝ) else 0)]
  have hja := (frac_experiment q hq0 hq1 (c.blocksFun j)).2.2 a
  have hkb := (frac_experiment q hq0 hq1 (c.blocksFun k)).2.2 b
  have hj' : (∑ u : Fin (c.blocksFun j) → Bool,fracLaw q (c.blocksFun j) u*(if u a=true then 1 else 0))=q := by
    convert hja using 1;apply Finset.sum_congr rfl;intro u _;split_ifs <;> simp
  have hk' : (∑ u : Fin (c.blocksFun k) → Bool,fracLaw q (c.blocksFun k) u*(if u b=true then 1 else 0))=q := by
    convert hkb using 1;apply Finset.sum_congr rfl;intro u _;split_ifs <;> simp
  rw [hj',hk',pow_two]
lemma corr_same_block {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n)
    (j : Fin c.length) (a b : Fin (c.blocksFun j)) :
    corr q (ibrLaw q c) (c.embedding j a) (c.embedding j b)=corr q (fracLaw q (c.blocksFun j)) a b := by
  unfold corr;rw [block_pair_moment q hq0 hq1 c j a b]
lemma corr_cross_block {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n)
    (j k : Fin c.length) (hjk : j ≠ k) (a : Fin (c.blocksFun j)) (b : Fin (c.blocksFun k)) :
    corr q (ibrLaw q c) (c.embedding j a) (c.embedding k b)=0 := by
  unfold corr;rw [cross_pair_moment q hq0 hq1 c j k hjk a b,sub_self,zero_div]
end Queelius.ClusterFractional

namespace Queelius.ClusterFractional
open CorrClusterExp.IBR Queelius.ClusterRelaxation Matrix
lemma mulVec_block {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n)
    (y : Fin n → ℝ) (j : Fin c.length) (a : Fin (c.blocksFun j)) :
    (corr q (ibrLaw q c) *ᵥ y) (c.embedding j a)=
      (corr q (fracLaw q (c.blocksFun j)) *ᵥ (fun b => y (c.embedding j b))) a := by
  classical
  change (∑ i,corr q (ibrLaw q c) (c.embedding j a) i*y i)=_
  calc
    _ = ∑ k : Fin c.length,∑ b : Fin (c.blocksFun k),
        corr q (ibrLaw q c) (c.embedding j a) (c.embedding k b)*y (c.embedding k b) :=
      (Composition.sum_sum_apply_embedding _ c).symm
    _ = ∑ b : Fin (c.blocksFun j),
        corr q (ibrLaw q c) (c.embedding j a) (c.embedding j b)*y (c.embedding j b) := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        simp_rw [corr_cross_block q hq0 hq1 c j k hkj.symm a,zero_mul]
        simp
      · intro hj;exact False.elim (hj (Finset.mem_univ j))
    _ = _ := by simp_rw [corr_same_block q hq0 hq1 c j a];rfl
lemma quadratic_blocks {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n)
    (y : Fin n → ℝ) :
    y ⬝ᵥ (corr q (ibrLaw q c) *ᵥ y)=
      ∑ j : Fin c.length,(fun a => y (c.embedding j a)) ⬝ᵥ
        (corr q (fracLaw q (c.blocksFun j)) *ᵥ (fun a => y (c.embedding j a))) := by
  change (∑ i,y i*(corr q (ibrLaw q c) *ᵥ y) i)=_
  rw [← Composition.sum_sum_apply_embedding (fun i => y i*(corr q (ibrLaw q c) *ᵥ y) i) c]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mulVec_block q hq0 hq1 c y j]
  rfl
lemma worst_attained {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i,0 ≤ w i) : ∃ y ∈ box w,y ⬝ᵥ (S *ᵥ y)=worstCase S w := by
  have hne : (box w).Nonempty := ⟨0,fun i => ⟨le_rfl,hw i⟩⟩
  obtain ⟨y,hy,hmax⟩ := (box_compact w).exists_isMaxOn hne (quadratic_continuous S).continuousOn
  refine ⟨y,hy,?_⟩
  unfold worstCase
  apply le_antisymm
  · exact le_csSup ((box_compact w).bddAbove_image (quadratic_continuous S).continuousOn) ⟨y,hy,rfl⟩
  · apply csSup_le (hne.image _)
    rintro _ ⟨z,hz,rfl⟩
    exact hmax hz
noncomputable def blockValues {n : ℕ} (c : Composition n) :
    (Fin n → ℝ) ≃ (∀ j : Fin c.length,Fin (c.blocksFun j) → ℝ) :=
  (Equiv.arrowCongr c.blocksFinEquiv.symm (Equiv.refl ℝ)).trans
    (Equiv.piCurry (fun j (_ : Fin (c.blocksFun j)) => ℝ))
lemma blockValues_apply {n : ℕ} (c : Composition n) (y : Fin n → ℝ)
    (j : Fin c.length) (a : Fin (c.blocksFun j)) : blockValues c y j a=y (c.embedding j a) := rfl
lemma variance_additivity {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Composition n)
    (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i) :
    VIBR q w c=∑ j : Fin c.length,
      worstCase (corr q (fracLaw q (c.blocksFun j))) (fun a => w (c.embedding j a)) := by
  classical
  have hne : (box w).Nonempty := ⟨0,fun i => ⟨le_rfl,hw i⟩⟩
  have hb := (box_compact w).bddAbove_image (quadratic_continuous (corr q (ibrLaw q c))).continuousOn
  unfold VIBR worstCase
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨y,hy,rfl⟩
    change y ⬝ᵥ (corr q (ibrLaw q c) *ᵥ y) ≤ _
    rw [quadratic_blocks q hq0 hq1 c y]
    apply Finset.sum_le_sum
    intro j _
    have hlocal : (fun a => y (c.embedding j a)) ∈ box (fun a => w (c.embedding j a)) :=
      fun a => hy (c.embedding j a)
    apply le_csSup ((box_compact (fun a => w (c.embedding j a))).bddAbove_image
      (quadratic_continuous (corr q (fracLaw q (c.blocksFun j)))).continuousOn)
    exact ⟨_,hlocal,rfl⟩
  · have hex (j : Fin c.length) : ∃ v ∈ box (fun a => w (c.embedding j a)),
        v ⬝ᵥ (corr q (fracLaw q (c.blocksFun j)) *ᵥ v)=
          worstCase (corr q (fracLaw q (c.blocksFun j))) (fun a => w (c.embedding j a)) :=
      worst_attained _ _ (fun a => hw (c.embedding j a))
    choose ys hys hyv using hex
    let y := (blockValues c).symm ys
    have hyb (j : Fin c.length) (a : Fin (c.blocksFun j)) : y (c.embedding j a)=ys j a := by
      exact congrArg (fun u => u j a) ((blockValues c).apply_symm_apply ys)
    have hy : y ∈ box w := by
      intro i
      have hh := hys (c.index i) (c.invEmbedding i)
      rw [← hyb (c.index i) (c.invEmbedding i),c.embedding_comp_inv i] at hh
      simpa only [c.embedding_comp_inv] using hh
    have hv : y ⬝ᵥ (corr q (ibrLaw q c) *ᵥ y)=
        ∑ j : Fin c.length,worstCase (corr q (fracLaw q (c.blocksFun j))) (fun a => w (c.embedding j a)) := by
      rw [quadratic_blocks q hq0 hq1 c y]
      apply Finset.sum_congr rfl
      intro j _
      rw [show (fun a => y (c.embedding j a))=ys j from funext (hyb j),hyv j]
    change (∑ j : Fin c.length,worstCase (corr q (fracLaw q (c.blocksFun j))) (fun a => w (c.embedding j a))) ≤ _
    rw [← hv]
    exact le_csSup hb ⟨y,hy,rfl⟩
end Queelius.ClusterFractional

namespace CorrClusterExp.IBR
theorem _root_.prior_additivity (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (c : Composition n)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) :
    IsExperiment q (ibrLaw q c) ∧
      VIBR q w c = ∑ j : Fin c.length,
        worstCase (corr q (fracLaw q (c.blocksFun j))) (fun i => w (c.embedding j i)) := by
  exact ⟨Queelius.ClusterFractional.ibr_experiment q hq0.le (by linarith) c,
    Queelius.ClusterFractional.variance_additivity q hq0.le (by linarith) c w hw0⟩
end CorrClusterExp.IBR

namespace Queelius.ClusterBellman
open CorrClusterExp.IBR
noncomputable def blockCost (q : ℝ) (W : ℕ → ℝ) (h : ℕ) : ℝ :=
  worstCase (corr q (fracLaw q h)) (fun i => W i.val)
noncomputable def listCost (q : ℝ) (W : ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | h::t => blockCost q W h+listCost q (fun i => W (h+i)) t
lemma listCost_sum (q : ℝ) (W : ℕ → ℝ) (l : List ℕ) :
    listCost q W l=∑ j : Fin l.length,
      worstCase (corr q (fracLaw q (l.get j))) (fun i => W ((l.take j.val).sum+i.val)) := by
  induction l generalizing W with
  | nil => simp [listCost]
  | cons h t ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons,List.get_cons_zero,Fin.val_zero,List.take_zero,List.sum_nil,zero_add]
    rw [listCost,ih]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [List.get_cons_succ,Fin.val_succ,List.take_succ_cons,List.sum_cons]
    congr 1
    funext i
    congr 1
    omega
lemma variance_list {n : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (W : ℕ → ℝ) (hW : ∀ i,0 ≤ W i) (c : Composition n) :
    VIBR q (fun i : Fin n => W i.val) c=listCost q W c.blocks := by
  rw [Queelius.ClusterFractional.variance_additivity q hq0 hq1 c _ (fun i => hW i.val),listCost_sum]
  rfl
noncomputable def prepend {m : ℕ} (h : ℕ) (hh : 0 < h) (c : Composition m) : Composition (h+m) where
  blocks := h::c.blocks
  blocks_pos := by intro x hx;rcases List.mem_cons.mp hx with rfl|hx;exact hh;exact c.blocks_pos hx
  blocks_sum := by simp [c.blocks_sum]
lemma prepend_cost {m : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (W : ℕ → ℝ) (hW : ∀ i,0 ≤ W i) (h : ℕ) (hh : 0 < h) (c : Composition m) :
    VIBR q (fun i : Fin (h+m) => W i.val) (prepend h hh c)=
      blockCost q W h+VIBR q (fun i : Fin m => W (h+i.val)) c := by
  rw [variance_list q hq0 hq1 W hW,variance_list q hq0 hq1 _ (fun i => hW _)]
  rfl
lemma dp_attained (q : ℝ) (n : ℕ) (w : Fin n → ℝ) :
    ∃ c : Composition n,VDP q w=VIBR q w c := by
  classical
  obtain ⟨c,_,hc⟩ := Finset.exists_min_image Finset.univ (fun c : Composition n => VIBR q w c) Finset.univ_nonempty
  refine ⟨c,le_antisymm ?_ ?_⟩
  · exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) c
  · exact le_ciInf (fun d => hc d (Finset.mem_univ d))
end Queelius.ClusterBellman

namespace Queelius.ClusterBellman
open CorrClusterExp.IBR
lemma prefix_bound_add (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (W : ℕ → ℝ) (hW : ∀ i,0 ≤ W i) (h m : ℕ) (hh : 0 < h) :
    VDP q (fun i : Fin (h+m) => W i.val) ≤
      blockCost q W h+VDP q (fun i : Fin m => W (h+i.val)) := by
  obtain ⟨d,hd⟩ := dp_attained q m (fun i => W (h+i.val))
  have hb : VDP q (fun i : Fin (h+m) => W i.val) ≤
      VIBR q (fun i : Fin (h+m) => W i.val) (prepend h hh d) :=
    ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) _
  rw [prepend_cost q hq0 hq1 W hW h hh d,← hd] at hb
  exact hb
lemma bellman_sequence (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (W : ℕ → ℝ) (hW : ∀ i,0 ≤ W i) (n : ℕ) (hn : 0 < n) :
    (∀ h : ℕ,1 ≤ h → h ≤ n →
      VDP q (fun i : Fin n => W i.val) ≤
        blockCost q W h+VDP q (fun i : Fin (n-h) => W (h+i.val))) ∧
    ∃ h : ℕ,1 ≤ h ∧ h ≤ n ∧
      VDP q (fun i : Fin n => W i.val)=
        blockCost q W h+VDP q (fun i : Fin (n-h) => W (h+i.val)) := by
  have hfirst (h : ℕ) (hh : 1 ≤ h) (hle : h ≤ n) :
      VDP q (fun i : Fin n => W i.val) ≤
        blockCost q W h+VDP q (fun i : Fin (n-h) => W (h+i.val)) := by
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hle
    subst n
    have he : h+m-h=m := by omega
    have hv := congrArg (fun k : ℕ => VDP q (fun i : Fin k => W (h+i.val))) he
    rw [hv]
    exact prefix_bound_add q hq0 hq1 W hW h m hh
  refine ⟨hfirst,?_⟩
  obtain ⟨c,hc⟩ := dp_attained q n (fun i => W i.val)
  have hne : c.blocks ≠ [] := by
    intro he
    have hs := c.blocks_sum
    rw [he,List.sum_nil] at hs
    omega
  obtain ⟨h,t,hblocks⟩ := List.exists_cons_of_ne_nil hne
  have hh : 0 < h := c.blocks_pos (by rw [hblocks];exact List.mem_cons_self)
  have hsum : h+t.sum=n := by simpa only [hblocks,List.sum_cons] using c.blocks_sum
  have hle : h ≤ n := by omega
  let d : Composition t.sum := {
    blocks := t
    blocks_pos := by intro x hx;apply c.blocks_pos;rw [hblocks];exact List.mem_cons_of_mem h hx
    blocks_sum := rfl }
  have hsplit : VIBR q (fun i : Fin n => W i.val) c=
      blockCost q W h+VIBR q (fun i : Fin t.sum => W (h+i.val)) d := by
    rw [variance_list q hq0 hq1 W hW c,variance_list q hq0 hq1 _ (fun i => hW _),hblocks]
    rfl
  have htail : VDP q (fun i : Fin t.sum => W (h+i.val)) ≤
      VIBR q (fun i : Fin t.sum => W (h+i.val)) d :=
    ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) d
  have he : n-h=t.sum := by omega
  refine ⟨h,hh,hle,le_antisymm (hfirst h hh hle) ?_⟩
  rw [he,hc,hsplit]
  linarith
end Queelius.ClusterBellman
namespace CorrClusterExp.IBR
open Matrix Finset
theorem _root_.solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 1 ≤ n)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) :
    (∀ (h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ n),
      VDP q w ≤ worstCase (corr q (fracLaw q h)) (fun i : Fin h => w (Fin.castLE h2 i)) +
        VDP q (fun i : Fin (n - h) => w ⟨h + i.val, by have := i.isLt; omega⟩)) ∧
    ∃ (h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ n),
      VDP q w = worstCase (corr q (fracLaw q h)) (fun i : Fin h => w (Fin.castLE h2 i)) +
        VDP q (fun i : Fin (n - h) => w ⟨h + i.val, by have := i.isLt; omega⟩) := by
  let W : ℕ → ℝ := fun i => if hi : i<n then w ⟨i,hi⟩ else 0
  have hW : ∀ i,0 ≤ W i := by intro i;dsimp [W];split_ifs;exact hw0 _;exact le_rfl
  have hb : (fun i : Fin n => W i.val)=w := by funext i;simp [W,i.isLt]
  have hp (h : ℕ) (hle : h ≤ n) : (fun i : Fin h => W i.val)=(fun i : Fin h => w (Fin.castLE hle i)) := by
    funext i;simp only [W,dif_pos (lt_of_lt_of_le i.isLt hle)];rfl
  have ht (h : ℕ) : (fun i : Fin (n-h) => W (h+i.val))=
      (fun i : Fin (n-h) => w ⟨h+i.val,by have := i.isLt;omega⟩) := by
    funext i
    have hi : h+i.val<n := by have := i.isLt;omega
    simp only [W,dif_pos hi]
  have hs := Queelius.ClusterBellman.bellman_sequence q hq0.le (by linarith) W hW n hn
  constructor
  · intro h h1 h2
    simpa only [hb,Queelius.ClusterBellman.blockCost,hp h h2,ht h] using hs.1 h h1 h2
  · obtain ⟨h,h1,h2,he⟩ := hs.2
    refine ⟨h,h1,h2,?_⟩
    simpa only [hb,Queelius.ClusterBellman.blockCost,hp h h2,ht h] using he
end CorrClusterExp.IBR
