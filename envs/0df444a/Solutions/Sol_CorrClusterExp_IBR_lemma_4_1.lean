-- Prove2me | solution 1 for CorrClusterExp.IBR.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T09:22:28.888385+00:00
-- url     : https://prove2.me/submissions/4a00901f-902a-4928-8591-584facc741b4

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
namespace CorrClusterExp.IBR
 theorem _root_.solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1/2) (n : ℕ) (w : Fin n → ℝ)
    (hw0 : ∀ i,0 ≤ w i) : VLB w ≤ VOPT q w := by
  exact Queelius.ClusterRelaxation.relaxation q hq0 (by linarith) w hw0
end CorrClusterExp.IBR
