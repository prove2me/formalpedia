-- Prove2me | solution 1 for DataDrivenRO.Moment.worst_case_var_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T07:19:38.340215+00:00
-- url     : https://prove2.me/submissions/0eac99a9-a833-4e3f-b945-4f78deeaa552

import Definitions.Def_DataDrivenRO_Moment_Setting
import Mathlib

section
set_option autoImplicit false
namespace MomentVarCodex

theorem p1feb_cs {d : ℕ} (u y : Fin d → ℝ) :
    u ⬝ᵥ y ≤ DataDrivenRO.Moment.enorm u * DataDrivenRO.Moment.enorm y := by
  unfold DataDrivenRO.Moment.enorm
  have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u y
  simpa [dotProduct, sq] using this

theorem p1feb_key {d : ℕ} (u : Fin d → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    IsGreatest ((fun y : Fin d → ℝ => u ⬝ᵥ y) '' {y | DataDrivenRO.Moment.enorm y ≤ R})
      (R * DataDrivenRO.Moment.enorm u) := by
  have hn : 0 ≤ u ⬝ᵥ u := by
    simpa [dotProduct] using Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (u i))
  have hsq : DataDrivenRO.Moment.enorm u ^ 2 = u ⬝ᵥ u := Real.sq_sqrt hn
  have he : 0 ≤ DataDrivenRO.Moment.enorm u := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · rcases he.eq_or_lt with h | h
    · refine ⟨0, ?_, ?_⟩
      · show DataDrivenRO.Moment.enorm (0 : Fin d → ℝ) ≤ R
        simp [DataDrivenRO.Moment.enorm, hR]
      · simp [← h]
    · have he0 : DataDrivenRO.Moment.enorm u ≠ 0 := h.ne'
      refine ⟨(R / DataDrivenRO.Moment.enorm u) • u, ?_, ?_⟩
      · show DataDrivenRO.Moment.enorm _ ≤ R
        have hh : ((R / DataDrivenRO.Moment.enorm u) • u) ⬝ᵥ
            ((R / DataDrivenRO.Moment.enorm u) • u) = R ^ 2 := by
          rw [smul_dotProduct, dotProduct_smul, ← hsq, smul_eq_mul, smul_eq_mul]
          field_simp
        have hdef : DataDrivenRO.Moment.enorm ((R / DataDrivenRO.Moment.enorm u) • u) =
            Real.sqrt (((R / DataDrivenRO.Moment.enorm u) • u) ⬝ᵥ
              ((R / DataDrivenRO.Moment.enorm u) • u)) := rfl
        simp only [hdef, hh, Real.sqrt_sq hR, le_refl]
      · show u ⬝ᵥ ((R / DataDrivenRO.Moment.enorm u) • u) = R * DataDrivenRO.Moment.enorm u
        rw [dotProduct_smul, ← hsq, smul_eq_mul]
        field_simp
  · rintro _ ⟨y, hy, rfl⟩
    calc u ⬝ᵥ y ≤ DataDrivenRO.Moment.enorm u * DataDrivenRO.Moment.enorm y := p1feb_cs u y
      _ ≤ DataDrivenRO.Moment.enorm u * R := mul_le_mul_of_nonneg_left hy he
      _ = R * DataDrivenRO.Moment.enorm u := mul_comm _ _

/-- The two Cauchy–Schwarz maximizations cited in EC.1.7, p. ec8. -/
theorem accepted_cauchy_schwarz_steps {d : ℕ} (Γ₁ Γ₂ r : ℝ)
    (Shat C : Matrix (Fin d) (Fin d) ℝ)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂) (hr : 0 ≤ r)
    (hC : C.transpose * C = Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (v : Fin d → ℝ) :
    IsGreatest ((fun y : Fin d → ℝ => v ⬝ᵥ y) '' {y | DataDrivenRO.Moment.enorm y ≤ Γ₁})
        (Γ₁ * DataDrivenRO.Moment.enorm v) ∧
    IsGreatest ((fun w : Fin d → ℝ => v ⬝ᵥ Matrix.mulVec C.transpose w) ''
        {w | DataDrivenRO.Moment.enorm w ≤ r}) (r * DataDrivenRO.Moment.enorm (Matrix.mulVec C v)) ∧
    DataDrivenRO.Moment.enorm (Matrix.mulVec C v) =
      Real.sqrt (v ⬝ᵥ Matrix.mulVec (Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) v) := by
  refine ⟨p1feb_key v Γ₁ hΓ₁, ?_, ?_⟩
  · have hf : (fun w : Fin d → ℝ => v ⬝ᵥ Matrix.mulVec C.transpose w) =
        fun w => (Matrix.mulVec C v) ⬝ᵥ w := by
      funext w
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hf]
    exact p1feb_key _ r hr
  · unfold DataDrivenRO.Moment.enorm
    congr 1
    rw [← hC, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]

end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentVarCodex
lemma enorm_coord_le {d : ℕ} (u : Fin d → ℝ) (i : Fin d) : |u i| ≤ DataDrivenRO.Moment.enorm u := by
  have h : (u i)^2 ≤ u ⬝ᵥ u := by
    simpa [dotProduct,pow_two] using Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (u j)) (Finset.mem_univ i)
  simpa only [Real.sqrt_sq_eq_abs,DataDrivenRO.Moment.enorm] using Real.sqrt_le_sqrt h
lemma pcs_coords_memLp {d : ℕ} (R Γ₁ Γ₂ : ℝ) (μ : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) (P : Measure (Fin d → ℝ))
    (hP : P ∈ DataDrivenRO.Moment.PCS R Γ₁ Γ₂ μ S) (i : Fin d) :
    MemLp (fun u => u i) 2 P := by
  let := hP.1
  have hae : ∀ᵐ u ∂P,DataDrivenRO.Moment.enorm u ≤ R := ae_iff.mpr hP.2.1
  apply MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable R
  filter_upwards [hae] with u hu
  simpa only [Real.norm_eq_abs] using (enorm_coord_le u i).trans hu
lemma pcs_scalar_lower {d : ℕ} (R Γ₁ Γ₂ : ℝ) (μ : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) (P : Measure (Fin d → ℝ))
    (hP : P ∈ DataDrivenRO.Moment.PCS R Γ₁ Γ₂ μ S) (v : Fin d → ℝ) :
    ∀ᵐ u ∂P,-(R*DataDrivenRO.Moment.enorm v) ≤ u ⬝ᵥ v := by
  have hae : ∀ᵐ u ∂P,DataDrivenRO.Moment.enorm u ≤ R := ae_iff.mpr hP.2.1
  filter_upwards [hae] with u hu
  have hh := p1feb_cs (-u) v
  have hn : DataDrivenRO.Moment.enorm (-u)=DataDrivenRO.Moment.enorm u := by
    unfold DataDrivenRO.Moment.enorm
    simp
  rw [hn,neg_dotProduct] at hh
  have hm := mul_le_mul_of_nonneg_right hu (Real.sqrt_nonneg (v ⬝ᵥ v))
  change DataDrivenRO.Moment.enorm u*DataDrivenRO.Moment.enorm v ≤ R*DataDrivenRO.Moment.enorm v at hm
  linarith
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentVarCodex
noncomputable def gramMoment {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (P : Measure α) (f : α → ι → ℝ) : Matrix ι ι ℝ := of fun i j => ∫ z,f z i*f z j ∂P
lemma gram_quadratic {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (P : Measure α) (f : α → ι → ℝ) (hf : ∀ i,MemLp (fun z => f z i) 2 P) (q : ι → ℝ) :
    (∫ z,(q ⬝ᵥ f z)^2 ∂P) = q ⬝ᵥ ((gramMoment P f)*ᵥ q) := by
  classical
  have hij (i j : ι) : Integrable (fun z => q i*(f z i*f z j)*q j) P :=
    ((hf i).integrable_mul (hf j)).const_mul (q i) |>.mul_const (q j)
  have hp : (fun z => (q ⬝ᵥ f z)^2) =
      (fun z => ∑ i : ι,∑ j : ι,q i*(f z i*f z j)*q j) := by
    funext z
    unfold dotProduct
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hp,integral_finsetSum]
  · change (∑ i : ι, ∫ z,∑ j : ι,q i*(f z i*f z j)*q j ∂P) =
      ∑ i : ι,q i*(∑ j : ι,(∫ z,f z i*f z j ∂P)*q j)
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_mul_const,integral_const_mul]
      ring
    · intro j hj
      exact hij i j
  · intro i hi
    exact integrable_finsetSum _ (fun j _ => hij i j)
lemma gram_moment_psd {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (P : Measure α) (f : α → ι → ℝ) (hf : ∀ i,MemLp (fun z => f z i) 2 P) :
    (gramMoment P f).PosSemidef := by
  have hh : (gramMoment P f).IsHermitian := by
    ext i j
    change star (∫ z,f z j*f z i ∂P) = ∫ z,f z i*f z j ∂P
    simp only [star_trivial]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => mul_comm _ _)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro q
  simp only [star_trivial]
  rw [← gram_quadratic P f hf q]
  exact integral_nonneg (fun z => sq_nonneg _)
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentVarCodex
lemma scalar_memLp {d : ℕ} (P : Measure (Fin d → ℝ))
    (hc : ∀ i,MemLp (fun u => u i) 2 P) (v : Fin d → ℝ) : MemLp (fun u => u ⬝ᵥ v) 2 P := by
  exact memLp_finsetSum _ (fun i _ => (hc i).mul_const (v i))
lemma scalar_mean {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (hc : ∀ i,MemLp (fun u => u i) 2 P) (v : Fin d → ℝ) :
    (∫ u,u ⬝ᵥ v ∂P)=DataDrivenRO.Moment.mean P ⬝ᵥ v := by
  unfold dotProduct
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const]
    rfl
  · intro i hi
    exact ((hc i).integrable (by norm_num)).mul_const _
lemma scalar_centered_second {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (hc : ∀ i,MemLp (fun u => u i) 2 P) (v : Fin d → ℝ) :
    (∫ u,(u ⬝ᵥ v-(∫ u,u ⬝ᵥ v ∂P))^2 ∂P)=v ⬝ᵥ ((DataDrivenRO.Moment.cov P)*ᵥv) := by
  let m := ∫ u,u ⬝ᵥ v ∂P
  have hf := scalar_memLp P hc v
  have hi := hf.integrable (by norm_num)
  have he : (fun u => (u ⬝ᵥ v-m)^2)=
      (fun u => (u ⬝ᵥ v)^2-(2*m)*(u ⬝ᵥ v)+m^2) := by funext u; ring
  have hvar : (∫ u,(u ⬝ᵥ v-m)^2 ∂P)=(∫ u,(u ⬝ᵥ v)^2 ∂P)-m^2 := by
    rw [he,integral_add (f := fun u => (u ⬝ᵥ v)^2-(2*m)*(u ⬝ᵥ v)) (g := fun _ => m^2)
      (hf.integrable_sq.sub (hi.const_mul _)) (integrable_const _),
      integral_sub (f := fun u => (u ⬝ᵥ v)^2) (g := fun u => (2*m)*(u ⬝ᵥ v)) hf.integrable_sq (hi.const_mul (2*m)),integral_const_mul]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    change (∫ u,(u ⬝ᵥ v)^2 ∂P)-(2*m)*m+m^2=(∫ u,(u ⬝ᵥ v)^2 ∂P)-m^2
    ring
  have hcov : DataDrivenRO.Moment.cov P=gramMoment P (fun u => u)-vecMulVec (DataDrivenRO.Moment.mean P) (DataDrivenRO.Moment.mean P) := by
    ext i j
    rfl
  have hGram : v ⬝ᵥ ((gramMoment P (fun u => u))*ᵥv)=(∫ u,(u ⬝ᵥ v)^2 ∂P) := by
    rw [← gram_quadratic P (fun u => u) hc v]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by
      change (v ⬝ᵥ u)^2=(u ⬝ᵥ v)^2
      rw [dotProduct_comm v u])
  have hm : m=DataDrivenRO.Moment.mean P ⬝ᵥ v := scalar_mean P hc v
  have hd : v ⬝ᵥ DataDrivenRO.Moment.mean P=DataDrivenRO.Moment.mean P ⬝ᵥ v := dotProduct_comm _ _
  rw [hvar,hcov,sub_mulVec,dotProduct_sub,vecMulVec_mulVec,dotProduct_smul]
  simp only [op_smul_eq_mul,hGram,hd,hm,pow_two]

end MomentVarCodex

end


section
set_option autoImplicit false
open Matrix
namespace MomentVarCodex
lemma frob_quadratic_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ (A*ᵥv) ≤ DataDrivenRO.Moment.frob A*(DataDrivenRO.Moment.enorm v)^2 := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d × Fin d))
    (fun i => A i.1 i.2) (fun i => v i.1*v i.2)
  have hsum : (∑ i : Fin d × Fin d,(v i.1*v i.2)^2)=(v ⬝ᵥ v)^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow]
    rw [← Finset.sum_mul_sum]
    simp [dotProduct,pow_two]
  have hnon : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hsq : (DataDrivenRO.Moment.enorm v)^2=v ⬝ᵥ v := Real.sq_sqrt hnon
  rw [hsum,Real.sqrt_sq hnon] at h
  simp only [Fintype.sum_prod_type] at h
  rw [hsq]
  change (∑ i : Fin d,v i*(∑ j : Fin d,A i j*v j)) ≤
    Real.sqrt (∑ i : Fin d,∑ j : Fin d,(A i j)^2)*(v ⬝ᵥ v)
  have he : (∑ i : Fin d,v i*(∑ j : Fin d,A i j*v j))=
      ∑ i : Fin d,∑ j : Fin d,A i j*(v i*v j) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact h

end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentVarCodex
lemma pcs_mean_le {d : ℕ} (R Γ₁ Γ₂ : ℝ) (μ : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ DataDrivenRO.Moment.PCS R Γ₁ Γ₂ μ S) (v : Fin d → ℝ) :
    DataDrivenRO.Moment.mean P ⬝ᵥ v ≤ μ ⬝ᵥ v+Γ₁*DataDrivenRO.Moment.enorm v := by
  have hh := p1feb_cs (DataDrivenRO.Moment.mean P-μ) v
  have hb := mul_le_mul_of_nonneg_right hP.2.2.1 (Real.sqrt_nonneg (v ⬝ᵥ v))
  rw [sub_dotProduct] at hh
  change DataDrivenRO.Moment.enorm (DataDrivenRO.Moment.mean P-μ)*DataDrivenRO.Moment.enorm v ≤ Γ₁*DataDrivenRO.Moment.enorm v at hb
  linarith
lemma pcs_variance_le {d : ℕ} (R Γ₁ Γ₂ : ℝ) (μ : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ DataDrivenRO.Moment.PCS R Γ₁ Γ₂ μ S) (v : Fin d → ℝ) :
    (∫ u,(u ⬝ᵥ v-(∫ u,u ⬝ᵥ v ∂P))^2 ∂P) ≤ v ⬝ᵥ ((S+Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))*ᵥv) := by
  let := hP.1
  have hc := pcs_coords_memLp R Γ₁ Γ₂ μ S P hP
  rw [scalar_centered_second P hc v]
  have hh := frob_quadratic_le (DataDrivenRO.Moment.cov P-S) v
  have hb := mul_le_mul_of_nonneg_right hP.2.2.2 (sq_nonneg (DataDrivenRO.Moment.enorm v))
  have hv := hh.trans hb
  rw [sub_mulVec,dotProduct_sub] at hv
  rw [add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul,one_mulVec]
  simp only [smul_eq_mul]
  have hn : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hs : (DataDrivenRO.Moment.enorm v)^2=v ⬝ᵥ v := Real.sq_sqrt hn
  rw [hs] at hv
  linarith
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory
namespace MomentVarCodex
lemma quantile_bddBelow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ)
    (α L : ℝ) (hα : 0<α) (hL : ∀ᵐ z ∂P,L ≤ f z) :
    BddBelow {y : ℝ | ENNReal.ofReal α ≤ P {z | f z ≤ y}} := by
  refine ⟨L,?_⟩
  intro y hy
  by_contra hn
  have hlt : y<L := lt_of_not_ge hn
  have hz : P {z | ¬ L ≤ f z}=0 := ae_iff.mp hL
  have hs : {z | f z ≤ y} ⊆ {z | ¬ L ≤ f z} := by
    intro z hzy
    change f z ≤ y at hzy
    change ¬ L ≤ f z
    linarith
  have hzero : P {z | f z ≤ y}=0 := measure_mono_null hs hz
  change ENNReal.ofReal α ≤ P {z | f z ≤ y} at hy
  rw [hzero] at hy
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hα)) hy
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory
namespace MomentVarCodex
lemma centered_integral_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ z,f z-(∫ z,f z ∂P) ∂P)=0 := by
  rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _)]
  simp
lemma shifted_second_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P) (b : ℝ) :
    (∫ z,(f z-(∫ z,f z ∂P)+b)^2 ∂P)=(∫ z,(f z-(∫ z,f z ∂P))^2 ∂P)+b^2 := by
  let m := ∫ z,f z ∂P
  have hg : MemLp (fun z => f z-m) 2 P := hf.sub (memLp_const m)
  have hi : Integrable (fun z => f z-m) P := hg.integrable (by norm_num)
  have he : (fun z => (f z-m+b)^2)=
      (fun z => ((f z-m)^2+(2*b)*(f z-m))+b^2) := by funext z; ring
  rw [he]
  rw [integral_add (f := fun z => (f z-m)^2+(2*b)*(f z-m)) (g := fun _ => b^2)
    (hg.integrable_sq.add (hi.const_mul (2*b))) (integrable_const (b^2))]
  rw [integral_add (f := fun z => (f z-m)^2) (g := fun z => (2*b)*(f z-m))
    hg.integrable_sq (hi.const_mul (2*b)),integral_const_mul]
  dsimp only [m]
  rw [centered_integral_zero P f hf]
  simp
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory
namespace MomentVarCodex
lemma shifted_markov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P) (t : ℝ) (ht : 0<t) (b : ℝ) (hb : 0 ≤ b) :
    P.real {z | t ≤ f z-(∫ z,f z ∂P)} ≤
      ((∫ z,(f z-(∫ z,f z ∂P))^2 ∂P)+b^2)/(t+b)^2 := by
  let m := ∫ z,f z ∂P
  have hg : MemLp (fun z => f z-m+b) 2 P := (hf.sub (memLp_const m)).add (memLp_const b)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun z => sq_nonneg (f z-m+b))) hg.integrable_sq ((t+b)^2)
  have hs : {z | t ≤ f z-m} ⊆ {z | (t+b)^2 ≤ (f z-m+b)^2} := by
    intro z hz
    change t ≤ f z-m at hz
    change (t+b)^2 ≤ (f z-m+b)^2
    have hp := mul_nonneg (show 0 ≤ f z-m-t by linarith) (show 0 ≤ f z-m+t+2*b by linarith)
    nlinarith
  have hle := (mul_le_mul_of_nonneg_left (measureReal_mono (μ:=P) hs) (sq_nonneg (t+b))).trans hm
  rw [shifted_second_integral P f hf b] at hle
  apply (le_div_iff₀ (sq_pos_of_pos (add_pos_of_pos_of_nonneg ht hb))).mpr
  simpa only [mul_comm] using hle
lemma cantelli {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P) (t : ℝ) (ht : 0<t) :
    P.real {z | t ≤ f z-(∫ z,f z ∂P)} ≤
      (∫ z,(f z-(∫ z,f z ∂P))^2 ∂P)/((∫ z,(f z-(∫ z,f z ∂P))^2 ∂P)+t^2) := by
  let s := ∫ z,(f z-(∫ z,f z ∂P))^2 ∂P
  have hs : 0 ≤ s := integral_nonneg (fun z => sq_nonneg _)
  have hb : 0 ≤ s/t := div_nonneg hs ht.le
  have hh := shifted_markov P f hf t ht (s/t) hb
  have he : (s+(s/t)^2)/(t+s/t)^2=s/(s+t^2) := by
    have hn1 : t+s/t ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht hb)
    have hn2 : s+t^2 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hs (sq_pos_of_pos ht))
    field_simp [ne_of_gt ht,hn1,hn2]
    ring
  change P.real {z | t ≤ f z-(∫ z,f z ∂P)} ≤ (s+(s/t)^2)/(t+s/t)^2 at hh
  rwa [he] at hh
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory
namespace MomentVarCodex
lemma cantelli_ratio_le {s σ t ε : ℝ} (hs : 0 ≤ s) (hσ : 0 ≤ σ) (hv : s ≤ σ^2)
    (ht : 0<t) (hε0 : 0<ε) (hε1 : ε<1) (hb : Real.sqrt ((1-ε)/ε)*σ ≤ t) :
    s/(s+t^2) ≤ ε := by
  let k := Real.sqrt ((1-ε)/ε)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k^2=(1-ε)/ε := Real.sq_sqrt (div_nonneg (by linarith) hε0.le)
  have hek : ε*k^2=1-ε := by rw [hk2]; field_simp [ne_of_gt hε0]
  have hsq : (k*σ)^2 ≤ t^2 := by
    have hp := mul_nonneg (show 0 ≤ t-k*σ from sub_nonneg.mpr hb)
      (show 0 ≤ t+k*σ from add_nonneg ht.le (mul_nonneg hk hσ))
    nlinarith
  have hc : (1-ε)*σ^2 ≤ ε*t^2 := by
    calc
      _ = ε*(k*σ)^2 := by rw [mul_pow,← hek]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq hε0.le
  have hv' := (mul_le_mul_of_nonneg_left hv (show 0 ≤ 1-ε by linarith)).trans hc
  apply (div_le_iff₀ (add_pos_of_nonneg_of_pos hs (sq_pos_of_pos ht))).mpr
  linarith
lemma cantelli_tail_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P) (σ ε t : ℝ) (hσ : 0 ≤ σ)
    (hv : (∫ z,(f z-(∫ z,f z ∂P))^2 ∂P) ≤ σ^2)
    (hε0 : 0<ε) (hε1 : ε<1) (ht : 0<t) (hb : Real.sqrt ((1-ε)/ε)*σ ≤ t) :
    P.real {z | t ≤ f z-(∫ z,f z ∂P)} ≤ ε :=
  (cantelli P f hf t ht).trans (cantelli_ratio_le (integral_nonneg (fun z => sq_nonneg _)) hσ hv ht hε0 hε1 hb)
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory
namespace MomentVarCodex
lemma cdf_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hm : Measurable f) (m t ε : ℝ)
    (htail : P.real {z | t ≤ f z-m} ≤ ε) :
    ENNReal.ofReal (1-ε) ≤ P {z | f z ≤ m+t} := by
  have hs : {z | m+t<f z} ⊆ {z | t ≤ f z-m} := by
    intro z hz
    change m+t<f z at hz
    change t ≤ f z-m
    linarith
  have hb := (measureReal_mono (μ:=P) hs).trans htail
  have hmeas : MeasurableSet {z | m+t<f z} := measurableSet_lt measurable_const hm
  have he : {z | f z ≤ m+t}={z | m+t<f z}ᶜ := by ext z; simp
  have hc : 1-ε ≤ P.real {z | f z ≤ m+t} := by
    rw [he,measureReal_compl hmeas,probReal_univ]
    linarith
  calc
    ENNReal.ofReal (1-ε) ≤ ENNReal.ofReal (P.real {z | f z ≤ m+t}) := ENNReal.ofReal_le_ofReal hc
    _ = _ := ENNReal.ofReal_toReal (measure_ne_top P _)
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory
namespace MomentVarCodex
lemma quantile_variance_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hm : Measurable f) (hf : MemLp f 2 P) (σ ε L : ℝ)
    (hσ : 0 ≤ σ) (hv : (∫ z,(f z-(∫ z,f z ∂P))^2 ∂P) ≤ σ^2)
    (hε0 : 0<ε) (hε1 : ε<1) (hL : ∀ᵐ z ∂P,L ≤ f z) :
    MultistageStochastic.valueAtRisk P f (1-ε) ≤
      (∫ z,f z ∂P)+Real.sqrt ((1-ε)/ε)*σ := by
  have hb := quantile_bddBelow P f (1-ε) L (by linarith) hL
  apply le_of_forall_pos_le_add
  intro δ hδ
  let t := Real.sqrt ((1-ε)/ε)*σ+δ
  have ht : 0<t := add_pos_of_nonneg_of_pos (mul_nonneg (Real.sqrt_nonneg _) hσ) hδ
  have hk : Real.sqrt ((1-ε)/ε)*σ ≤ t := by dsimp [t]; linarith
  have htail := cantelli_tail_le P f hf σ ε t hσ hv hε0 hε1 ht hk
  have hcdf := cdf_of_tail P f hm (∫ z,f z ∂P) t ε htail
  have hi : MultistageStochastic.valueAtRisk P f (1-ε) ≤ (∫ z,f z ∂P)+t := csInf_le hb hcdf
  simpa only [t,add_assoc] using hi
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentVarCodex
lemma worst_case_var_le {d : ℕ} (R Γ₁ Γ₂ : ℝ) (μ : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (hε0 : 0<ε) (hε1 : ε<1)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ DataDrivenRO.Moment.PCS R Γ₁ Γ₂ μ S) (v : Fin d → ℝ) :
    DataDrivenRO.Moment.VaR P ε v ≤ DataDrivenRO.Moment.csValue μ S Γ₁ Γ₂ ε v := by
  let := hP.1
  have hc := pcs_coords_memLp R Γ₁ Γ₂ μ S P hP
  have hv := pcs_variance_le R Γ₁ Γ₂ μ S P hP v
  let V := v ⬝ᵥ ((S+Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))*ᵥv)
  have hV : 0 ≤ V := (integral_nonneg (fun u => sq_nonneg (u ⬝ᵥ v-(∫ u,u ⬝ᵥ v ∂P)))).trans hv
  have hs : (∫ u,(u ⬝ᵥ v-(∫ u,u ⬝ᵥ v ∂P))^2 ∂P) ≤ (Real.sqrt V)^2 := by
    rw [Real.sq_sqrt hV]
    exact hv
  have hq := quantile_variance_bound P (fun u => u ⬝ᵥ v) (by fun_prop)
    (scalar_memLp P hc v) (Real.sqrt V) ε (-(R*DataDrivenRO.Moment.enorm v))
    (Real.sqrt_nonneg _) hs hε0 hε1 (pcs_scalar_lower R Γ₁ Γ₂ μ S P hP v)
  rw [scalar_mean P hc v] at hq
  have hm := pcs_mean_le R Γ₁ Γ₂ μ S P hP v
  change DataDrivenRO.Moment.VaR P ε v ≤
    μ ⬝ᵥ v+Γ₁*DataDrivenRO.Moment.enorm v+Real.sqrt ((1-ε)/ε)*Real.sqrt V
  exact hq.trans (add_le_add hm (le_refl _))
end MomentVarCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix DataDrivenRO.Moment
theorem solution {d : ℕ} (R Γ₁ Γ₂ : ℝ)
    (μhat : Fin d → ℝ) (Shat : Matrix (Fin d) (Fin d) ℝ)
    (hR : 0 ≤ R) (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ P ∈ PCS R Γ₁ Γ₂ μhat Shat, ∀ v : Fin d → ℝ,
      VaR P ε v ≤ csValue μhat Shat Γ₁ Γ₂ ε v  := by
  intro P hP v
  exact MomentVarCodex.worst_case_var_le R Γ₁ Γ₂ μhat Shat ε hε0 hε1 P hP v


end

#print axioms solution
