-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_35
-- status  : ACCEPTED   (disprove)
-- author  : @I am wealthy
-- created : 2026-11-21T15:01:29.798956+00:00
-- url     : https://prove2.me/submissions/c77ece00-d938-42bf-9006-5ff1e6861348

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

set_option autoImplicit false

section
-- Source module: Solutions.GaussLocalMaxLemma35Counterexample

set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main GaussLocalMaxColoring.Main
open Classical

namespace GaussLocalMaxColoring.Lemma35Counterexample
noncomputable section

def lowBand : Ival := ⟨-(1/2),0,true,false⟩
def midBand : Ival := ⟨0,1/2,true,false⟩
def topBand : Ival := ⟨1/2,1,true,true⟩
def partition : Finset Ival := {lowBand,midBand,topBand}
def graph : SimpleGraph (Fin 2) := ⊥
def vectors (i : Fin 2) : Space 2 := EuclideanSpace.single i 1
def error : ℝ := epsSDP 2
def threshold : ℝ := error/100
def mass : ℝ := 1/3-error/2

theorem error_pos : 0 < error := Real.exp_pos _
theorem error_le : error ≤ (1/7:ℝ) := by
  have hp := Real.add_one_le_exp (6:ℝ)
  have he : error*Real.exp 6=1 := by
    unfold error epsSDP
    norm_num only [Nat.cast_ofNat]
    rw [← Real.exp_add]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hp error_pos.le
  nlinarith only [he,hm]
theorem mass_nonneg : 0 ≤ mass := by unfold mass; linarith [error_le]
theorem mass_le_one : mass ≤ 1 := by unfold mass; linarith [error_pos]
theorem threshold_pos : 0 < threshold := div_pos error_pos (by norm_num)
theorem threshold_le : threshold ≤ (1/30:ℝ) := by unfold threshold; linarith [error_le]

theorem low_toSet : lowBand.toSet=Set.Ico (-(1/2):ℝ) 0 := by rfl
theorem mid_toSet : midBand.toSet=Set.Ico (0:ℝ) (1/2) := by rfl
theorem top_toSet : topBand.toSet=Set.Icc (1/2:ℝ) 1 := by rfl
theorem low_not_positive : ¬ lowBand.Positive := by
  intro h
  have hx : (-(1/4):ℝ) ∈ lowBand.toSet := by norm_num [low_toSet]
  have hx0 := (h hx).1
  norm_num at hx0
theorem mid_positive : midBand.Positive := by
  intro x hx
  rw [mid_toSet] at hx
  exact ⟨hx.1,by linarith [hx.2]⟩
theorem top_positive : topBand.Positive := by
  intro x hx
  rw [top_toSet] at hx
  exact ⟨by linarith [hx.1],hx.2⟩
theorem mid_rho : midBand.rhoP=0 := by
  rw [Ival.rhoP,if_pos mid_positive,mid_toSet]
  exact csInf_Ico (by norm_num)
theorem top_rho : topBand.rhoP=(1/2:ℝ) := by
  rw [Ival.rhoP,if_pos top_positive,top_toSet]
  exact csInf_Icc (by norm_num)

theorem partition_valid : IsBandPartition 2 partition := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog1 : Real.log (2:ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    linarith
  have hwidth : (1/2:ℝ) ≤ 1/Real.log 2 := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith only [hlog1]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro P hP
    simp only [partition,Finset.mem_insert,Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · exact ⟨-(1/4),by norm_num [low_toSet]⟩
    · exact ⟨1/4,by norm_num [mid_toSet]⟩
    · exact ⟨3/4,by norm_num [top_toSet]⟩
  · intro P hP Q hQ hne
    simp only [partition,Finset.mem_insert,Finset.mem_singleton] at hP hQ
    rcases hP with rfl | rfl | rfl <;> rcases hQ with rfl | rfl | rfl
    all_goals try exact (hne rfl).elim
    all_goals
      rw [Set.disjoint_left]
      intro x hx hy
      simp only [low_toSet,mid_toSet,top_toSet,Set.mem_Ico,Set.mem_Icc] at hx hy
      linarith
  · ext x
    simp only [Set.mem_iUnion,partition,Finset.mem_insert,Finset.mem_singleton,
      exists_prop,Set.mem_Icc]
    constructor
    · rintro ⟨P,hP,hx⟩
      rcases hP with rfl | rfl | rfl
      all_goals
        simp only [low_toSet,mid_toSet,top_toSet,Set.mem_Ico,Set.mem_Icc] at hx
        constructor <;> linarith
    · intro hx
      by_cases hx0 : x < 0
      · exact ⟨lowBand,Or.inl rfl,by rw [low_toSet]; exact ⟨hx.1,hx0⟩⟩
      by_cases hxhalf : x < (1/2:ℝ)
      · exact ⟨midBand,Or.inr (Or.inl rfl),by rw [mid_toSet]; exact ⟨by linarith,hxhalf⟩⟩
      · exact ⟨topBand,Or.inr (Or.inr rfl),by rw [top_toSet]; exact ⟨by linarith,hx.2⟩⟩
  · intro P hP
    simp only [partition,Finset.mem_insert,Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    all_goals norm_num only [lowBand,midBand,topBand,Nat.cast_ofNat] <;> linarith [hwidth]
  · intro P hP
    simp only [partition,Finset.mem_insert,Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · left
      intro x hx
      rw [low_toSet] at hx
      exact ⟨hx.1,hx.2.le⟩
    · exact Or.inr mid_positive
    · exact Or.inr top_positive

def e0 : Space 2 := EuclideanSpace.single (0:Fin 2) 1
def e1 : Space 2 := EuclideanSpace.single (1:Fin 2) 1
def shortVector : Space 2 := mass • e0+Real.sqrt (mass-mass^2) • e1
def witnessVector (P : Ival) : Space 2 := if P=midBand then shortVector else e0
def witnesses (_ : Fin 2) (P : Ival) : WIdx 2 → Space 2
  | none => e0
  | some (_,c) => if c=0 then witnessVector P else 0

theorem inner_e0_e0 : ⟪e0,e0⟫=(1:ℝ) := by simp [e0,EuclideanSpace.inner_single_left]
theorem inner_e1_e1 : ⟪e1,e1⟫=(1:ℝ) := by simp [e1,EuclideanSpace.inner_single_left]
theorem inner_e0_e1 : ⟪e0,e1⟫=(0:ℝ) := by simp [e0,e1,EuclideanSpace.inner_single_left]
theorem inner_e1_e0 : ⟪e1,e0⟫=(0:ℝ) := by simp [e0,e1,EuclideanSpace.inner_single_left]

theorem inner_e0_short : ⟪e0,shortVector⟫=mass := by
  simp only [shortVector,inner_add_right,inner_smul_right,inner_e0_e0,inner_e0_e1,
    mul_one,mul_zero,add_zero]
theorem inner_short_short : ⟪shortVector,shortVector⟫=mass := by
  have hbase : 0 ≤ mass-mass^2 := by
    have h := mul_nonneg mass_nonneg (sub_nonneg.mpr mass_le_one)
    nlinarith only [h]
  simp only [shortVector,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    inner_e0_e0,inner_e0_e1,inner_e1_e0,inner_e1_e1,
    zero_mul,mul_zero,add_zero,zero_add,mul_one]
  nlinarith [Real.sq_sqrt hbase]

theorem inner_witness_eq (P : Ival) :
    ⟪e0,witnessVector P⟫=⟪witnessVector P,witnessVector P⟫ := by
  by_cases h : P=midBand
  · simp only [witnessVector,if_pos h,inner_e0_short,inner_short_short]
  · simp only [witnessVector,if_neg h]

theorem theta_feasible (r : Fin 2) (P : Ival) (S : Finset (Fin 2)) (m : ℕ) :
    ThetaFeasible graph S m (gram (witnesses r P)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact inner_e0_e0
  · intro i hi c hc
    fin_cases c
    · change ⟪e0,witnessVector P⟫=⟪witnessVector P,witnessVector P⟫
      exact inner_witness_eq P
    · simp [gram,witnesses]
  · intro i hi c c' hc hc' hne
    fin_cases c <;> fin_cases c'
    all_goals try exact (hne rfl).elim
    all_goals simp [gram,witnesses]
  · intro i hi j hj hij
    exact (show False from hij).elim
  · intro i hi j hj hij
    exact (show False from hij).elim

theorem gram_vectors (i j : Fin 2) : gram vectors i j=if i=j then 1 else 0 := by
  simp [gram,vectors,EuclideanSpace.inner_single_left,eq_comm]

theorem band_low (r : Fin 2) : band (gram vectors) r lowBand=∅ := by
  ext i
  fin_cases r <;> fin_cases i <;> norm_num [band,gram_vectors,low_toSet]
theorem band_mid (r : Fin 2) : band (gram vectors) r midBand=Finset.univ.erase r := by
  ext i
  fin_cases r <;> fin_cases i <;> norm_num [band,gram_vectors,mid_toSet]
theorem band_top (r : Fin 2) : band (gram vectors) r topBand={r} := by
  ext i
  fin_cases r <;> fin_cases i <;> norm_num [band,gram_vectors,top_toSet]

theorem band_mid_zero : band (gram vectors) (0:Fin 2) midBand={1} := by
  ext i
  fin_cases i <;> norm_num [band,gram_vectors,mid_toSet]
theorem band_mid_one : band (gram vectors) (1:Fin 2) midBand={0} := by
  ext i
  fin_cases i <;> norm_num [band,gram_vectors,mid_toSet]

theorem band_mid_reverse (r : Fin 2) : band (gram vectors) r midBand={r.rev} := by
  ext i
  fin_cases r <;> fin_cases i <;> norm_num [band,gram_vectors,mid_toSet,Fin.rev]
theorem ne_reverse (r : Fin 2) : r ≠ r.rev := by
  fin_cases r <;> decide

theorem top_ne_mid : topBand ≠ midBand := by
  intro h
  have he := congrArg Ival.lo h
  norm_num [topBand,midBand] at he

theorem witness_diag (r : Fin 2) (P : Ival) (i : Fin 2) :
    gram (witnesses r P) (some (i,0)) (some (i,0))=
      if P=midBand then mass else 1 := by
  change ⟪witnessVector P,witnessVector P⟫=_
  by_cases h : P=midBand
  · rw [witnessVector,if_pos h,if_pos h]
    exact inner_short_short
  · rw [witnessVector,if_neg h,if_neg h]
    exact inner_e0_e0

theorem vector_conditions : BVVectorConds graph (gram vectors) (epsSDP 2) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    simp [gram_vectors]
  · intro i j
    by_cases h : i=j <;> norm_num [gram_vectors,h]
  · intro i j hij
    exact (show False from hij).elim
  · intro i j hij
    exact (show False from hij).elim
  · intro i j hij
    exact (show False from hij).elim

theorem witness_conditions : BVWitnessConds graph (gram vectors) partition
    (fun r P => gram (witnesses r P)) (epsSDP 2) := by
  intro r P hP
  simp only [partition,Finset.mem_insert,Finset.mem_singleton] at hP
  rcases hP with rfl | rfl | rfl
  · refine ⟨fun h => (low_not_positive h).elim,?_⟩
    intro _
    refine ⟨theta_feasible _ _ _ _,?_,?_⟩
    · simp only [band_low,Finset.sum_empty]
      change 0-error ≤ 0
      linarith [error_pos]
    · simp only [band_low,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,mul_zero]
      exact le_rfl
  · refine ⟨?_,fun h => (h mid_positive).elim⟩
    intro _
    refine ⟨theta_feasible _ _ _ _,?_,?_⟩
    · simp only [band_mid_reverse,Finset.sum_singleton,witness_diag,if_pos rfl,
        gram_vectors,if_neg (ne_reverse r)]
      change (1+2*0)/3-error ≤ mass
      unfold mass
      linarith [error_pos]
    · simp only [band_mid_reverse,Finset.sum_singleton,Finset.card_singleton,mid_rho,Nat.cast_one,
        gram_vectors,if_neg (ne_reverse r),mul_one]
      exact le_rfl
  · refine ⟨?_,fun h => (h top_positive).elim⟩
    intro _
    refine ⟨theta_feasible _ _ _ _,?_,?_⟩
    · simp only [band_top,Finset.sum_singleton,witness_diag,if_neg top_ne_mid,gram_vectors,if_pos rfl]
      change (1+2*1)/3-error ≤ 1
      linarith [error_pos]
    · simp only [band_top,Finset.sum_singleton,Finset.card_singleton,top_rho,Nat.cast_one,gram_vectors,if_pos rfl]
      norm_num

theorem bv_guarantee : BVGuarantee graph partition vectors witnesses :=
  ⟨vector_conditions,witness_conditions⟩

theorem graph_colorable : graph.Colorable 3 := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ : Fin 2 => (0:Fin 3)) ?_⟩
  intro i j hij
  exact (show False from hij).elim

theorem graph_degree : (maxDegOn graph Finset.univ:ℝ) ≤ (2:ℝ)^beta5 := by
  have he : maxDegOn graph Finset.univ=0 := by simp [maxDegOn,nbr,graph]
  rw [he]
  norm_num only [Nat.cast_zero]
  positivity

theorem mid_prime_empty (r : Fin 2) :
    sPrimePos (band (gram vectors) r midBand) (gram (witnesses r midBand))
      (tauPos midBand threshold)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have ht := (Finset.mem_filter.mp hi).2
  rw [witness_diag,if_pos rfl] at ht
  unfold tauPos at ht
  rw [mid_rho] at ht
  unfold threshold mass at ht
  linarith [error_pos]

end
end GaussLocalMaxColoring.Lemma35Counterexample
end

section
-- Source module: Solutions.Sol_GaussLocalMaxLemma35Disprove
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Lemma35Counterexample
open Classical

theorem solution : ¬ (
    ∃ K : ℝ, 0 < K ∧
      ∀ εthr h : ℝ, 0 < εthr → εthr ≤ 1 / 30 → 0 < h → h ≤ 1 / 8 → (∃ N : ℕ, h * N = 1) →
      ∀ g : ℝ → ℝ → ℕ → ℝ, (∀ k b, IsLittleO1 (g k b)) →
      ∃ g' : ℕ → ℝ, IsLittleO1 g' ∧
      ∀ (n d d' : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
        (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
        ∀ (Pt : Finset Ival), IsBandPartition n Pt →
        ∀ (v : Fin n → Space d) (W : Fin n → Ival → WIdx n → Space d'), BVGuarantee G Pt v W →
        ∀ (r : Fin n) (P : Ival), P ∈ Pt →
          let S := band (gram v) r P
          let Y := gram (W r P)
          ((εthr / 2 * S.card : ℝ) ≤
              ((if P.Positive then sPrimePos S Y (tauPos P εthr)
                else sPrimeNeg S Y (tauNeg P εthr)).card : ℝ)) ∧
          (P.Positive → P.rhoP ≤ 1 / 4 →
            let S' := sPrimePos S Y (tauPos P εthr)
            let S'' := S' \ isolatedIn G S'
            let τ := tauPos P εthr
            ∀ βp : ℝ, 0 < βp → βp ≤ 1 → (maxDegOn G S'' : ℝ) ≤ (S''.card : ℝ) ^ βp →
            ∀ I' : Finset (Fin n), VCMeets g h (1 / τ) G S'' I' →
              IsIndep G (isolatedIn G S' ∪ I') ∧
              (εthr * S.card) ^ (2 * τ * (1 + βp) / (2 * τ + βp) - K * h - g' S.card) ≤
                ((isolatedIn G S' ∪ I').card : ℝ)) ∧
          (P.Positive → 1 / 4 < P.rhoP →
            Edgeless G S ∧
              isolatedIn G (sPrimePos S Y (tauPos P εthr)) = sPrimePos S Y (tauPos P εthr)) ∧
          (¬ P.Positive →
            let S' := sPrimeNeg S Y (tauNeg P εthr)
            let τ := tauNeg P εthr
            ∀ βm : ℝ, 0 < βm → βm ≤ 1 → (maxDegOn G S' : ℝ) ≤ (S'.card : ℝ) ^ βm →
            ∀ I' : Finset (Fin n), VCMeets g h ((3 * τ - 1) / (2 * τ - 1)) G S' I' →
              IsIndep G I' ∧
              (εthr * S.card) ^
                  (2 * (1 + βm) * (2 * τ - 1) / ((4 + 3 * βm) * τ - (2 + βm)) - K * h - g' S.card) ≤
                (I'.card : ℝ))) := by
  intro h
  obtain ⟨K,hK,hall⟩ := h
  have hg : ∀ k b : ℝ, IsLittleO1 (fun _ : ℕ => (0:ℝ)) := by
    intro k b
    exact tendsto_const_nhds
  obtain ⟨g',hg',hb⟩ := hall threshold (1/8) threshold_pos threshold_le
    (by norm_num) (by norm_num) ⟨8,by norm_num⟩ (fun _ _ _ => 0) hg
  have hf := (hb 2 2 2 graph graph_colorable (by simpa using graph_degree)
    partition partition_valid vectors witnesses bv_guarantee (0:Fin 2) midBand
    (by simp [partition])).1
  change threshold/2*(band (gram vectors) (0:Fin 2) midBand).card ≤
    ((if midBand.Positive then
      sPrimePos (band (gram vectors) (0:Fin 2) midBand) (gram (witnesses (0:Fin 2) midBand))
        (tauPos midBand threshold)
      else sPrimeNeg (band (gram vectors) (0:Fin 2) midBand) (gram (witnesses (0:Fin 2) midBand))
        (tauNeg midBand threshold)).card:ℝ) at hf
  rw [if_pos mid_positive,mid_prime_empty,band_mid_zero] at hf
  norm_num only [Finset.card_empty,Finset.card_singleton,Nat.cast_zero,Nat.cast_one,mul_one] at hf
  linarith [threshold_pos]
end

#print axioms solution
