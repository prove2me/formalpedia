-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T16:13:46.807751+00:00
-- url     : https://prove2.me/submissions/745bef0d-1e4d-4365-a4ce-b2c551bf88a7

import Definitions.Def_GaussLocalMaxColoring_Main_Iterative


set_option autoImplicit false
set_option maxHeartbeats 6000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem bounded_empirical_deviation {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι→Ω→ℝ) (hI : iIndepFun X μ) (hX : ∀i,Measurable (X i))
    (hB : ∀i ω,X i ω∈Set.Icc 0 1) (p ε : ℝ) (hmean : ∀i,∫ω,X i ω ∂μ=p)
    (hε : 0 ≤ ε) :
    μ.real {ω | ε < |(∑i,X i ω)/(Fintype.card ι:ℝ)-p|} ≤
      2*Real.exp (-2*(Fintype.card ι:ℝ)*ε^2) := by
  let S : Ω→ℝ := fun ω => ∑i,(X i ω-p)
  have hR : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hsub : ∀i,HasSubgaussianMGF (fun ω => X i ω-p) (1/4:NNReal) μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ:=μ) (hX i).aemeasurable
      (Eventually.of_forall (hB i))
    rw [hmean i] at h
    norm_num at h ⊢
    exact h
  have hIc : iIndepFun (fun i ω => X i ω-p) μ := by
    simpa only [Function.comp_def] using
      (hI.comp (fun _ z => z-p) (fun _ => measurable_id.sub_const p))
  have hIn : iIndepFun (fun i ω => -(X i ω-p)) μ := by
    simpa only [Function.comp_def] using
      (hIc.comp (fun _ z => -z) (fun _ => measurable_neg))
  have he : -(ε*(Fintype.card ι:ℝ))^2 /
      (2*∑_i : ι,(1/4:NNReal)) = -2*(Fintype.card ι:ℝ)*ε^2 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,NNReal.coe_mul,
      NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    field_simp
    ring
  have hplus : μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ S ω} ≤
      Real.exp (-2*(Fintype.card ι:ℝ)*ε^2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIc (s:=Finset.univ)
      (fun i _ => hsub i) (mul_nonneg hε hR.le)
    simpa only [S,he] using h
  have hminus : μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω} ≤
      Real.exp (-2*(Fintype.card ι:ℝ)*ε^2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIn (s:=Finset.univ)
      (fun i _ => (hsub i).neg) (mul_nonneg hε hR.le)
    simpa only [S,Finset.sum_neg_distrib,he] using h
  have hS : ∀ω,S ω=(∑i,X i ω)-(Fintype.card ι:ℝ)*p := by
    intro ω
    simp [S,Finset.sum_sub_distrib]
  have hE : {ω | ε < |(∑i,X i ω)/(Fintype.card ι:ℝ)-p|} ⊆
      {ω | ε*(Fintype.card ι:ℝ) ≤ S ω} ∪ {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω} := by
    intro ω hω
    change ε < |(∑i,X i ω)/(Fintype.card ι:ℝ)-p| at hω
    rcases (lt_abs.mp hω) with h|h
    · left
      change ε*(Fintype.card ι:ℝ) ≤ S ω
      rw [hS]
      have hm := (lt_div_iff₀ hR).mp (show ε+p < (∑i,X i ω)/(Fintype.card ι:ℝ) by linarith)
      nlinarith
    · right
      change ε*(Fintype.card ι:ℝ) ≤ -S ω
      rw [hS]
      have hm := (div_lt_iff₀ hR).mp (show (∑i,X i ω)/(Fintype.card ι:ℝ) < p-ε by linarith)
      nlinarith
  calc
    _ ≤ μ.real ({ω | ε*(Fintype.card ι:ℝ) ≤ S ω} ∪
        {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω}) := measureReal_mono hE
    _ ≤ μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ S ω}+
        μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 6000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem measurableSet_localMax_mem {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) :
    MeasurableSet {g : Space d | x∈localMax G v F g} := by
  classical
  apply measurableSet_setOfPred.mpr
  simp only [localMax,Finset.mem_filter]
  apply Measurable.and measurable_const
  apply Measurable.forall
  intro y
  apply Measurable.imp measurable_const
  apply Measurable.or
  · exact measurableSet_setOfPred.mp (measurableSet_lt
      (by fun_prop : Measurable fun g : Space d => ⟪g,v y⟫)
      (by fun_prop : Measurable fun g : Space d => ⟪g,v x⟫))
  · exact (measurableSet_setOfPred.mp (measurableSet_eq_fun
      (by fun_prop : Measurable fun g : Space d => ⟪g,v y⟫)
      (by fun_prop : Measurable fun g : Space d => ⟪g,v x⟫))).and measurable_const

theorem measurable_localMax {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) :
    Measurable (localMax G v F) := by
  rw [measurable_finset_iff]
  intro x
  exact measurableSet_setOfPred.mp (measurableSet_localMax_mem G v F x)

def localIndicator {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) (g : Space d) : ℝ :=
  if x∈localMax G v F g then 1 else 0

theorem localIndicator_measurable {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) :
    Measurable (localIndicator G v F x) := by
  classical
  exact Measurable.ite (measurableSet_localMax_mem G v F x) measurable_const measurable_const

theorem localIndicator_range {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) (g : Space d) :
    localIndicator G v F x g∈Set.Icc 0 1 := by
  classical
  dsimp [localIndicator]
  split_ifs <;> norm_num

theorem localIndicator_mean {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) :
    ∫g,localIndicator G v F x g ∂stdGaussian (Space d)=pLocal G v F x := by
  classical
  simpa only [localIndicator,pLocal,gaussProb,Set.indicator_apply,
    Set.mem_setOf_eq,Pi.one_apply] using
    (integral_indicator_one (μ:=stdGaussian (Space d)) (measurableSet_localMax_mem G v F x))

theorem freq_eq_indicator_sum {n R : ℕ} (I : Fin R→Finset (Fin n)) (x : Fin n) :
    freq I x=(∑i : Fin R,if x∈I i then (1:ℝ) else 0)/R := by
  classical
  rw [freq,Finset.card_filter]
  push_cast
  rfl

theorem fixed_core_deviation {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n)
    (hR : 0 < R) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin R => stdGaussian (Space d)).real
      {ω | ε < |freq (fun i => localMax G v F (ω i)) x-pLocal G v F x|} ≤
      2*Real.exp (-2*R*ε^2) := by
  classical
  letI : Nonempty (Fin R) := Fin.pos_iff_nonempty.mp hR
  let μ : Measure (Fin R→Space d) := Measure.pi fun _ => stdGaussian (Space d)
  let X : Fin R→(Fin R→Space d)→ℝ := fun i ω => localIndicator G v F x (ω i)
  have hI : iIndepFun X μ := iIndepFun_pi (fun _ => (localIndicator_measurable G v F x).aemeasurable)
  have hX : ∀i,Measurable (X i) := fun i =>
    (localIndicator_measurable G v F x).comp (measurable_pi_apply i)
  have hmean : ∀i,∫ω,X i ω ∂μ=pLocal G v F x := by
    intro i
    change (∫ω,localIndicator G v F x (ω i) ∂Measure.pi (fun _ : Fin R => stdGaussian (Space d)))=_
    have hm := measurePreserving_eval (fun _ : Fin R => stdGaussian (Space d)) i
    calc
      _ = ∫g,localIndicator G v F x g ∂
          (Measure.pi (fun _ : Fin R => stdGaussian (Space d))).map (Function.eval i) :=
        (integral_map_of_stronglyMeasurable (measurable_pi_apply i)
          (localIndicator_measurable G v F x).stronglyMeasurable).symm
      _ = ∫g,localIndicator G v F x g ∂stdGaussian (Space d) := by rw [hm.map_eq]
      _ = _ := localIndicator_mean G v F x
  have h := bounded_empirical_deviation μ X hI hX
    (fun i ω => localIndicator_range G v F x (ω i)) (pLocal G v F x) ε hmean hε
  simpa only [freq_eq_indicator_sum,X,localIndicator,Fintype.card_fin] using h

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem measurable_freq {n R : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Fin R→Ω→Finset (Fin n)) (hI : ∀i,Measurable (I i)) (x : Fin n) :
    Measurable (fun ω => freq (fun i => I i ω) x) := by
  classical
  simp only [freq_eq_indicator_sum]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (measurableSet_setOfPred.mpr ((measurable_finset_mem x).comp (hI i)))
    measurable_const measurable_const

theorem measurable_sampledAt_fixed {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (j : ℕ) (i : Fin R) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => sampledAt G v ω F j i) := by
  classical
  unfold sampledAt
  split_ifs with h
  · exact (measurable_localMax G v F).comp
      (measurable_pi_apply ((⟨j,h⟩:Fin (numLevels n)),i))
  · exact measurable_const

theorem measurable_cores {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : ℕ) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => cores G v δ ω j) := by
  classical
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    let U : Finset (Fin n)×(Fin (numLevels n)×Fin R→Space d)→Finset (Fin n) :=
      fun p => p.1.filter (fun x => freq (sampledAt G v p.2 p.1 j) x<δ/2)
    have hU : Measurable U := by
      apply measurable_from_prod_countable_right
      intro F
      rw [measurable_finset_iff]
      intro x
      simp only [U,Finset.mem_filter]
      apply Measurable.and measurable_const
      apply measurableSet_setOfPred.mp
      exact measurableSet_lt
        (measurable_freq (fun i ω => sampledAt G v ω F j i)
          (measurable_sampledAt_fixed G v F j) x) measurable_const
    change Measurable (fun ω : Fin (numLevels n)×Fin R→Space d =>
      U (cores G v δ ω j,ω))
    exact hU.comp (ih.prodMk measurable_id)

theorem cores_congr_before {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω ω' : Fin (numLevels n)×Fin R→Space d)
    (j : ℕ) (hω : ∀p,p.1.val<j → ω p=ω' p) :
    cores G v δ ω j=cores G v δ ω' j := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    have hc := ih (fun p hp => hω p (by omega))
    have hs : sampledAt G v ω (cores G v δ ω' j) j=
        sampledAt G v ω' (cores G v δ ω' j) j := by
      funext i
      unfold sampledAt
      split_ifs with h
      · rw [hω (⟨j,h⟩,i) (by simp)]
      · rfl
    simp only [cores,hc,hs]

def pastIndices (n R j : ℕ) : Finset (Fin (numLevels n)×Fin R) :=
  Finset.univ.filter (fun p => p.1.val<j)

def rowIndices (n R : ℕ) (j : Fin (numLevels n)) : Finset (Fin (numLevels n)×Fin R) :=
  Finset.univ.filter (fun p => p.1=j)

def fillPast {n d R : ℕ} (j : ℕ) (z : ↥(pastIndices n R j)→Space d) :
    Fin (numLevels n)×Fin R→Space d :=
  fun p => if hp : p∈pastIndices n R j then z ⟨p,hp⟩ else 0

theorem fillPast_measurable {n d R : ℕ} (j : ℕ) :
    Measurable (fillPast (n:=n) (d:=d) (R:=R) j) := by
  classical
  apply measurable_pi_iff.mpr
  intro p
  unfold fillPast
  split_ifs with h
  · exact measurable_pi_apply (⟨p,h⟩:↥(pastIndices n R j))
  · exact measurable_const

theorem cores_fillPast {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d) (j : ℕ) :
    cores G v δ (fillPast j (fun p : ↥(pastIndices n R j) => ω p)) j=cores G v δ ω j := by
  classical
  apply cores_congr_before
  intro p hp
  simp [fillPast,pastIndices,hp]

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

instance instIsProbabilityMeasureTrialLaw (n d R : ℕ) : IsProbabilityMeasure (trialLaw n d R) := by
  unfold trialLaw
  infer_instance

theorem cores_independent_row {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : Fin (numLevels n)) :
    IndepFun (fun ω : Fin (numLevels n)×Fin R→Space d => cores G v δ ω j.val)
      (fun ω i => ω (j,i)) (trialLaw n d R) := by
  classical
  have hI : iIndepFun (fun p (ω : Fin (numLevels n)×Fin R→Space d) => ω p)
      (trialLaw n d R) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hST : Disjoint (pastIndices n R j.val) (rowIndices n R j) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [pastIndices,rowIndices,Finset.mem_filter,Finset.mem_univ,true_and] at hp hq
    rw [hq] at hp
    exact (lt_irrefl _ hp)
  have h := iIndepFun.indepFun_finset (pastIndices n R j.val) (rowIndices n R j) hST hI
    (fun p => measurable_pi_apply p)
  let C : (↥(pastIndices n R j.val)→Space d)→Finset (Fin n) :=
    fun z => cores G v δ (fillPast j.val z) j.val
  let Y : (↥(rowIndices n R j)→Space d)→(Fin R→Space d) :=
    fun z i => z ⟨(j,i),by simp [rowIndices]⟩
  have hC : Measurable C := (measurable_cores G v δ j.val).comp (fillPast_measurable j.val)
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hi := h.comp hC hY
  simpa only [C,Y,Function.comp_def,cores_fillPast] using hi

theorem trial_row_map {n d R : ℕ} (j : Fin (numLevels n)) :
    (trialLaw n d R).map (fun ω i => ω (j,i))=
      Measure.pi (fun _ : Fin R => stdGaussian (Space d)) := by
  have hI : iIndepFun (fun p (ω : Fin (numLevels n)×Fin R→Space d) => ω p)
      (trialLaw n d R) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hrow := iIndepFun.precomp (g:=fun i : Fin R => (j,i))
    (fun a b h => (Prod.mk.inj h).2) hI
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (j,i)).aemeasurable) hrow]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin (numLevels n)×Fin R => stdGaussian (Space d)) (j,i)).map_eq

theorem independent_finite_parameter_bound {κ Υ Ω : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [MeasurableSpace Υ] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Υ) [IsProbabilityMeasure ν]
    (F : Ω→κ) (Y : Ω→Υ) (hF : Measurable F) (hY : Measurable Y)
    (hI : IndepFun F Y μ) (hν : μ.map Y=ν)
    (B : ℝ) (E : κ→Set Υ) (hE : ∀k,MeasurableSet (E k)) (hB : ∀k,ν.real (E k)≤B) :
    μ.real {ω | Y ω∈E (F ω)} ≤ B := by
  haveI : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  let A : Set (κ×Υ) := {z | z.2∈E z.1}
  have hA : MeasurableSet A := by
    apply measurableSet_setOfPred.mpr
    apply measurable_from_prod_countable_right
    intro k
    exact measurableSet_setOfPred.mp (hE k)
  let f : κ×Υ→ℝ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  have hfint : Integrable f ((μ.map F).prod ν) := (integrable_const (1:ℝ)).indicator hA
  calc
    μ.real {ω | Y ω∈E (F ω)} = ∫ω,f (F ω,Y ω) ∂μ := by
      simpa [f,A,Set.indicator,Set.preimage] using
        (integral_indicator_one (μ:=μ) (hA.preimage (hF.prodMk hY))).symm
    _ = ∫z,f z ∂μ.map (fun ω => (F ω,Y ω)) :=
      (integral_map (hF.prodMk hY).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫z,f z ∂(μ.map F).prod ν := by
      rw [hI.map_prod_eq_prod_map_map hF.aemeasurable hY.aemeasurable,hν]
    _ = ∫k,∫y,f (k,y) ∂ν ∂μ.map F := integral_prod f hfint
    _ = ∫k,ν.real (E k) ∂μ.map F := by
      apply integral_congr_ae
      filter_upwards [] with k
      simpa [f,A,Set.indicator] using
        (integral_indicator_one (μ:=ν) (hE k))
    _ ≤ ∫_k,B ∂μ.map F := by
      apply integral_mono Integrable.of_finite (integrable_const B)
      intro k
      exact hB k
    _ = B := by simp

theorem adaptive_core_deviation {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : Fin (numLevels n)) (x : Fin n)
    (hR : 0 < R) (ε : ℝ) (hε : 0 ≤ ε) :
    (trialLaw n d R).real {ω |
      ε < |freq (fun i => localMax G v (cores G v δ ω j.val) (ω (j,i))) x-
        pLocal G v (cores G v δ ω j.val) x|} ≤
      2*Real.exp (-2*R*ε^2) := by
  let E : Finset (Fin n)→Set (Fin R→Space d) := fun F =>
    {z | ε < |freq (fun i => localMax G v F (z i)) x-pLocal G v F x|}
  have hE : ∀F,MeasurableSet (E F) := by
    intro F
    have hf : Measurable (fun z : Fin R→Space d => freq (fun i => localMax G v F (z i)) x) :=
      measurable_freq (n:=n) (R:=R) (Ω:=Fin R→Space d)
        (fun (i : Fin R) (z : Fin R→Space d) => localMax G v F (z i))
        (fun i => (measurable_localMax G v F).comp (measurable_pi_apply i)) x
    exact measurableSet_lt measurable_const ((hf.sub_const (pLocal G v F x)).abs)
  exact independent_finite_parameter_bound (trialLaw n d R)
    (Measure.pi fun _ : Fin R => stdGaussian (Space d))
    (fun ω => cores G v δ ω j.val) (fun ω i => ω (j,i))
    (measurable_cores G v δ j.val) (by fun_prop) (cores_independent_row G v δ j)
    (trial_row_map j) _ E hE (fun F => fixed_core_deviation G v F x hR ε hε)

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def concentrationRuns (n : ℕ) (δ : ℝ) : ℕ :=
  ⌈32*δ⁻¹^2*Real.log (8*n*(numLevels n:ℝ))⌉₊

theorem concentrationRuns_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hℓ : 0 < numLevels n) :
    0 < concentrationRuns n δ ∧
      (numLevels n:ℝ)*n*(2*Real.exp (-2*(concentrationRuns n δ:ℝ)*(δ/8)^2)) ≤ 1/4 := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n=0 := by omega
    simp [numLevels,hn0] at hℓ
  have hnr : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hℓr : 1 ≤ (numLevels n:ℝ) := by exact_mod_cast hℓ
  have hA : 0 < 8*(n:ℝ)*(numLevels n:ℝ) := by positivity
  have hA1 : 1 < 8*(n:ℝ)*(numLevels n:ℝ) := by nlinarith
  have hlog : 0 < Real.log (8*(n:ℝ)*(numLevels n:ℝ)) := Real.log_pos hA1
  have hceil : 32*δ⁻¹^2*Real.log (8*(n:ℝ)*(numLevels n:ℝ)) ≤
      (concentrationRuns n δ:ℝ) := Nat.le_ceil _
  have hRp : 0 < (concentrationRuns n δ:ℝ) :=
    lt_of_lt_of_le (by positivity) hceil
  constructor
  · exact_mod_cast hRp
  · have hmul := mul_le_mul_of_nonneg_right hceil (show 0 ≤ δ^2/32 by positivity)
    have heq : (32*δ⁻¹^2*Real.log (8*(n:ℝ)*(numLevels n:ℝ)))*(δ^2/32)=
        Real.log (8*(n:ℝ)*(numLevels n:ℝ)) := by field_simp
    have hmain : Real.log (8*(n:ℝ)*(numLevels n:ℝ)) ≤
        (concentrationRuns n δ:ℝ)*δ^2/32 := by nlinarith [heq]
    calc
      _ = (numLevels n:ℝ)*n*(2*Real.exp (-((concentrationRuns n δ:ℝ)*δ^2/32))) := by
        congr 3
        ring
      _ ≤ (numLevels n:ℝ)*n*(2*Real.exp (-Real.log (8*(n:ℝ)*(numLevels n:ℝ)))) := by
        gcongr
      _ = 1/4 := by
        rw [Real.exp_neg,Real.exp_log hA]
        field_simp
        ring

end
end GaussLocalMaxColoring.Main


set_option autoImplicit false
set_option maxHeartbeats 500000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem measurable_sampleSet {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : ℕ) (i : Fin R) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => sampleSet G v δ ω j i) := by
  classical
  let U : Finset (Fin n)×(Fin (numLevels n)×Fin R→Space d)→Finset (Fin n) :=
    fun p => sampledAt G v p.2 p.1 (j-1) i
  have hU : Measurable U := measurable_from_prod_countable_right
    (fun F => measurable_sampledAt_fixed (R:=R) G v F (j-1) i)
  change Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => U (cores G v δ ω (j-1),ω))
  exact hU.comp ((measurable_cores (R:=R) G v δ (j-1)).prodMk measurable_id)

theorem measurable_phat {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : ℕ) (x : Fin n) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => phat G v δ ω j x) :=
  measurable_freq (n:=n) (R:=R) (Ω:=Fin (numLevels n)×Fin R→Space d)
    (fun (i : Fin R) (ω : Fin (numLevels n)×Fin R→Space d) => sampleSet G v δ ω j i)
    (measurable_sampleSet (R:=R) G v δ j) x

theorem phat_survivor_lt {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d)
    (j : ℕ) (hj : 1 ≤ j) (x : Fin n) (hx : x∈cores G v δ ω j) :
    phat G v δ ω j x<δ/2 := by
  classical
  obtain ⟨k,rfl⟩ : ∃k,j=k+1 := ⟨j-1,by omega⟩
  change freq (sampledAt G v ω (cores G v δ ω k) k) x<δ/2
  exact (Finset.mem_filter.mp hx).2

theorem phat_succ_eq {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d)
    (j : Fin (numLevels n)) (x : Fin n) :
    phat G v δ ω (j.val+1) x=
      freq (fun i => localMax G v (cores G v δ ω j.val) (ω (j,i))) x := by
  classical
  change freq (sampledAt G v ω (cores G v δ ω j.val) j.val) x=_
  congr 1
  funext i
  rw [sampledAt,dif_pos j.isLt]

theorem accurate_survivor_bound (δ b p : ℝ) (hδ : 0 < δ)
    (hb : b<δ/2) (hp : -(δ/8) ≤ b-p) : p<δ := by
  linarith

theorem lemma_21 {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (T : ℕ) :
    (trialLaw n d ⌈32*δ⁻¹^2*Real.log (8*n*(numLevels n:ℝ))⌉₊).real
        {ω | ∀j,1 ≤ j → j ≤ numLevels n → Constructed G v δ T ω j →
          (∀x∈cores G v δ ω (j-1),
            |phat G v δ ω j x-pLocal G v (cores G v δ ω (j-1)) x| ≤ δ/8) ∧
          (∀x∈cores G v δ ω j,pLocal G v (cores G v δ ω (j-1)) x<δ)} ≥ 3/4 := by
  classical
  by_cases hℓ : 0 < numLevels n
  · let R := concentrationRuns n δ
    let μ := trialLaw n d R
    haveI : IsProbabilityMeasure μ := instIsProbabilityMeasureTrialLaw n d R
    have hRate := concentrationRuns_bound n δ hδ0 hℓ
    let Bad : (Fin (numLevels n)×Fin n)→Set (Fin (numLevels n)×Fin R→Space d) :=
      fun p => {ω | δ/8 < |phat G v δ ω (p.1.val+1) p.2-
        pLocal G v (cores G v δ ω p.1.val) p.2|}
    have hBadMeas : ∀p,MeasurableSet (Bad p) := by
      intro p
      have hph : Measurable (fun ω : Fin (numLevels n)×Fin R→Space d =>
          phat G v δ ω (p.1.val+1) p.2) := measurable_phat (R:=R) G v δ (p.1.val+1) p.2
      have hpc : Measurable (fun ω : Fin (numLevels n)×Fin R→Space d =>
          pLocal G v (cores G v δ ω p.1.val) p.2) :=
        (measurable_of_countable (fun F : Finset (Fin n) => pLocal G v F p.2)).comp
          (measurable_cores (R:=R) G v δ p.1.val)
      exact measurableSet_lt measurable_const (hph.sub hpc).abs
    have hBad : ∀p,μ.real (Bad p) ≤ 2*Real.exp (-2*R*(δ/8)^2) := by
      intro p
      have h := adaptive_core_deviation G v δ p.1 p.2 hRate.1 (δ/8) (by positivity)
      simpa only [Bad,phat_succ_eq] using h
    have hU : μ.real (⋃p,Bad p) ≤ 1/4 := by
      calc
        _ ≤ ∑p,μ.real (Bad p) := measureReal_iUnion_fintype_le Bad
        _ ≤ ∑_p : Fin (numLevels n)×Fin n,2*Real.exp (-2*R*(δ/8)^2) :=
          Finset.sum_le_sum (fun p _ => hBad p)
        _ = (numLevels n:ℝ)*n*(2*Real.exp (-2*R*(δ/8)^2)) := by simp [Fintype.card_prod]
        _ ≤ 1/4 := hRate.2
    have hGood : 3/4 ≤ μ.real (⋃p,Bad p)ᶜ := by
      rw [probReal_compl_eq_one_sub (MeasurableSet.iUnion hBadMeas)]
      linarith
    apply hGood.trans
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω j hj1 hjℓ hjC
    have hAcc : ∀x : Fin n,
        |phat G v δ ω j x-pLocal G v (cores G v δ ω (j-1)) x| ≤ δ/8 := by
      intro x
      have hn : ω∉Bad (⟨j-1,by omega⟩,x) := by
        intro h
        exact hω (Set.mem_iUnion.mpr ⟨(⟨j-1,by omega⟩,x),h⟩)
      have hj : j-1+1=j := by omega
      simpa only [Bad,Set.mem_setOf_eq,hj,not_lt] using hn
    constructor
    · exact fun x _ => hAcc x
    · intro x hx
      have hp := phat_survivor_lt G v δ ω j hj1 x hx
      have ha := (abs_le.mp (hAcc x)).1
      exact accurate_survivor_bound δ _ _ hδ0 hp ha
  · have hz : numLevels n=0 := by omega
    have hE : {ω : Fin (numLevels n)×
        Fin ⌈32*δ⁻¹^2*Real.log (8*n*(numLevels n:ℝ))⌉₊→Space d |
        ∀j,1 ≤ j → j ≤ numLevels n → Constructed G v δ T ω j →
          (∀x∈cores G v δ ω (j-1),
            |phat G v δ ω j x-pLocal G v (cores G v δ ω (j-1)) x| ≤ δ/8) ∧
          (∀x∈cores G v δ ω j,pLocal G v (cores G v δ ω (j-1)) x<δ)}=Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
      intro j hj1 hjℓ
      omega
    rw [hE,probReal_univ]
    norm_num

end
end GaussLocalMaxColoring.Main

open GaussLocalMaxColoring.Main
open RecGaussColoring.Main
open MeasureTheory
open ProbabilityTheory
open scoped RealInnerProductSpace

theorem solution {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (T : ℕ) :
    (trialLaw n d ⌈32 * δ⁻¹ ^ 2 * Real.log (8 * n * (numLevels n : ℝ))⌉₊).real
        {ω | ∀ j, 1 ≤ j → j ≤ numLevels n → Constructed G v δ T ω j →
          (∀ x ∈ cores G v δ ω (j - 1),
            |phat G v δ ω j x - pLocal G v (cores G v δ ω (j - 1)) x| ≤ δ / 8) ∧
          (∀ x ∈ cores G v δ ω j, pLocal G v (cores G v δ ω (j - 1)) x < δ)} ≥ 3 / 4  := GaussLocalMaxColoring.Main.lemma_21 G v δ hδ0 hδ1 T
