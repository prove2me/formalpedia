-- Prove2me | solution 1 for FKZAvg.WStar.corollary_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:07:32.485488+00:00
-- url     : https://prove2.me/submissions/745defe1-89f7-4f6d-8555-b33cfbb01fee

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt
open FKZAvg.WStar

open Classical in
noncomputable def g70op_M : Model ℝ ℝ where
  toMDP := { lower := 0, cost := fun x _ => if x = 0 then 0 else 1,
             q := ProbabilityTheory.Kernel.const _ (Measure.dirac 0) }
  lower_eq := rfl
  Aset := fun _ => Set.univ
  Aset_nonempty := fun _ => ⟨0, trivial⟩
  graph_meas := by simp
  cost_meas := by
    apply Measurable.ite _ measurable_const measurable_const
    exact measurable_fst (measurableSet_singleton 0)

open FeinbergLiang.ACOE in
instance g70op_initP (π : Policy ℝ ℝ) (x : ℝ) : IsProbabilityMeasure (initMeasure π x) := by
  unfold initMeasure; exact Measure.isProbabilityMeasure_map (by fun_prop)

open FeinbergLiang.ACOE in
theorem g70op_succ (π : Policy ℝ ℝ) (x : ℝ) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure g70op_M.toMDP π x), (ω (t+1)).1 = 0 := by
  rw [ae_iff]
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≠ 0} :=
    (measurableSet_singleton (0:ℝ)).compl.preimage measurable_fst
  have h1 : {ω : ℕ → ℝ × ℝ | ¬ (ω (t+1)).1 = 0} =
      (fun ω => (Preorder.frestrictLe t ω, ω (t+1))) ⁻¹' (Set.univ ×ˢ {p : ℝ × ℝ | p.1 ≠ 0}) := by
    ext ω; simp
  rw [h1, ← Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hS)]
  unfold pathMeasure
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.compProd_apply (MeasurableSet.univ.prod hS)]
  have : IsMarkovKernel (g70op_M.toMDP.q.comap (lastPair (X := ℝ) (A := ℝ) t)
      (measurable_pi_apply _)) := Kernel.IsMarkovKernel.comap _ _
  have hf : (stepKernel g70op_M.toMDP π t).fst =
      g70op_M.toMDP.q.comap (lastPair t) (measurable_pi_apply _) := Kernel.fst_compProd _ _
  have hz : ∀ h : (Π _ : Finset.Iic t, ℝ × ℝ), (stepKernel g70op_M.toMDP π t h)
      {p : ℝ × ℝ | ¬ p.1 = 0} = 0 := by
    intro h
    have e := Kernel.fst_apply' (stepKernel g70op_M.toMDP π t) h
      ((measurableSet_singleton (0:ℝ)).compl)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at e
    rw [← e, hf]
    change (g70op_M.toMDP.q (lastPair t h)) {0}ᶜ = 0
    simp [g70op_M]
  have e2 : ∀ h : (Π _ : Finset.Iic t, ℝ × ℝ),
      Prod.mk h ⁻¹' (Set.univ ×ˢ {p : ℝ × ℝ | p.1 ≠ 0}) = {p : ℝ × ℝ | ¬ p.1 = 0} := by
    intro h; ext p; simp
  simp only [e2, hz, lintegral_zero]

open FeinbergLiang.ACOE in
theorem g70op_zero (π : Policy ℝ ℝ) (x : ℝ) :
    ∀ᵐ ω ∂(pathMeasure g70op_M.toMDP π x), (ω 0).1 = x := by
  rw [ae_iff]
  have hS' : MeasurableSet {y : (Π _ : Finset.Iic 0, ℝ × ℝ) | ¬ (y ⟨0, by simp⟩).1 = x} :=
    ((measurableSet_singleton x).compl.preimage measurable_fst).preimage (measurable_pi_apply _)
  have h1 : {ω : ℕ → ℝ × ℝ | ¬ (ω 0).1 = x} =
      Preorder.frestrictLe 0 ⁻¹' {y : (Π _ : Finset.Iic 0, ℝ × ℝ) | ¬ (y ⟨0, by simp⟩).1 = x} := by
    ext ω; simp
  unfold pathMeasure Kernel.trajMeasure
  rw [h1, Measure.bind_apply (hS'.preimage (by fun_prop)) (Kernel.aemeasurable _)]
  have hz : ∀ x₀ : (Π _ : Finset.Iic 0, ℝ × ℝ), (Kernel.traj (stepKernel g70op_M.toMDP π) 0 x₀)
      (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × ℝ) 0 ⁻¹'
      {y : (Π _ : Finset.Iic 0, ℝ × ℝ) | ¬ (y ⟨0, by simp⟩).1 = x}) =
      {y : (Π _ : Finset.Iic 0, ℝ × ℝ) | ¬ (y ⟨0, by simp⟩).1 = x}.indicator 1 x₀ := by
    intro x₀
    rw [← Measure.map_apply (by fun_prop) hS', ← Kernel.map_apply _ (by fun_prop),
      Kernel.traj_map_frestrictLe_of_le (le_refl 0), Kernel.deterministic_apply,
      Measure.dirac_apply' _ hS']
    rfl
  simp_rw [hz]
  rw [lintegral_indicator_one hS', Measure.map_apply (by fun_prop) hS']
  unfold initMeasure
  rw [Measure.map_apply (by fun_prop) (hS'.preimage (by fun_prop))]
  convert measure_empty (μ := π.rule 0 (fun j => j.elim0, x))
  ext a; simp [MeasurableEquiv.piUnique]

open FeinbergLiang.ACOE in
instance g70op_pathP (π : Policy ℝ ℝ) (x : ℝ) :
    IsProbabilityMeasure (pathMeasure g70op_M.toMDP π x) := by
  unfold pathMeasure; infer_instance

open FeinbergLiang.ACOE in
theorem g70op_ae_cost (π : Policy ℝ ℝ) (x : ℝ) :
    ∀ᵐ ω ∂(pathMeasure g70op_M.toMDP π x), ∀ t, g70op_M.toMDP.cost (ω t).1 (ω t).2 =
      if t = 0 then g70op_M.toMDP.cost x 0 else 0 := by
  rw [ae_all_iff]; intro t
  cases t with
  | zero => filter_upwards [g70op_zero π x] with ω h; simp [g70op_M, h]
  | succ t => filter_upwards [g70op_succ π x t] with ω h; simp [g70op_M, h]

open FeinbergLiang.ACOE in
theorem g70op_vDisc (π : Policy ℝ ℝ) (α x : ℝ) :
    vDisc g70op_M.toMDP π α x = g70op_M.toMDP.cost x 0 := by
  unfold vDisc
  rw [lintegral_congr_ae (g := fun _ => g70op_M.toMDP.cost x 0)]
  · simp
  · filter_upwards [g70op_ae_cost π x] with ω h
    simp_rw [h]
    rw [tsum_eq_single 0 (by intro t ht; simp [ht])]
    simp

open FeinbergLiang.ACOE in
theorem g70op_vN0 (π : Policy ℝ ℝ) (N : ℕ) :
    vN g70op_M.toMDP π N 1 0 = 0 := by
  unfold vN
  rw [lintegral_congr_ae (g := fun _ => 0)]
  · simp
  · filter_upwards [g70op_ae_cost π 0] with ω h
    simp_rw [h]
    simp [g70op_M]

theorem g70op_adm (π : FeinbergLiang.ACOE.Policy ℝ ℝ) : Admissible g70op_M π := by
  intro t h; simp [g70op_M]

noncomputable def g70op_pol : FeinbergLiang.ACOE.Policy ℝ ℝ :=
  FeinbergLiang.ACOE.Policy.ofStationary (fun _ : ℝ => (0:ℝ)) measurable_const

theorem g70op_vβ (α x : ℝ) : vβ g70op_M α x = g70op_M.toMDP.cost x 0 := by
  unfold vβ Jbeta
  apply le_antisymm
  · exact (iInf_le _ ⟨g70op_pol, g70op_adm _⟩).trans (g70op_vDisc _ _ _).le
  · exact le_iInf fun π => (g70op_vDisc _ _ _).ge

theorem g70op_mβ (α : ℝ) : mβ g70op_M α = 0 := by
  unfold mβ
  refine le_antisymm ((iInf_le _ 0).trans ?_) bot_le
  rw [g70op_vβ]; simp [g70op_M]

theorem g70op_wβ (α x : ℝ) : wβ g70op_M α x = g70op_M.toMDP.cost x 0 := by
  unfold wβ; rw [g70op_vβ, g70op_mβ, tsub_zero]

theorem g70op_hB : CondBLow g70op_M := by
  refine ⟨?_, fun x => ?_⟩
  · unfold GeneralAssumption gStar
    refine lt_of_le_of_lt ((iInf_le _ 0).trans ((iInf_le _ ⟨g70op_pol, g70op_adm _⟩))) ?_
    unfold Phi FeinbergLiang.ACOE.avgCost
    simp only [g70op_vN0, mul_zero]
    simp
  · simp only [g70op_wβ]
    refine lt_of_le_of_lt (Filter.liminf_le_of_frequently_le'
      (x := g70op_M.toMDP.cost x 0) (Frequently.of_forall fun _ => le_rfl)) ?_
    simp only [g70op_M]; split_ifs <;> simp

theorem g70op_UInf0 (β : ℝ) (hβ : β < 1) : FKZAvg.WStar.UInf g70op_M β 0 = 0 := by
  unfold UInf; simp only [g70op_wβ]; simp only [g70op_M, if_true]
  exact le_antisymm (iInf₂_le_of_le β ⟨le_rfl, hβ⟩ le_rfl) bot_le

theorem g70op_UInf1 (β y : ℝ) (hy : y ≠ 0) : 1 ≤ FKZAvg.WStar.UInf g70op_M β y := by
  unfold UInf; refine le_iInf₂ fun α _ => ?_; rw [g70op_wβ]; simp [g70op_M, hy]

theorem g70op_uLow0 (β : ℝ) (hβ : β < 1) : uLow g70op_M β 0 = 0 := by
  unfold uLow
  refine le_antisymm (Filter.liminf_le_of_frequently_le' ?_) bot_le
  rw [Filter.Frequently]
  intro h
  have := mem_of_mem_nhds h
  simp [g70op_UInf0 β hβ] at this

theorem g70op_uLow1 (β y : ℝ) (hy : y ≠ 0) : 1 ≤ uLow g70op_M β y := by
  unfold uLow
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [isOpen_ne.mem_nhds hy] with z hz
  exact g70op_UInf1 β z hz

theorem g70op_seq : FeinbergLiang.ACOE.IsDiscountSeq (fun n : ℕ => 1 - 1 / ((n:ℝ) + 1)) := by
  refine ⟨fun n => ⟨?_, ?_⟩, ?_, ?_⟩
  · have : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    linarith
  · have : 0 < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  · intro a b hab
    have : 1 / ((b:ℝ) + 1) ≤ 1 / ((a:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    simp only; linarith
  · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1:ℝ)
    simpa using this

theorem solution : ¬ (∀ {X A : Type}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M) (hB : CondBLow M)
    (αs : ℕ → ℝ) (hαs : FeinbergLiang.ACOE.IsDiscountSeq αs) (x : X),
    Monotone (fun n => uLow M (αs n) x) ∧
    Tendsto (fun n => uLow M (αs n) x) atTop (𝓝 (uAvg M x)) ∧
    Tendsto (fun p : ℕ × X => uLow M (αs p.1) p.2) (atTop ×ˢ 𝓝 x) (𝓝 (uAvg M x))) := by
  intro H
  have hsel : HasSelector g70op_M := ⟨fun _ => 0, measurable_const, fun _ => trivial⟩
  have h3 := (H g70op_M hsel g70op_hB _ g70op_seq 0).2.2
  set L := uAvg g70op_M 0
  set αs := fun n : ℕ => 1 - 1 / ((n:ℝ) + 1)
  have hA : Tendsto (fun n : ℕ => ((n, (0:ℝ)) : ℕ × ℝ)) atTop (atTop ×ˢ 𝓝 0) :=
    tendsto_id.prodMk tendsto_const_nhds
  have hB' : Tendsto (fun n : ℕ => ((n, 1 / ((n:ℝ) + 1)) : ℕ × ℝ)) atTop (atTop ×ˢ 𝓝 0) :=
    tendsto_id.prodMk tendsto_one_div_add_atTop_nhds_zero_nat
  have e1 := h3.comp hA
  have e2 := h3.comp hB'
  have hL0 : L = 0 := by
    refine tendsto_nhds_unique e1 ?_
    simp only [Function.comp_def, g70op_uLow0 _ (g70op_seq.1 _).2]
    exact tendsto_const_nhds
  have hL1 : 1 ≤ L := by
    refine ge_of_tendsto e2 (Eventually.of_forall fun n => ?_)
    exact g70op_uLow1 _ _ (by positivity)
  rw [hL0] at hL1
  exact absurd hL1 (by simp)
