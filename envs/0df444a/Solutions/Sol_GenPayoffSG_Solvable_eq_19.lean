-- Prove2me | solution 1 for GenPayoffSG.Solvable.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:36:51.438267+00:00
-- url     : https://prove2.me/submissions/7f5c04a7-600c-4adf-9dcb-bc513ca13fd5

import Mathlib
import Definitions.Def_GenPayoffSG_Solvable_Game

open MeasureTheory ProbabilityTheory Filter Topology GenPayoffSG.Solvable

set_option linter.unusedSectionVars false

namespace GPSGEq19

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

lemma pi_le_iSup_piLE :
    (MeasurableSpace.pi : MeasurableSpace (Run I S A)) ≤ ⨆ n, Filtration.piLE (X := Coord I S A) n := by
  refine iSup_le fun a => ?_
  refine le_iSup_of_le a ?_
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have : (fun b : Run I S A => b a) =
      (fun x : (∀ k : Finset.Iic a, Coord I S A k) => x ⟨a, Finset.mem_Iic.2 le_rfl⟩) ∘
        Preorder.frestrictLe a := by
    funext b; rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (measurable_pi_apply (⟨a, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic a)).comap_le

/-- Under `stepPMF`, the next state has positive transition probability. -/
lemma stepPMF_bad_zero (G : Game I S A) (σ : Profile G) (k : ℕ) (h : Hist I S A k) :
    (stepPMF G σ k h).toMeasure
      {c | G.p (lastState h) (coordAction c) (coordState (k + 1) c) = 0} = 0 := by
  rw [(stepPMF G σ k h).toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete]
  rw [Set.disjoint_left]
  intro c hc hbad
  unfold stepPMF at hc
  rw [PMF.mem_support_bind_iff] at hc
  obtain ⟨a, _, hc⟩ := hc
  rw [PMF.mem_support_map_iff] at hc
  obtain ⟨s', hs', rfl⟩ := hc
  exact hs' hbad

/-- Almost surely every transition along the run has positive probability. -/
lemma ae_trans_pos (G : Game I S A) (σ : Profile G) (s : S) (k : ℕ) :
    ∀ᵐ r ∂(playMeasure G σ 0 (initHist s)),
      0 < G.p (coordState k (r k)) (coordAction (r (k + 1))) (coordState (k + 1) (r (k + 1))) := by
  set μ := playMeasure G σ 0 (initHist s)
  let φ : Run I S A → Hist I S A k × Coord I S A (k + 1) :=
    fun x => (Preorder.frestrictLe k x, x (k + 1))
  let E : Set (Hist I S A k × Coord I S A (k + 1)) :=
    {p | G.p (lastState p.1) (coordAction p.2) (coordState (k + 1) p.2) = 0}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hφ : Measurable φ := by fun_prop
  have hmap : μ.map φ = (Kernel.partialTraj (stepKernel G σ) 0 k (initHist s)) ⊗ₘ
      (stepKernel G σ k) :=
    (Kernel.partialTraj_compProd_eq_map_traj (κ := stepKernel G σ) (Nat.zero_le k)).symm
  have h0 : μ (φ ⁻¹' E) = 0 := by
    rw [← Measure.map_apply hφ hE, hmap, Measure.compProd_apply hE]
    have : ∀ h : Hist I S A k, stepKernel G σ k h (Prod.mk h ⁻¹' E) = 0 := fun h =>
      stepPMF_bad_zero G σ k h
    simp [this]
  rw [ae_iff]
  refine le_antisymm (le_of_le_of_eq (measure_mono ?_) h0) zero_le
  intro r hr
  simp only [Set.mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at hr
  exact hr

lemma ae_feasible (G : Game I S A) (σ : Profile G) (s : S) :
    ∀ᵐ r ∂(playMeasure G σ 0 (initHist s)), ∀ n, Feasible G (Preorder.frestrictLe n r) := by
  have := ae_all_iff.2 (ae_trans_pos G σ s)
  filter_upwards [this] with r hr n k hk
  exact hr k

lemma ae_cyl_pos (G : Game I S A) (σ : Profile G) (s : S) :
    ∀ᵐ r ∂(playMeasure G σ 0 (initHist s)), ∀ n,
      0 < playMeasure G σ 0 (initHist s) (cylinder (Preorder.frestrictLe n r)) := by
  refine ae_all_iff.2 fun n => ?_
  set μ := playMeasure G σ 0 (initHist s)
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ h : {h : Hist I S A n // μ (cylinder h) = 0}, cylinder h.1)
  · intro r hr
    simp only [Set.mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at hr
    exact Set.mem_iUnion.2 ⟨⟨Preorder.frestrictLe n r, hr⟩, rfl⟩
  · exact measure_iUnion_null fun h => h.2

end GPSGEq19

open GPSGEq19

theorem solution {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
  (G : Game I S A) (σ : Profile G) (s : S) (B : Set (Run I S A))
    (hB : MeasurableSet B) (hpos : 0 < playMeasure G σ 0 (initHist s) B)
    (δ : ℝ) (hδ : 0 < δ) (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ ∃ h : Hist I S A n, Feasible G h ∧
      0 < playMeasure G σ 0 (initHist s) (cylinder h) ∧
      1 - δ < (playMeasure G σ n h B).toReal := by
  set μ := playMeasure G σ 0 (initHist s) with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; unfold playMeasure; infer_instance
  set g : Run I S A → ℝ := B.indicator 1 with hg
  have hgm : Measurable g := measurable_one.indicator hB
  have hint : Integrable g μ := (integrable_const (1 : ℝ)).indicator hB
  have hce : ∀ n, μ[g | Filtration.piLE n] =ᵐ[μ]
      fun r => (playMeasure G σ n (Preorder.frestrictLe n r) B).toReal := by
    intro n
    refine (Kernel.condExp_traj (κ := stepKernel G σ) (Nat.zero_le n) hint).trans ?_
    refine ae_of_all _ fun r => ?_
    simp only [hg]
    rw [integral_indicator_one hB]
    rfl
  have hmeas : StronglyMeasurable[⨆ n, Filtration.piLE (X := Coord I S A) n] g :=
    (hgm.mono pi_le_iSup_piLE le_rfl).stronglyMeasurable
  have ht := hint.tendsto_ae_condExp hmeas
  have hall := ae_all_iff.2 hce
  have hgood : ∀ᵐ r ∂μ, (∀ n, Feasible G (Preorder.frestrictLe n r)) ∧
      (∀ n, 0 < μ (cylinder (Preorder.frestrictLe n r))) ∧
      Tendsto (fun n => (playMeasure G σ n (Preorder.frestrictLe n r) B).toReal) atTop
        (𝓝 (g r)) := by
    filter_upwards [ae_feasible G σ s, ae_cyl_pos G σ s, ht, hall] with r h1 h2 h3 h4
    exact ⟨h1, h2, h3.congr h4⟩
  obtain ⟨r, hrB, h1, h2, h3⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae hgood)
  have hgr : g r = 1 := by simp [hg, hrB]
  rw [hgr] at h3
  obtain ⟨N, hN⟩ := ((tendsto_order.1 h3).1 (1 - δ) (by linarith)).exists_forall_of_atTop
  exact ⟨max n₀ N, le_max_left _ _, _, h1 _, h2 _, hN _ (le_max_right _ _)⟩
