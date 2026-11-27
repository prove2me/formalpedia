-- Prove2me | solution 1 for CrossLayerControl.ECCA.ecca_drift_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:26:52.593929+00:00
-- url     : https://prove2.me/submissions/3d5db281-a56b-40e3-8297-8271b2e2f737

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_RateHyp
import Definitions.Def_CrossLayerControl_ECCA_DownlinkMeas
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun
import Definitions.Def_CrossLayerControl_ECCA_IsAdaptedIID
import Definitions.Def_CrossLayerControl_ECCA_achievable
import Definitions.Def_CrossLayerControl_ECCA_B
import Theorems.Thm_CrossLayerControl_ECCA_drift_bound

open MeasureTheory ProbabilityTheory Filter CrossLayerControl.ECCA

namespace DriftAux

/-- Comparison with a stationary randomized decision, in abstract form. -/
lemma core {Ω Z E ι : Type*} (G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Z] [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] [Fintype ι]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (hG : G ≤ mΩ)
    (Y : Ω → Z) (hY : Measurable Y)
    (hind : Indep (MeasurableSpace.comap Y inferInstance) G Pr)
    (ν : Measure (Z × E)) [IsProbabilityMeasure ν] (hmarg : ν.map Prod.fst = Pr.map Y)
    (f : ι → Ω → ℝ) (hf : ∀ j, Measurable[G] (f j)) (c : ℝ) (hfb : ∀ j ω, |f j ω| ≤ c)
    (g : ι → Z × E → ℝ) (hg : ∀ j, Measurable (g j)) (hgi : ∀ j, Integrable (g j) ν)
    (good : Z × E → Prop) (hgood : ∀ᵐ x ∂ν, good x)
    (h : Ω → ℝ) (hh : Integrable h Pr)
    (hbound : ∀ ω e, good (Y ω, e) → h ω ≤ ∑ j, f j ω * g j (Y ω, e)) :
    ∫ ω, h ω ∂Pr ≤ ∑ j, (∫ ω, f j ω ∂Pr) * ∫ x, g j x ∂ν := by
  set μ := Pr.map Y with hμ
  set κ := ν.condKernel
  have hdis : μ ⊗ₘ κ = ν := by
    have := ν.disintegrate ν.condKernel
    rw [Measure.fst, hmarg] at this
    exact this
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hY.aemeasurable
  set gb : ι → Z → ℝ := fun j z => ∫ e, g j (z, e) ∂κ z with hgb
  have hgbm : ∀ j, Measurable (gb j) := fun j =>
    ((hg j).stronglyMeasurable.integral_kernel_prod_right').measurable
  have hgi' : ∀ j, Integrable (g j) (μ ⊗ₘ κ) := fun j => by rw [hdis]; exact hgi j
  have hgbi : ∀ j, Integrable (gb j) μ := by
    intro j
    have h2 := ((Measure.integrable_compProd_iff (hgi' j).aestronglyMeasurable).mp (hgi' j)).2
    refine h2.mono (hgbm j).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    calc ‖gb j z‖ ≤ ∫ e, ‖g j (z, e)‖ ∂κ z := norm_integral_le_integral_norm _
      _ ≤ ‖∫ e, ‖g j (z, e)‖ ∂κ z‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
  have hgint : ∀ j, ∫ x, g j x ∂ν = ∫ z, gb j z ∂μ := by
    intro j; rw [← hdis, Measure.integral_compProd (hgi' j)]
  -- a.e. good fibres
  have hae_z : ∀ᵐ z ∂μ, (∀ j, Integrable (fun e => g j (z, e)) (κ z)) ∧
      ∀ᵐ e ∂κ z, good (z, e) := by
    have h1 : ∀ᵐ z ∂μ, ∀ j, Integrable (fun e => g j (z, e)) (κ z) := by
      rw [ae_all_iff]
      intro j
      exact ((Measure.integrable_compProd_iff (hgi' j).aestronglyMeasurable).mp (hgi' j)).1
    have h2 : ∀ᵐ z ∂μ, ∀ᵐ e ∂κ z, good (z, e) := by
      rw [← hdis] at hgood
      exact Measure.ae_ae_of_ae_compProd hgood
    filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩
  have hae_ω := ae_of_ae_map hY.aemeasurable hae_z
  have hfm : ∀ j, Measurable (f j) := fun j => (hf j).mono hG le_rfl
  have hpt : ∀ᵐ ω ∂Pr, h ω ≤ ∑ j, f j ω * gb j (Y ω) := by
    filter_upwards [hae_ω] with ω ⟨hint, hgd⟩
    have hI : Integrable (fun e => ∑ j, f j ω * g j (Y ω, e)) (κ (Y ω)) :=
      integrable_finsetSum _ fun j _ => (hint j).const_mul (f j ω)
    have := integral_mono_ae (integrable_const (h ω)) hI
      (by filter_upwards [hgd] with e he using hbound ω e he)
    rw [integral_const, integral_finsetSum _ (fun j _ => (hint j).const_mul (f j ω))] at this
    simpa [hgb, integral_const_mul] using this
  have hprodi : ∀ j, Integrable (fun ω => f j ω * gb j (Y ω)) Pr := by
    intro j
    have : Integrable (fun ω => gb j (Y ω)) Pr :=
      (integrable_map_measure (hgbm j).aestronglyMeasurable hY.aemeasurable).mp (hgbi j)
    exact this.bdd_mul (hfm j).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfb j ω)
  calc ∫ ω, h ω ∂Pr ≤ ∫ ω, ∑ j, f j ω * gb j (Y ω) ∂Pr :=
        integral_mono_ae hh (integrable_finsetSum _ fun j _ => hprodi j) hpt
    _ = ∑ j, ∫ ω, f j ω * gb j (Y ω) ∂Pr := integral_finsetSum _ fun j _ => hprodi j
    _ = ∑ j, (∫ ω, f j ω ∂Pr) * ∫ x, g j x ∂ν := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hindep : IndepFun (f j) (fun ω => gb j (Y ω)) Pr := by
          rw [IndepFun_iff_Indep]
          refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm ?_) ?_
          · exact (hf j).comap_le
          · rw [show (fun ω => gb j (Y ω)) = gb j ∘ Y from rfl, ← MeasurableSpace.comap_comp]
            exact MeasurableSpace.comap_mono (hgbm j).comap_le
        have := hindep.integral_mul_eq_mul_integral (hfm j).aestronglyMeasurable
          ((hgbm j).comp hY).aestronglyMeasurable
        simp only [Pi.mul_apply] at this
        rw [this, hgint j, hμ, integral_map hY.aemeasurable (hgbm j).aestronglyMeasurable]

/-- bounded measurable real functions -/
def BM {Ω : Type*} [MeasurableSpace Ω] (g : Ω → ℝ) : Prop :=
  Measurable g ∧ ∃ c, ∀ ω, |g ω| ≤ c

lemma BM.const {Ω : Type*} [MeasurableSpace Ω] (a : ℝ) : BM (fun _ : Ω => a) :=
  ⟨measurable_const, |a|, fun _ => le_rfl⟩

lemma BM.add {Ω : Type*} [MeasurableSpace Ω] {g k : Ω → ℝ} (hg : BM g) (hk : BM k) :
    BM (fun ω => g ω + k ω) := by
  obtain ⟨hgm, c1, h1⟩ := hg
  obtain ⟨hkm, c2, h2⟩ := hk
  exact ⟨hgm.add hkm, c1 + c2, fun ω => (abs_add_le _ _).trans (add_le_add (h1 ω) (h2 ω))⟩

lemma BM.neg {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ} (hg : BM g) :
    BM (fun ω => - g ω) := by
  obtain ⟨hgm, c1, h1⟩ := hg
  exact ⟨hgm.neg, c1, fun ω => by rw [abs_neg]; exact h1 ω⟩

lemma BM.sub {Ω : Type*} [MeasurableSpace Ω] {g k : Ω → ℝ} (hg : BM g) (hk : BM k) :
    BM (fun ω => g ω - k ω) := by
  have := hg.add hk.neg
  simpa [sub_eq_add_neg] using this

lemma BM.mul {Ω : Type*} [MeasurableSpace Ω] {g k : Ω → ℝ} (hg : BM g) (hk : BM k) :
    BM (fun ω => g ω * k ω) := by
  obtain ⟨hgm, c1, h1⟩ := hg
  obtain ⟨hkm, c2, h2⟩ := hk
  refine ⟨hgm.mul hkm, c1 * c2, fun ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (h1 ω) (h2 ω) (abs_nonneg _) ((abs_nonneg _).trans (h1 ω))

lemma BM.sum {Ω ι : Type*} [MeasurableSpace Ω] (s : Finset ι) {g : ι → Ω → ℝ}
    (hg : ∀ i ∈ s, BM (g i)) : BM (fun ω => ∑ i ∈ s, g i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BM.const (Ω := Ω) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma BM.integrable {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ} (hg : BM g)
    (Pr : Measure Ω) [IsFiniteMeasure Pr] : Integrable g Pr := by
  obtain ⟨hgm, c, h⟩ := hg
  exact Integrable.mono' (integrable_const c) hgm.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using h ω)

/-- the σ-algebra of the past before slot `t` -/
def pastSigma {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m) : ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | k + 1 => ℱ k

end DriftAux

open DriftAux in
theorem solution {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮)
    (hM : RateHyp M) (hMm : DownlinkMeas M) (V : ℝ) (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ : Filtration ℕ mΩ) (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮) (R P : ℕ → Ω → Fin L → ℝ)
    (μ : Measure ((Fin L → ℝ) × 𝒮)) (hiid : IsAdaptedIID Pr ℱ A S μ)
    (hA : ∀ t ω i, 0 ≤ A t ω i ∧ A t ω i ≤ M.Rhat)
    (hRP : ∀ t, Measurable[ℱ t] (R t) ∧ Measurable[ℱ t] (P t))
    (hrun : ∀ ω, IsECCARun M V u₀ (fun t => A t ω) (fun t => S t ω) (fun t => R t ω)
      (fun t => P t ω))
    (q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ) (hq : q ∈ achievable M μ) (t : ℕ) :
    (∫ ω, (∑ i, queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) (t + 1) i ^ 2 +
          virtD M (fun τ => P τ ω) (t + 1) ^ 2) / 2 ∂Pr) -
        (∫ ω, (∑ i, queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i ^ 2 +
          virtD M (fun τ => P τ ω) t ^ 2) / 2 ∂Pr) -
        V * ∑ i, ∫ ω, R t ω i ∂Pr ≤
      B M - V * ∑ i, q.1 i +
        ∑ i, (∫ ω, queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i ∂Pr) *
          (q.1 i - q.2.1 i) +
        (∫ ω, virtD M (fun τ => P τ ω) t ∂Pr) * (q.2.2 - M.Pav) := by
  set U : Ω → ℕ → Fin L → ℝ := fun ω t i =>
    queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i with hUdef
  set D : Ω → ℕ → ℝ := fun ω t => virtD M (fun τ => P τ ω) t with hDdef
  set Cq : ℕ → Ω → Fin L → ℝ := fun τ ω i => M.C i (P τ ω) (S τ ω) with hCq
  have hUstep : ∀ ω τ i, U ω (τ + 1) i = max (U ω τ i - Cq τ ω i) 0 + R τ ω i :=
    fun ω τ i => rfl
  have hU0 : ∀ ω i, U ω 0 i = u₀ i := fun ω i => rfl
  have hDstep : ∀ ω τ, D ω (τ + 1) = max (D ω τ - M.Pav) 0 + ∑ i, P τ ω i := fun ω τ => rfl
  have hD0 : ∀ ω, D ω 0 = 0 := fun ω => rfl
  have hRb : ∀ τ ω i, 0 ≤ R τ ω i ∧ R τ ω i ≤ M.Rhat := fun τ ω i =>
    ⟨((hrun ω τ).1 i).1, ((hrun ω τ).1 i).2.trans (hA τ ω i).2⟩
  have hPf : ∀ τ ω, IsFeasiblePower M (P τ ω) := fun τ ω => (hrun ω τ).2.2.1
  have hCb : ∀ τ ω i, 0 ≤ Cq τ ω i ∧ Cq τ ω i ≤ M.muMax := fun τ ω i =>
    ⟨hM.rate_nonneg _ (hPf τ ω) _ i, hM.rate_le _ (hPf τ ω) _ i⟩
  have hUb : ∀ ω τ i, 0 ≤ U ω τ i ∧ U ω τ i ≤ u₀ i + τ * M.Rhat := by
    intro ω τ i
    induction τ with
    | zero => simp [hU0, hu₀ i]
    | succ τ ih =>
      rw [hUstep]
      have h1 := (hCb τ ω i).1
      have h2 := hRb τ ω i
      have h3 := le_max_right (U ω τ i - Cq τ ω i) 0
      have h4 : max (U ω τ i - Cq τ ω i) 0 ≤ U ω τ i := max_le (by linarith) ih.1
      push_cast
      constructor <;> linarith
  have hPb : ∀ τ ω, 0 ≤ ∑ i, P τ ω i ∧ ∑ i, P τ ω i ≤ M.Pmax := fun τ ω =>
    ⟨Finset.sum_nonneg fun i _ => (hPf τ ω).1 i, (hPf τ ω).2⟩
  have hDb : ∀ ω τ, 0 ≤ D ω τ ∧ D ω τ ≤ τ * M.Pmax := by
    intro ω τ
    induction τ with
    | zero => simp [hD0]
    | succ τ ih =>
      rw [hDstep]
      have h2 := hPb τ ω
      have h3 := le_max_right (D ω τ - M.Pav) 0
      have h4 : max (D ω τ - M.Pav) 0 ≤ D ω τ := max_le (by linarith [hM.Pav_nonneg]) ih.1
      push_cast
      constructor <;> linarith
  -- measurability with respect to the past
  have hSm : ∀ τ, Measurable[ℱ τ] (S τ) := fun τ => measurable_snd.comp (hiid.1 τ)
  have hpast : ∀ k τ, τ ≤ k + 1 → (∀ i, Measurable[ℱ k] (fun ω => U ω τ i)) ∧
      Measurable[ℱ k] (fun ω => D ω τ) := by
    intro k τ
    induction τ with
    | zero =>
      intro _
      exact ⟨fun i => measurable_const, measurable_const⟩
    | succ τ ih =>
      intro hτ
      have hle : ℱ τ ≤ ℱ k := ℱ.mono (by omega)
      obtain ⟨ihU, ihD⟩ := ih (by omega)
      have hRk : Measurable[ℱ k] (R τ) := (hRP τ).1.mono hle le_rfl
      have hPk : Measurable[ℱ k] (P τ) := (hRP τ).2.mono hle le_rfl
      have hSk : Measurable[ℱ k] (S τ) := (hSm τ).mono hle le_rfl
      constructor
      · intro i
        have hC : Measurable[ℱ k] (fun ω => Cq τ ω i) := (hMm i).comp (hPk.prodMk hSk)
        exact (((ihU i).sub hC).max measurable_const).add ((measurable_pi_apply i).comp hRk)
      · exact ((ihD.sub measurable_const).max measurable_const).add
          (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp hPk)
  have hUm : ∀ τ i, Measurable (fun ω => U ω τ i) := fun τ i =>
    ((hpast τ τ (by omega)).1 i).mono (ℱ.le τ) le_rfl
  have hDm : ∀ τ, Measurable (fun ω => D ω τ) := fun τ =>
    ((hpast τ τ (by omega)).2).mono (ℱ.le τ) le_rfl
  have hRm : ∀ τ, Measurable (R τ) := fun τ => (hRP τ).1.mono (ℱ.le τ) le_rfl
  have hPm : ∀ τ, Measurable (P τ) := fun τ => (hRP τ).2.mono (ℱ.le τ) le_rfl
  have hSm' : ∀ τ, Measurable (S τ) := fun τ => (hSm τ).mono (ℱ.le τ) le_rfl
  -- bounded measurable pieces
  have bU : ∀ τ i, BM (fun ω => U ω τ i) := fun τ i =>
    ⟨hUm τ i, u₀ i + τ * M.Rhat, fun ω => by
      rw [abs_of_nonneg (hUb ω τ i).1]; exact (hUb ω τ i).2⟩
  have bD : ∀ τ, BM (fun ω => D ω τ) := fun τ =>
    ⟨hDm τ, τ * M.Pmax, fun ω => by rw [abs_of_nonneg (hDb ω τ).1]; exact (hDb ω τ).2⟩
  have bR : ∀ τ i, BM (fun ω => R τ ω i) := fun τ i =>
    ⟨(measurable_pi_apply i).comp (hRm τ), M.Rhat, fun ω => by
      rw [abs_of_nonneg (hRb τ ω i).1]; exact (hRb τ ω i).2⟩
  have bP : ∀ τ i, BM (fun ω => P τ ω i) := fun τ i =>
    ⟨(measurable_pi_apply i).comp (hPm τ), M.Pmax, fun ω => by
      rw [abs_of_nonneg ((hPf τ ω).1 i)]
      calc P τ ω i ≤ ∑ j, P τ ω j :=
            Finset.single_le_sum (fun j _ => (hPf τ ω).1 j) (Finset.mem_univ i)
        _ ≤ M.Pmax := (hPf τ ω).2⟩
  have bC : ∀ τ i, BM (fun ω => Cq τ ω i) := fun τ i =>
    ⟨(hMm i).comp ((hPm τ).prodMk (hSm' τ)), M.muMax, fun ω => by
      rw [abs_of_nonneg (hCb τ ω i).1]; exact (hCb τ ω i).2⟩
  -- the per-slot functions
  set L0 : Ω → ℝ := fun ω => (∑ i, U ω t i ^ 2 + D ω t ^ 2) / 2 with hL0
  set L1 : Ω → ℝ := fun ω => (∑ i, U ω (t + 1) i ^ 2 + D ω (t + 1) ^ 2) / 2 with hL1
  set h : Ω → ℝ := fun ω => ∑ i, (U ω t i - V) * R t ω i -
    ∑ i, (U ω t i * Cq t ω i - D ω t * P t ω i) with hh
  have bL : ∀ τ, BM (fun ω => (∑ i, U ω τ i ^ 2 + D ω τ ^ 2) / 2) := by
    intro τ
    have := ((BM.sum Finset.univ fun i _ => (bU τ i).mul (bU τ i)).add
      ((bD τ).mul (bD τ))).mul (BM.const (Ω := Ω) (1 / 2 : ℝ))
    convert this using 2 with ω
    simp only [pow_two]; ring
  have bh : BM h := by
    refine BM.sub (BM.sum _ fun i _ => ((bU t i).sub (BM.const V)).mul (bR t i))
      (BM.sum _ fun i _ => ((bU t i).mul (bC t i)).sub ((bD t).mul (bP t i)))
  -- pointwise drift bound
  have hptw : ∀ ω, L1 ω - L0 ω - V * ∑ i, R t ω i ≤ B M + h ω - D ω t * M.Pav := by
    intro ω
    have := drift_bound M hM V (fun i => U ω t i) (D ω t) (fun i => (hUb ω t i).1) (hDb ω t).1
      (S t ω) (R t ω) (P t ω) (fun i => hRb t ω i) (hPf t ω)
    simp only [hL1, hL0, hh, hUstep, hDstep]
    linarith
  -- the comparison decision
  obtain ⟨ν, hνp, hmarg, hae, hint, rfl⟩ := hq
  have hGt : pastSigma ℱ t ≤ mΩ ∧
      Indep (MeasurableSpace.comap (fun ω => (A t ω, S t ω)) inferInstance) (pastSigma ℱ t) Pr ∧
      (∀ i, Measurable[pastSigma ℱ t] (fun ω => U ω t i)) ∧
      Measurable[pastSigma ℱ t] (fun ω => D ω t) := by
    cases t with
    | zero => exact ⟨bot_le, indep_bot_right _, fun i => measurable_const, measurable_const⟩
    | succ k =>
      exact ⟨ℱ.le k, hiid.2.2 k, (hpast k (k + 1) le_rfl).1, (hpast k (k + 1) le_rfl).2⟩
  obtain ⟨hG, hind, hGU, hGD⟩ := hGt
  have hY : Measurable (fun ω => (A t ω, S t ω)) := (hiid.1 t).mono (ℱ.le t) le_rfl
  have hmarg' : ν.map Prod.fst = Pr.map (fun ω => (A t ω, S t ω)) := by
    rw [hmarg, hiid.2.1 t]
  set f : Option (Option (Fin L)) → Ω → ℝ := fun j ω => match j with
    | none => -V
    | some none => D ω t
    | some (some i) => U ω t i with hf
  set g : Option (Option (Fin L)) → ((Fin L → ℝ) × 𝒮) × ((Fin L → ℝ) × (Fin L → ℝ)) → ℝ :=
    fun j x => match j with
    | none => ∑ i, x.2.1 i
    | some none => ∑ i, x.2.2 i
    | some (some i) => x.2.1 i - M.C i x.2.2 x.1.2 with hg
  have hu0s : 0 ≤ ∑ i, (u₀ i + t * M.Rhat) :=
    Finset.sum_nonneg fun i _ => by have := hu₀ i; have := hM.Rhat_nonneg; positivity
  have hfG : ∀ j, Measurable[pastSigma ℱ t] (f j) := by
    rintro (_ | _ | i)
    · exact measurable_const
    · exact hGD
    · exact hGU i
  have hfb : ∀ j ω, |f j ω| ≤ |V| + ∑ i, (u₀ i + t * M.Rhat) + t * M.Pmax := by
    have hPm0 : 0 ≤ (t : ℝ) * M.Pmax := by have := hM.Pmax_nonneg; positivity
    rintro (_ | _ | i) ω
    · simp only [hf, abs_neg]; linarith
    · simp only [hf]
      rw [abs_of_nonneg (hDb ω t).1]
      have := (hDb ω t).2
      linarith [abs_nonneg V]
    · simp only [hf]
      rw [abs_of_nonneg (hUb ω t i).1]
      have h1 := (hUb ω t i).2
      have h2 : u₀ i + t * M.Rhat ≤ ∑ i, (u₀ i + t * M.Rhat) :=
        Finset.single_le_sum (f := fun i => u₀ i + t * M.Rhat)
          (fun j _ => by have := hu₀ j; have := hM.Rhat_nonneg; positivity) (Finset.mem_univ i)
      linarith [abs_nonneg V]
  have hgm : ∀ j, Measurable (g j) := by
    rintro (_ | _ | i)
    · exact Finset.measurable_sum _ fun i _ => by fun_prop
    · exact Finset.measurable_sum _ fun i _ => by fun_prop
    · exact (by fun_prop : Measurable fun x : ((Fin L → ℝ) × 𝒮) × ((Fin L → ℝ) × (Fin L → ℝ)) =>
        x.2.1 i).sub ((hMm i).comp ((measurable_snd.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_fst)))
  have hgi : ∀ j, Integrable (g j) ν := by
    rintro (_ | _ | i)
    · exact integrable_finsetSum _ fun i _ => (hint i).1
    · refine Integrable.mono' (integrable_const M.Pmax) (hgm (some none)).aestronglyMeasurable ?_
      filter_upwards [hae] with x hx
      simp only [hg, Real.norm_eq_abs]
      rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => hx.2.1 i)]
      exact hx.2.2
    · exact (hint i).1.sub (hint i).2
  have hcore := core (pastSigma ℱ t) Pr hG (fun ω => (A t ω, S t ω)) hY hind ν hmarg' f hfG _ hfb g hgm hgi
    (fun x => (∀ i, 0 ≤ x.2.1 i ∧ x.2.1 i ≤ x.1.1 i) ∧ IsFeasiblePower M x.2.2) hae
    h (bh.integrable Pr) (by
      intro ω e he
      have flow := (hrun ω t).2.1 e.1 (fun i => he.1 i)
      have pow := (hrun ω t).2.2.2 e.2 he.2
      simp only [Fintype.sum_option, hf, hg, hh]
      have key : ∑ i, (U ω t i - V) * e.1 i - ∑ i, (U ω t i * M.C i e.2 (S t ω) - D ω t * e.2 i) =
          -V * ∑ i, e.1 i + (D ω t * ∑ i, e.2 i + ∑ i, U ω t i * (e.1 i - M.C i e.2 (S t ω))) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [hUdef, hDdef, hCq] at flow pow key ⊢
      linarith)
  -- evaluate the right-hand side of the comparison
  simp only [Fintype.sum_option, hf, hg] at hcore
  rw [integral_const, integral_finsetSum _ (fun i _ => (hint i).1)] at hcore
  simp only [probReal_univ, smul_eq_mul, one_mul] at hcore
  have hsub : ∀ i, ∫ x, (x.2.1 i - M.C i x.2.2 x.1.2) ∂ν =
      (∫ x, x.2.1 i ∂ν) - ∫ x, M.C i x.2.2 x.1.2 ∂ν := fun i => integral_sub (hint i).1 (hint i).2
  simp only [hsub] at hcore
  -- integrate the pointwise drift bound
  have iL1 : Integrable L1 Pr := (bL (t + 1)).integrable Pr
  have iL0 : Integrable L0 Pr := (bL t).integrable Pr
  have iR : ∀ i, Integrable (fun ω => R t ω i) Pr := fun i => (bR t i).integrable Pr
  have iRs : Integrable (fun ω => V * ∑ i, R t ω i) Pr :=
    (integrable_finsetSum _ fun i _ => iR i).const_mul V
  have ih : Integrable h Pr := bh.integrable Pr
  have iD : Integrable (fun ω => D ω t) Pr := (bD t).integrable Pr
  have hmono : ∫ ω, (L1 ω - L0 ω - V * ∑ i, R t ω i) ∂Pr ≤
      ∫ ω, (B M + h ω - D ω t * M.Pav) ∂Pr :=
    integral_mono ((iL1.sub iL0).sub iRs)
      (((integrable_const (B M)).add ih).sub (iD.mul_const M.Pav)) hptw
  have iA : Integrable (fun ω => L1 ω - L0 ω) Pr := iL1.sub iL0
  have iBh : Integrable (fun ω => B M + h ω) Pr := (integrable_const (B M)).add ih
  have iDP : Integrable (fun ω => D ω t * M.Pav) Pr := iD.mul_const M.Pav
  rw [integral_sub iA iRs, integral_sub iL1 iL0, integral_const_mul,
    integral_finsetSum _ (fun i _ => iR i), integral_sub iBh iDP,
    integral_add (integrable_const (B M)) ih, integral_mul_const,
    integral_const] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  have e1 : ∀ i, (∫ ω, U ω t i ∂Pr) * ((∫ x, x.2.1 i ∂ν) - ∫ x, M.C i x.2.2 x.1.2 ∂ν) =
      (∫ ω, U ω t i ∂Pr) * ((∫ x, x.2.1 i ∂ν) - ∫ x, M.C i x.2.2 x.1.2 ∂ν) := fun i => rfl
  show (∫ ω, L1 ω ∂Pr) - (∫ ω, L0 ω ∂Pr) - V * ∑ i, ∫ ω, R t ω i ∂Pr ≤ _
  simp only
  linarith
