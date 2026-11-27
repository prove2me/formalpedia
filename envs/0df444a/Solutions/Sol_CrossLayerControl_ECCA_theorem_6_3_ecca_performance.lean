-- Prove2me | solution 1 for CrossLayerControl.ECCA.theorem_6_3_ecca_performance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:12:07.609978+00:00
-- url     : https://prove2.me/submissions/37d5ec66-901a-466e-a0b8-d70d71d1e187

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_DownlinkMeas
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun
import Definitions.Def_CrossLayerControl_ECCA_IsAdaptedIID
import Definitions.Def_CrossLayerControl_ECCA_throughputAvg
import Definitions.Def_CrossLayerControl_ECCA_IsAdmissiblePolicy
import Definitions.Def_CrossLayerControl_ECCA_rStar
import Definitions.Def_CrossLayerControl_ECCA_B
import Theorems.Thm_CrossLayerControl_ECCA_queue_bound
import Theorems.Thm_CrossLayerControl_ECCA_virtual_queue_bound
import Theorems.Thm_CrossLayerControl_ECCA_energy_bound
import Theorems.Thm_CrossLayerControl_ECCA_ecca_drift_comparison
import Theorems.Thm_CrossLayerControl_ECCA_rStar_ge_admissible

open MeasureTheory Filter CrossLayerControl.ECCA

universe u

theorem solution {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮]
    (M : Downlink L 𝒮) (hM : DownlinkHyp M) (V : ℝ) (hV : 0 < V)
    (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat) :
    (∀ (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ),
      (∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) → IsECCARun M V u₀ a s r p →
      (∀ t i, queueU M u₀ s r p t i ≤ V + M.Rhat) ∧
      (∀ t, virtD M p t ≤ M.β * V + M.β * M.Rhat + M.Pmax) ∧
      (∀ t₀ T : ℕ, ∑ τ ∈ Finset.Ico t₀ (t₀ + T), ∑ i, p τ i ≤
        M.Pav * T + (M.β * V + M.β * M.Rhat + M.Pmax)) ∧
      limsup (fun T : ℕ => (((T : ℝ)⁻¹ * ∑ τ ∈ Finset.range T, ∑ i, p τ i : ℝ) : EReal))
        atTop ≤ (M.Pav : EReal)) ∧
    (DownlinkMeas M →
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (ℱ : Filtration ℕ mΩ) (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮)
        (R P : ℕ → Ω → Fin L → ℝ) (μ : Measure ((Fin L → ℝ) × 𝒮)),
        IsAdaptedIID Pr ℱ A S μ →
        (∀ t ω i, 0 ≤ A t ω i ∧ A t ω i ≤ M.Rhat) →
        (∀ t, Measurable[ℱ t] (R t) ∧ Measurable[ℱ t] (P t)) →
        (∀ ω, IsECCARun M V u₀ (fun t => A t ω) (fun t => S t ω) (fun t => R t ω)
          (fun t => P t ω)) →
        ((rStar M μ - B M / V : ℝ) : EReal) ≤
            liminf (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop ∧
        ∀ (R' P' : ℕ → Ω → Fin L → ℝ) (u₀' : Fin L → ℝ),
          IsAdmissiblePolicy M Pr A S R' P' u₀' →
          limsup (fun t : ℕ => (throughputAvg Pr R' t : EReal)) atTop - ((B M / V : ℝ) : EReal) ≤
            liminf (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop) := by
  have hR := hM.Rhat_nonneg
  have hPav := hM.Pav_nonneg
  have hPm := hM.Pmax_nonneg
  refine ⟨?_, ?_⟩
  · intro a s r p ha hrun
    refine ⟨fun t i => (queue_bound M hM.rate_nonneg V u₀ hu₀ a s r p ha hrun t i).2,
      virtual_queue_bound M hM V hV u₀ hu₀ a s r p ha hrun,
      energy_bound M hM V hV u₀ hu₀ a s r p ha hrun⟩
  · intro hMm Ω mΩ Pr _ ℱ A S R P μ hiid hA hRP hrun
    -- notation
    set U : Ω → ℕ → Fin L → ℝ := fun ω t i =>
      queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i with hUdef
    set D : Ω → ℕ → ℝ := fun ω t => virtD M (fun τ => P τ ω) t with hDdef
    set I : ℕ → ℝ := fun t => ∫ ω, (∑ i, U ω t i ^ 2 + D ω t ^ 2) / 2 ∂Pr with hIdef
    have hUnn : ∀ ω t i, 0 ≤ U ω t i := fun ω t i =>
      (queue_bound M hM.rate_nonneg V u₀ hu₀ _ _ _ _ (fun t i => hA t ω i) (hrun ω) t i).1
    have hDnn : ∀ ω t, 0 ≤ D ω t := by
      intro ω t
      cases t with
      | zero => show (0:ℝ) ≤ 0; exact le_rfl
      | succ t =>
        show 0 ≤ max (D ω t - M.Pav) 0 + ∑ i, P t ω i
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => ((hrun ω t).2.2.1).1 i)
        have := le_max_right (D ω t - M.Pav) 0
        linarith
    have hInn : ∀ t, 0 ≤ I t := fun t => integral_nonneg (fun ω => by
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (U ω t i))
      have := sq_nonneg (D ω t)
      positivity)
    have hRnn : ∀ t ω i, 0 ≤ R t ω i := fun t ω i => ((hrun ω t).1 i).1
    have hthr_nn : ∀ t, 0 ≤ throughputAvg Pr R t := by
      intro t
      unfold throughputAvg
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ =>
        integral_nonneg fun ω => hRnn τ ω i
    have hB : 0 ≤ B M := by unfold B; positivity
    -- the drift comparison, extended to the closure
    have hcl : ∀ q ∈ closure (achievable M μ), ∀ t,
        I (t + 1) - I t - V * ∑ i, ∫ ω, R t ω i ∂Pr ≤
          B M - V * ∑ i, q.1 i + ∑ i, (∫ ω, U ω t i ∂Pr) * (q.1 i - q.2.1 i) +
            (∫ ω, D ω t ∂Pr) * (q.2.2 - M.Pav) := by
      intro q hq t
      have hsub : achievable M μ ⊆ {q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ |
          I (t + 1) - I t - V * ∑ i, ∫ ω, R t ω i ∂Pr ≤
          B M - V * ∑ i, q.1 i + ∑ i, (∫ ω, U ω t i ∂Pr) * (q.1 i - q.2.1 i) +
            (∫ ω, D ω t ∂Pr) * (q.2.2 - M.Pav)} := by
        intro q' hq'
        exact ecca_drift_comparison M hM.toRateHyp hMm V u₀ (fun i => (hu₀ i).1) Pr ℱ A S R P μ
          hiid hA hRP hrun q' hq' t
      have hclosed : IsClosed {q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ |
          I (t + 1) - I t - V * ∑ i, ∫ ω, R t ω i ∂Pr ≤
          B M - V * ∑ i, q.1 i + ∑ i, (∫ ω, U ω t i ∂Pr) * (q.1 i - q.2.1 i) +
            (∫ ω, D ω t ∂Pr) * (q.2.2 - M.Pav)} :=
        isClosed_le continuous_const (by fun_prop)
      exact closure_minimal hsub hclosed hq
    -- lower bound for each feasible q
    have hlow : ∀ q ∈ closure (achievable M μ), (∀ i, q.1 i ≤ q.2.1 i) → q.2.2 ≤ M.Pav →
        (((∑ i, q.1 i - B M / V : ℝ)) : EReal) ≤
          liminf (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop := by
      intro q hq hq1 hq2
      have hstep : ∀ t, I (t + 1) - I t - V * ∑ i, ∫ ω, R t ω i ∂Pr ≤
          B M - V * ∑ i, q.1 i := by
        intro t
        have h := hcl q hq t
        have h1 : ∑ i, (∫ ω, U ω t i ∂Pr) * (q.1 i - q.2.1 i) ≤ 0 :=
          Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos
            (integral_nonneg fun ω => hUnn ω t i) (by linarith [hq1 i])
        have h2 : (∫ ω, D ω t ∂Pr) * (q.2.2 - M.Pav) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (integral_nonneg fun ω => hDnn ω t) (by linarith)
        linarith
      have htel : ∀ t : ℕ, I t - I 0 - V * ∑ τ ∈ Finset.range t, ∑ i, ∫ ω, R τ ω i ∂Pr ≤
          t * (B M - V * ∑ i, q.1 i) := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [Finset.sum_range_succ, mul_add]
          have := hstep t
          push_cast
          linarith
      have hbd : ∀ t : ℕ, 1 ≤ t → ∑ i, q.1 i - B M / V - I 0 / V * (t : ℝ)⁻¹ ≤
          throughputAvg Pr R t := by
        intro t ht
        have htpos : (0 : ℝ) < t := by exact_mod_cast ht
        have h := htel t
        have h0 := hInn t
        unfold throughputAvg
        have key : t * (V * ∑ i, q.1 i - B M) - I 0 ≤
            V * ∑ τ ∈ Finset.range t, ∑ i, ∫ ω, R τ ω i ∂Pr := by nlinarith
        have e : ∑ i, q.1 i - B M / V - I 0 / V * (t : ℝ)⁻¹ =
            (t : ℝ)⁻¹ * ((t * (V * ∑ i, q.1 i - B M) - I 0) / V) := by
          field_simp
        rw [e]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hV]
        linarith
      have hlim : Tendsto (fun t : ℕ =>
          ((∑ i, q.1 i - B M / V - I 0 / V * (t : ℝ)⁻¹ : ℝ) : EReal)) atTop
          (nhds ((∑ i, q.1 i - B M / V : ℝ) : EReal)) := by
        have h1 : Tendsto (fun t : ℕ => (∑ i, q.1 i - B M / V - I 0 / V * (t : ℝ)⁻¹ : ℝ))
            atTop (nhds (∑ i, q.1 i - B M / V)) := by
          have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (I 0 / V)
          simpa using this.const_sub (∑ i, q.1 i - B M / V)
        exact (continuous_coe_real_ereal.tendsto _).comp h1
      rw [← hlim.liminf_eq]
      apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
      filter_upwards [eventually_ge_atTop 1] with t ht
      exact EReal.coe_le_coe_iff.mpr (hbd t ht)
    -- clause 5
    have h5 : ((rStar M μ - B M / V : ℝ) : EReal) ≤
        liminf (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop := by
      set Sset := {y : ℝ | ∃ q ∈ closure (achievable M μ),
        (∀ i, q.1 i ≤ q.2.1 i) ∧ q.2.2 ≤ M.Pav ∧ y = ∑ i, q.1 i} with hSset
      have hmem : ∀ y ∈ Sset, ((y - B M / V : ℝ) : EReal) ≤
          liminf (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop := by
        rintro y ⟨q, hq, hq1, hq2, rfl⟩
        exact hlow q hq hq1 hq2
      have hrs : rStar M μ = sSup Sset := rfl
      by_cases hne : Sset.Nonempty ∧ BddAbove Sset
      · apply le_of_forall_lt
        intro c hc
        obtain ⟨z, hcz, hz⟩ := EReal.lt_iff_exists_real_btwn.mp hc
        have hz' : z + B M / V < sSup Sset := by
          rw [← hrs]; have := EReal.coe_lt_coe_iff.mp hz; linarith
        obtain ⟨y, hy, hzy⟩ := exists_lt_of_lt_csSup hne.1 hz'
        calc c < z := hcz
          _ ≤ ((y - B M / V : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
          _ ≤ _ := hmem y hy
      · have h0 : rStar M μ = 0 := by
          rw [hrs]
          rcases not_and_or.mp hne with h | h
          · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]
          · exact Real.sSup_of_not_bddAbove h
        rw [h0]
        have hBV : 0 ≤ B M / V := by positivity
        calc (((0 : ℝ) - B M / V : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) :=
              EReal.coe_le_coe_iff.mpr (by linarith)
          _ ≤ _ := le_liminf_of_le (by isBoundedDefault)
              (Eventually.of_forall fun t => EReal.coe_le_coe_iff.mpr (hthr_nn t))
    refine ⟨h5, ?_⟩
    intro R' P' u₀' hadm
    have hAS : ∀ t, Measurable (fun ω => (A t ω, S t ω)) := fun t =>
      (hiid.1 t).mono (ℱ.le t) le_rfl
    have hle := rStar_ge_admissible M hM.toRateHyp hMm Pr A S R' P' u₀' μ hAS hiid.2.1 hA hadm
    calc limsup (fun t : ℕ => (throughputAvg Pr R' t : EReal)) atTop - ((B M / V : ℝ) : EReal)
        ≤ (rStar M μ : EReal) - ((B M / V : ℝ) : EReal) := EReal.sub_le_sub hle le_rfl
      _ = ((rStar M μ - B M / V : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ _ := h5
