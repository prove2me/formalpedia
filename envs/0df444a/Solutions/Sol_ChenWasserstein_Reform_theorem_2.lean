-- Prove2me | solution 1 for ChenWasserstein.Reform.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-29T05:15:54.073+00:00
-- url     : https://prove2.me/submissions/44bb010f-91aa-4643-99f1-7831729c6ea8

import Mathlib
import Definitions.Def_ChenWasserstein_Reform_Data
import Theorems.Thm_ChenWasserstein_Reform_lemma_1
import Theorems.Thm_ModelRiskOT_WorstProb_eq_13

open MeasureTheory
open scoped ENNReal BigOperators

namespace ChenWasserstein.Attempt

noncomputable def scalarObj {N : ℕ} (d : Fin N → ℝ) (θ lam : ℝ) : ℝ :=
  lam * θ + (1 / (N : ℝ)) * ∑ i, max (1 - lam * d i) 0

lemma ofReal_sum_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ENNReal.ofReal_add]
      · exact congrArg (fun z => ENNReal.ofReal (f a) + z)
          (ih (by intro i hi; exact hf i (by simp [hi])))
      · exact hf a (by simp)
      · exact Finset.sum_nonneg fun i hi => hf i (by simp [hi])

theorem scalar_bound_of_threshold {N : ℕ} (d : Fin N → ℝ) (ε θ : ℝ)
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε < 1) (hθ : 0 < θ)
    (hd : ∀ i, 0 ≤ d i)
    (hθF : θ ≤ (1 / (N : ℝ)) * ChenWasserstein.Reform.fractionalSmallest d (ε * (N : ℝ))) :
    (⨅ lam ∈ Set.Ici (0 : ℝ), ENNReal.ofReal (scalarObj d θ lam)) ≤
      ENNReal.ofReal ε := by
  let F : ℝ := ChenWasserstein.Reform.fractionalSmallest d (ε * (N : ℝ))
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNF : θ * (N : ℝ) ≤ F := by
    have h := hθF
    field_simp [Nat.cast_ne_zero.mpr hN.ne'] at h
    dsimp [F]
    simpa [mul_comm] using h
  obtain ⟨s, t, hs, hcon, heq, hbound⟩ :=
    ChenWasserstein.Reform.lemma_1 d ε hN hε hε1
  let s0 : Fin N → ℝ := fun i => max 0 (t - d i)
  have hs0 : ∀ i, 0 ≤ s0 i := by
    intro i
    exact le_max_left _ _
  have hcon0 : ∀ i, t - s0 i ≤ d i := by
    intro i
    have hi : t - d i ≤ s0 i := le_max_right _ _
    linarith
  have hsumle : (∑ i, s0 i) ≤ ∑ i, s i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : t - d i ≤ s i := by linarith [hcon i]
    exact max_le (hs i) hi'
  have hEqMax : ε * (N : ℝ) * t - ∑ i, s0 i = F := by
    have h0 := hbound s0 t hs0 hcon0
    dsimp [F] at *
    linarith
  have hsum0 : 0 ≤ ∑ i, s0 i := Finset.sum_nonneg fun i _ => hs0 i
  have hFpos : 0 < F := lt_of_lt_of_le (mul_pos hθ hNR) hNF
  have hetapos : 0 < ε * (N : ℝ) := mul_pos hε hNR
  have htprod : 0 < ε * (N : ℝ) * t := by
    have h := hEqMax
    dsimp [F] at h
    nlinarith
  have ht : 0 < t := by nlinarith
  let lam : ℝ := 1 / t
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hlammem : lam ∈ Set.Ici (0 : ℝ) := hlam.le
  have hlamt : lam * t = 1 := by
    dsimp [lam]
    field_simp
  have hscale (i : Fin N) :
      max (1 - lam * d i) 0 = lam * max (t - d i) 0 := by
    rw [mul_max_of_nonneg (t - d i) 0 hlam.le]
    rw [mul_sub]
    rw [hlamt]
    simp [mul_sub]
  have hsumscale :
      (∑ i, max (1 - lam * d i) 0) = lam * ∑ i, max (t - d i) 0 := by
    rw [Finset.sum_congr rfl fun i _ => hscale i]
    rw [← Finset.mul_sum]
  have hreal : scalarObj d θ lam ≤ ε := by
    dsimp [scalarObj]
    rw [hsumscale]
    have hFsum : F + ∑ i, max (t - d i) 0 = ε * (N : ℝ) * t := by
      have hsum0eq : (∑ i, s0 i) = ∑ i, max (t - d i) 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [s0, max_comm]
      calc
        F + ∑ i, max (t - d i) 0 =
            (ε * (N : ℝ) * t - ∑ i, s0 i) + ∑ i, max (t - d i) 0 := by
              rw [hEqMax]
        _ = ε * (N : ℝ) * t := by rw [hsum0eq]; ring
    have hobjineq :
        lam * (θ * (N : ℝ) + ∑ i, max (t - d i) 0) ≤ ε * (N : ℝ) := by
      calc
        lam * (θ * (N : ℝ) + ∑ i, max (t - d i) 0)
            ≤ lam * (F + ∑ i, max (t - d i) 0) :=
              mul_le_mul_of_nonneg_left (add_le_add hNF le_rfl) hlam.le
        _ = ε * (N : ℝ) := by
          rw [hFsum]
          calc
            lam * (ε * (N : ℝ) * t) = ε * (N : ℝ) * (lam * t) := by ring
            _ = ε * (N : ℝ) := by rw [hlamt, mul_one]
    have hgoal :
        lam * θ + (1 / (N : ℝ)) * (lam * ∑ i, max (t - d i) 0) ≤ ε := by
      field_simp [Nat.cast_ne_zero.mpr hN.ne', hlamt]
      nlinarith [hobjineq]
    exact hgoal
  apply le_trans
    (iInf_le_of_le lam (iInf_le_of_le hlammem le_rfl))
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).2 hreal

theorem threshold_of_scalar_bound {N : ℕ} (d : Fin N → ℝ) (ε θ : ℝ)
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε < 1) (hθ : 0 < θ)
    (hd : ∀ i, 0 ≤ d i)
    (hinf :
      (⨅ lam ∈ Set.Ici (0 : ℝ), ENNReal.ofReal (scalarObj d θ lam)) ≤
        ENNReal.ofReal ε) :
    θ ≤ (1 / (N : ℝ)) * ChenWasserstein.Reform.fractionalSmallest d (ε * (N : ℝ)) := by
  let F : ℝ := ChenWasserstein.Reform.fractionalSmallest d (ε * (N : ℝ))
  let A : ℝ := ∑ i, d i
  let D : ℝ := A / (N : ℝ)
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i _ => hd i
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg hA0 hNR.le
  have hgap : 0 < 1 - ε := sub_pos.mpr hε1
  have hnear (δ : ℝ) (hδ : 0 < δ) :
      ∃ lam, 0 ≤ lam ∧ scalarObj d θ lam < ε + δ := by
    by_contra hnot
    have hall : ∀ lam, 0 ≤ lam → ε + δ ≤ scalarObj d θ lam := by
      intro lam hlam
      have hnotlt : ¬ scalarObj d θ lam < ε + δ := by
        intro hlt
        exact hnot ⟨lam, hlam, hlt⟩
      exact le_of_not_gt hnotlt
    have hlow :
        ENNReal.ofReal (ε + δ) ≤
          (⨅ lam ∈ Set.Ici (0 : ℝ), ENNReal.ofReal (scalarObj d θ lam)) := by
      apply le_iInf
      intro lam
      apply le_iInf
      intro hlam
      have hlam' : 0 ≤ scalarObj d θ lam :=
        le_trans (by positivity) (hall lam (by simpa using hlam))
      exact (ENNReal.ofReal_le_ofReal_iff hlam').2
        (hall lam (by simpa using hlam))
    have hcmp := le_trans hlow hinf
    have hreal := (ENNReal.ofReal_le_ofReal_iff hε.le).mp hcmp
    linarith
  have hlower (lam : ℝ) (hlam : 0 ≤ lam) :
      1 - lam * D ≤ scalarObj d θ lam := by
    have hsum :
        (∑ i, (1 - lam * d i)) ≤ ∑ i, max (1 - lam * d i) 0 :=
      Finset.sum_le_sum fun i _ => le_max_left _ _
    have hsumEq :
        (∑ i : Fin N, (1 - lam * d i)) = (N : ℝ) - lam * A := by
      simp [A, Finset.sum_sub_distrib, Finset.mul_sum]
    have hscaled :
        (1 / (N : ℝ)) * ((N : ℝ) - lam * A) =
          1 - lam * D := by
      dsimp [D]
      field_simp [Nat.cast_ne_zero.mpr hN.ne']
    have hterm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 / (N : ℝ))
    rw [hsumEq, hscaled] at hterm
    dsimp [scalarObj]
    have hpos : 0 ≤ lam * θ := mul_nonneg hlam hθ.le
    nlinarith
  obtain ⟨lam0, hlam0, hnear0⟩ := hnear ((1 - ε) / 2) (by positivity)
  have hlamD0 : (1 - ε) / 2 < lam0 * D := by
    have h := hlower lam0 hlam0
    dsimp [D] at *
    nlinarith [hnear0, h]
  have hDpos : 0 < D := by nlinarith [hlam0, hD0, hlamD0]
  have hDpos' : D ≠ 0 := ne_of_gt hDpos
  have hApos : 0 < A := by
    dsimp [D] at hDpos
    have hAeq : A = D * (N : ℝ) := by
      dsimp [D]
      field_simp [Nat.cast_ne_zero.mpr hN.ne']
    rw [hAeq]
    exact mul_pos hDpos hNR
  have hApos' : A ≠ 0 := ne_of_gt hApos
  have hNθ : θ * (N : ℝ) ≤ F := by
    apply le_of_forall_pos_le_add
    intro η hη
    let δ := min ((1 - ε) / 2) (η * (1 - ε) / (2 * A))
    have hδ0 : 0 < δ := by
      dsimp [δ]
      apply lt_min <;> positivity
    have hδgap : δ ≤ (1 - ε) / 2 := min_le_left _ _
    have hδsmall : δ ≤ η * (1 - ε) / (2 * A) := min_le_right _ _
    obtain ⟨lam, hlam, hnearδ⟩ := hnear δ hδ0
    have hlamD : (1 - ε) / 2 < lam * D := by
      have h := hlower lam hlam
      nlinarith [hnearδ, hδgap, h]
    have hlamPos : 0 < lam := by nlinarith [hlam, hD0, hlamD]
    let t : ℝ := 1 / lam
    have ht : 0 < t := by dsimp [t]; positivity
    have hlamt : lam * t = 1 := by dsimp [t]; field_simp
    have htBound : t ≤ (2 * D) / (1 - ε) := by
      have hprod : (1 - ε) < 2 * D * lam := by nlinarith [hlamD]
      have hdiv : (1 - ε) / lam ≤ 2 * D :=
        (div_le_iff₀ hlamPos).2 (by nlinarith [hprod])
      dsimp [t]
      apply (le_div_iff₀ hgap).2
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    have hscale (i : Fin N) :
        max (1 - lam * d i) 0 = lam * max (t - d i) 0 := by
      rw [mul_max_of_nonneg (t - d i) 0 hlam]
      rw [mul_sub, hlamt]
      simp
    have hsumscale :
        (∑ i, max (1 - lam * d i) 0) = lam * ∑ i, max (t - d i) 0 := by
      rw [Finset.sum_congr rfl fun i _ => hscale i]
      rw [← Finset.mul_sum]
    have hnearReal :
        lam * θ + (1 / (N : ℝ)) * (lam * ∑ i, max (t - d i) 0) <
          ε + δ := by
      simpa [scalarObj, hsumscale] using hnearδ
    have hscaleRadius :
        (lam * θ + (1 / (N : ℝ)) * (lam * ∑ i, max (t - d i) 0)) *
            ((N : ℝ) * t) =
          θ * (N : ℝ) + ∑ i, max (t - d i) 0 := by
      field_simp [Nat.cast_ne_zero.mpr hN.ne']
      rw [hlamt]
    have hscaled :=
      mul_lt_mul_of_pos_right hnearReal (mul_pos hNR ht)
    rw [hscaleRadius] at hscaled
    have hscaled' : θ * (N : ℝ) + ∑ i, max (t - d i) 0 <
        ε * (N : ℝ) * t + δ * (N : ℝ) * t := by
      nlinarith [hscaled]
    obtain ⟨s0, t0, hs0, hcon0, _, hbound⟩ :=
      ChenWasserstein.Reform.lemma_1 d ε hN hε hε1
    let r : Fin N → ℝ := fun i => max 0 (t - d i)
    have hr0 : ∀ i, 0 ≤ r i := by intro i; exact le_max_left _ _
    have hrcon : ∀ i, t - r i ≤ d i := by
      intro i
      have hi : t - d i ≤ r i := le_max_right _ _
      linarith
    have hUpper :
        ε * (N : ℝ) * t - ∑ i, max (t - d i) 0 ≤ F := by
      have h := hbound r t hr0 hrcon
      simpa [r, max_comm, F] using h
    have hNt : (N : ℝ) * t ≤ 2 * A / (1 - ε) := by
      calc
        (N : ℝ) * t ≤ (N : ℝ) * ((2 * D) / (1 - ε)) :=
          mul_le_mul_of_nonneg_left htBound hNR.le
        _ = 2 * A / (1 - ε) := by
          dsimp [D]
          field_simp [Nat.cast_ne_zero.mpr hN.ne', hgap.ne']
    have hslack : δ * ((N : ℝ) * t) ≤ η := by
      calc
        δ * ((N : ℝ) * t) ≤ δ * (2 * A / (1 - ε)) :=
          mul_le_mul_of_nonneg_left hNt hδ0.le
        _ ≤ (η * (1 - ε) / (2 * A)) * (2 * A / (1 - ε)) :=
          mul_le_mul_of_nonneg_right hδsmall (by positivity)
        _ = η := by field_simp [hApos', hgap.ne']
    have hNFη : θ * (N : ℝ) ≤ F + η := by
      nlinarith [hscaled', hUpper, hslack]
    exact hNFη
  have hresult : θ ≤ F / (N : ℝ) :=
    (le_div_iff₀ hNR).2 hNθ
  dsimp [F] at hresult ⊢
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hresult

end ChenWasserstein.Attempt

private lemma objective_eq_scalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {N : ℕ} (ξ : Fin N → E)
    (hN : 0 < N) (S : Set E) (θ lam : ℝ) (hθ : 0 < θ)
    (hlam : 0 ≤ lam) :
    ModelRiskOT.WorstProb.obj13 (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) θ Sᶜ lam =
      ENNReal.ofReal (ChenWasserstein.Attempt.scalarObj
        (fun i => WassDRCCP.Improved.distUnsafe S (ξ i)) θ lam) := by
  let d : Fin N → ℝ := fun i => WassDRCCP.Improved.distUnsafe S (ξ i)
  have hd (i : Fin N) : 0 ≤ d i := by
    dsimp [d, WassDRCCP.Improved.distUnsafe]
    exact Metric.infDist_nonneg
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hcoeff : (N : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hNreal]
    simp
  have hobj :
      ModelRiskOT.WorstProb.obj13 (fun u v : E => ‖u - v‖)
        (WassersteinDRO.Duality.empiricalDistribution ξ) θ Sᶜ lam =
        ENNReal.ofReal (lam * θ) +
      (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N,
            ENNReal.ofReal (1 - lam * d i) := by
    simp [ModelRiskOT.WorstProb.obj13,
      ModelRiskOT.WorstProb.costToSet,
      WassersteinDRO.Duality.empiricalDistribution,
      WassDRCCP.Improved.distUnsafe, Metric.infDist_eq_iInf, dist_eq_norm, d]
  rw [hobj, hcoeff]
  have hterms (i : Fin N) :
      ENNReal.ofReal (1 - lam * d i) =
        ENNReal.ofReal (max (1 - lam * d i) 0) := by
    rw [ENNReal.ofReal_max]
    simp
  simp_rw [hterms]
  rw [← ChenWasserstein.Attempt.ofReal_sum_nonneg]
  · rw [← ENNReal.ofReal_mul]
    · rw [← ENNReal.ofReal_add]
      · congr 1
        simp [ChenWasserstein.Attempt.scalarObj, d, one_div, add_comm, add_left_comm,
          add_assoc, mul_comm, mul_left_comm, mul_assoc]
      · exact mul_nonneg hlam hθ.le
      · positivity
    · positivity
  · intro i hi
    exact le_max_right _ _

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {N : ℕ}
    (ξ : Fin N → E) (S : Set E) (ε θ : ℝ)
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε < 1) (hθ : 0 < θ)
    (hS : IsOpen S) (hC : Sᶜ.Nonempty) :
    ModelRiskOT.WorstProb.worstProb (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) θ Sᶜ ≤ ENNReal.ofReal ε ↔
    θ ≤ (1 / (N : ℝ)) *
      ChenWasserstein.Reform.fractionalSmallest
        (fun i => WassDRCCP.Improved.distUnsafe S (ξ i)) (ε * (N : ℝ)) := by
  let c : E → E → ℝ := fun u v => ‖u - v‖
  let μ : Measure E := WassersteinDRO.Duality.empiricalDistribution ξ
  let d : Fin N → ℝ := fun i => WassDRCCP.Improved.distUnsafe S (ξ i)
  have hc : ModelRiskOT.Duality.AssumptionA1 c := by
    refine ⟨?_, ?_, ?_⟩
    · intro u v
      exact norm_nonneg _
    · exact (continuous_norm.comp (continuous_fst.sub continuous_snd)).lowerSemicontinuous
    · intro u v
      simp [c, norm_eq_zero, sub_eq_zero]
  have hμ : IsProbabilityMeasure μ := by
    rw [MeasureTheory.isProbabilityMeasure_iff]
    simp [μ, WassersteinDRO.Duality.empiricalDistribution]
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
    exact ENNReal.inv_mul_cancel hN0 ENNReal.coe_ne_top
  letI : IsProbabilityMeasure μ := hμ
  have hA : IsClosed (Sᶜ : Set E) := hS.isClosed_compl
  have hdual :=
    ModelRiskOT.WorstProb.eq_13 c hc μ θ hθ Sᶜ hA hC
  have hobj (lam : ℝ) (hlam : lam ∈ Set.Ici (0 : ℝ)) :
      ModelRiskOT.WorstProb.obj13 c μ θ Sᶜ lam =
        ENNReal.ofReal (ChenWasserstein.Attempt.scalarObj d θ lam) := by
    simpa [c, μ, d] using objective_eq_scalar ξ hN S θ lam hθ (by simpa using hlam)
  have hinf :
      (⨅ lam ∈ Set.Ici (0 : ℝ), ModelRiskOT.WorstProb.obj13 c μ θ Sᶜ lam) =
        (⨅ lam ∈ Set.Ici (0 : ℝ), ENNReal.ofReal (ChenWasserstein.Attempt.scalarObj d θ lam)) := by
    apply iInf_congr
    intro lam
    apply iInf_congr
    intro hlam
    exact hobj lam hlam
  rw [hdual, hinf]
  constructor
  · intro hprob
    have hd (i : Fin N) : 0 ≤ d i := by
      dsimp [d, WassDRCCP.Improved.distUnsafe]
      exact Metric.infDist_nonneg
    exact ChenWasserstein.Attempt.threshold_of_scalar_bound d ε θ
      hN hε hε1 hθ hd hprob
  · intro hthreshold
    have hd (i : Fin N) : 0 ≤ d i := by
      dsimp [d, WassDRCCP.Improved.distUnsafe]
      exact Metric.infDist_nonneg
    exact ChenWasserstein.Attempt.scalar_bound_of_threshold d ε θ
      hN hε hε1 hθ hd hthreshold
