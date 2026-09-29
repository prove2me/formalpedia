-- Prove2me | solution 1 for CondConvexRisk.Representation.continuousFromAbove_of_representable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:39:31.198544+00:00
-- url     : https://prove2.me/submissions/9974e328-3e5b-4fc6-8f30-9cd53637818f

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- Essentially bounded functions stay integrable under an absolutely continuous finite
measure. -/
lemma aux_cfa_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P Q : Measure Ω}
    [IsFiniteMeasure Q] (hQP : Q ≪ P) {X : Ω → ℝ} (hX : MemLp X ⊤ P) : Integrable X Q := by
  have h : MemLp X ⊤ Q := by
    refine ⟨hX.1.mono_ac hQP, ?_⟩
    rw [eLpNorm_exponent_top]
    exact (eLpNormEssSup_mono_measure _ hQP).trans_lt (by
      have := hX.2
      rwa [eLpNorm_exponent_top] at this)
  exact h.integrable le_top

/-- Conditional monotone convergence (only the needed inequality): the pointwise infimum of
`E_Q(X_n | G)` is a.s. below `E_Q(Y | G)` when `X_n ↘ Y`. -/
lemma aux_cfa_core {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) (Q : Measure Ω) [IsFiniteMeasure Q] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hXi : ∀ n, Integrable (X n) Q) (hYi : Integrable Y Q)
    (hconv : ∀ᵐ ω ∂Q, Antitone (fun n => X n ω) ∧ Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    (fun ω => ⨅ n, (Q[X n | m]) ω) ≤ᵐ[Q] Q[Y | m] := by
  set f : ℕ → Ω → ℝ := fun n => Q[X n | m] with hf_def
  set h : Ω → ℝ := Q[Y | m] with hh_def
  set g : Ω → ℝ := fun ω => ⨅ n, f n ω with hg_def
  have hYX : ∀ n, Y ≤ᵐ[Q] X n := fun n => by
    filter_upwards [hconv] with ω hω
    exact hω.1.le_of_tendsto hω.2 n
  have hhf : ∀ n, h ≤ᵐ[Q] f n := fun n => condExp_mono hYi (hXi n) (hYX n)
  have hgle : ∀ n, g ≤ᵐ[Q] f n := fun n => by
    filter_upwards [ae_all_iff.2 hhf] with ω hω
    exact ciInf_le ⟨h ω, by rintro _ ⟨k, rfl⟩; exact hω k⟩ n
  have hhg : h ≤ᵐ[Q] g := by
    filter_upwards [ae_all_iff.2 hhf] with ω hω
    exact le_ciInf hω
  have hgm : Measurable g :=
    Measurable.iInf (fun n => (stronglyMeasurable_condExp.mono hm).measurable)
  have hhi : Integrable h Q := integrable_condExp
  have hf0i : Integrable (f 0) Q := integrable_condExp
  have hgi : Integrable g Q := by
    refine Integrable.mono' (hhi.abs.add hf0i.abs) hgm.aestronglyMeasurable ?_
    filter_upwards [hhg, hgle 0] with ω h1 h2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le (h ω)
      have := abs_nonneg (f 0 ω)
      simp only [Pi.add_apply]
      linarith
    · have := le_abs_self (f 0 ω)
      have := abs_nonneg (h ω)
      simp only [Pi.add_apply]
      linarith
  have hint_le : ∀ n, ∫ ω, g ω ∂Q ≤ ∫ ω, X n ω ∂Q := fun n => by
    have h1 : ∫ ω, g ω ∂Q ≤ ∫ ω, f n ω ∂Q := integral_mono_ae hgi integrable_condExp (hgle n)
    have h2 : ∫ ω, f n ω ∂Q = ∫ ω, X n ω ∂Q := integral_condExp hm
    linarith
  have htend : Tendsto (fun n => ∫ ω, X n ω ∂Q) atTop (𝓝 (∫ ω, Y ω ∂Q)) :=
    integral_tendsto_of_tendsto_of_antitone hXi hYi (hconv.mono fun ω hω => hω.1)
      (hconv.mono fun ω hω => hω.2)
  have hgY : ∫ ω, g ω ∂Q ≤ ∫ ω, Y ω ∂Q := ge_of_tendsto' htend hint_le
  have hhY : ∫ ω, h ω ∂Q = ∫ ω, Y ω ∂Q := integral_condExp hm
  have heq : h =ᵐ[Q] g :=
    (integral_eq_iff_of_ae_le hhi hgi hhg).1
      (le_antisymm (integral_mono_ae hhi hgi hhg) (by linarith))
  filter_upwards [heq] with ω hω
  exact hω.ge

end CondConvexRisk.Representation

open CondConvexRisk.Representation
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (hrep : IsRepresentable m P ρ) :
    IsContinuousFromAbove P ρ := by
  intro X Y hX hY hconv
  obtain ⟨α, hαm, hess⟩ := hrep
  -- monotonicity facts
  have hmono : ∀ n, ρ (X n) ≤ᵐ[P] ρ (X (n + 1)) := fun n => by
    refine hρ.monotone (X (n + 1)) (X n) (hX (n + 1)) (hX n) ?_
    filter_upwards [hconv] with ω hω
    exact hω.1 (Nat.le_succ n)
  have hbd : ∀ n, ρ (X n) ≤ᵐ[P] ρ Y := fun n => by
    refine hρ.monotone Y (X n) hY (hX n) ?_
    filter_upwards [hconv] with ω hω
    exact hω.1.le_of_tendsto hω.2 n
  have hmeas : ∀ n, Measurable (ρ (X n)) := fun n =>
    ((hρ.stronglyMeasurable (X n) (hX n)).mono hm).measurable
  set S : Ω → ℝ := fun ω => ⨆ n, ρ (X n) ω with hS_def
  have hSm : Measurable S := Measurable.iSup hmeas
  have hleS : ∀ᵐ ω ∂P, ∀ n, ρ (X n) ω ≤ S ω := by
    filter_upwards [ae_all_iff.2 hbd] with ω hω n
    exact le_ciSup ⟨ρ Y ω, by rintro _ ⟨k, rfl⟩; exact hω k⟩ n
  -- the key step: each member of the representing family for `Y` is below `S`
  have hkey : ∀ Q : PG m P, reprFamily m P α Y Q ≤ᵐ[P] fun ω => ((S ω : ℝ) : EReal) := by
    intro Q
    obtain ⟨hQprob, hQP, hQeq⟩ := Q.2
    have : IsProbabilityMeasure Q.1 := hQprob
    have hXi : ∀ n, Integrable (X n) Q.1 := fun n => aux_cfa_integrable hQP (hX n)
    have hYi : Integrable Y Q.1 := aux_cfa_integrable hQP hY
    have hcore := aux_cfa_core m hm Q.1 X Y hXi hYi (hQP.ae_le hconv)
    -- transfer to `P`
    have hgm : Measurable[m] (fun ω => ⨅ n, (Q.1[X n | m]) ω) :=
      Measurable.iInf (fun n => stronglyMeasurable_condExp.measurable)
    have hhm : Measurable[m] (Q.1[Y | m]) := stronglyMeasurable_condExp.measurable
    have hcoreP : ∀ᵐ ω ∂P, (⨅ n, (Q.1[X n | m]) ω) ≤ (Q.1[Y | m]) ω := by
      have hcore' : ∀ᵐ ω ∂Q.1, (⨅ n, (Q.1[X n | m]) ω) ≤ (Q.1[Y | m]) ω := hcore
      rw [ae_iff] at hcore' ⊢
      have hset : MeasurableSet[m]
          {ω | ¬ (⨅ n, (Q.1[X n | m]) ω) ≤ (Q.1[Y | m]) ω} :=
        (measurableSet_le hgm hhm).compl
      rw [← hQeq _ hset]
      exact hcore'
    have hrepn : ∀ n, ∀ᵐ ω ∂P, reprFamily m P α (X n) Q ω ≤ ((ρ (X n) ω : ℝ) : EReal) :=
      fun n => (hess (X n) (hX n)).2.1 Q
    filter_upwards [hcoreP, ae_all_iff.2 hrepn, hleS] with ω h1 h2 h3
    simp only [reprFamily] at h2 ⊢
    rcases eq_top_or_lt_top (α Q ω) with hα | hα
    · rw [hα]
      simp
    · lift α Q ω to NNReal using hα.ne with r hr
      have hr' : ((r : ENNReal) : EReal) = ((r : ℝ) : EReal) := rfl
      rw [hr'] at h2 ⊢
      have h2' : ∀ n, -((Q.1[X n | m]) ω) - (r : ℝ) ≤ ρ (X n) ω := by
        intro n
        have := h2 n
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at this
        exact this
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      have h4 : -S ω - (r : ℝ) ≤ ⨅ n, (Q.1[X n | m]) ω := by
        apply le_ciInf
        intro n
        have := h2' n
        have := h3 n
        linarith
      show -((Q.1[Y | m]) ω) - (r : ℝ) ≤ S ω
      linarith
  -- apply the essential supremum property for `Y`
  have hYS : ∀ᵐ ω ∂P, ρ Y ω ≤ S ω := by
    have := (hess Y hY).2.2 (fun ω => ((S ω : ℝ) : EReal))
      (measurable_coe_real_ereal.comp hSm).aemeasurable hkey
    filter_upwards [this] with ω hω
    exact EReal.coe_le_coe_iff.1 hω
  filter_upwards [ae_all_iff.2 hmono, ae_all_iff.2 hbd, hYS] with ω h1 h2 h3
  have hmon : Monotone (fun n => ρ (X n) ω) := monotone_nat_of_le_succ h1
  have hbdd : BddAbove (Set.range fun n => ρ (X n) ω) :=
    ⟨ρ Y ω, by rintro _ ⟨k, rfl⟩; exact h2 k⟩
  refine ⟨hmon, ?_⟩
  have hSY : S ω = ρ Y ω := le_antisymm (ciSup_le h2) h3
  have := tendsto_atTop_ciSup hmon hbdd
  rw [← hSY]
  exact this
