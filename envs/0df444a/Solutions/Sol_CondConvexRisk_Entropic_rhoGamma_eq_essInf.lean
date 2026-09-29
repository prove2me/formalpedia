-- Prove2me | solution 1 for CondConvexRisk.Entropic.rhoGamma_eq_essInf
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:34:23.643227+00:00
-- url     : https://prove2.me/submissions/1e90eac7-662a-4735-96ee-dbf30aabc3ad

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

/-- An essentially bounded function has an a.e. bound on its absolute value. -/
lemma aux_rgei_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : MemLp X ⊤ P) : ∃ C : ℝ, ∀ᵐ ω ∂P, |X ω| ≤ C :=
  ⟨lpNorm X ⊤ P, by
    filter_upwards [ae_le_lpNorm_exponent_top hX] with ω hω
    simpa [Real.norm_eq_abs] using hω⟩

/-- Integrability of `exp(-γ X)` for essentially bounded `X`. -/
lemma aux_rgei_int {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (γ : ℝ) (hγ : 0 < γ) {X : Ω → ℝ} (hX : MemLp X ⊤ P) :
    Integrable (fun x => Real.exp (-γ * X x)) P := by
  obtain ⟨C, hC⟩ := aux_rgei_bound hX
  refine Integrable.of_bound
    (Real.continuous_exp.comp_aestronglyMeasurable (hX.1.const_mul (-γ))) (Real.exp (γ * C)) ?_
  filter_upwards [hC] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  have h1 : -X ω ≤ C := le_trans (neg_le_abs _) hω
  nlinarith

end CondConvexRisk.Entropic

open CondConvexRisk.Entropic

theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    IsEssInf P
        (fun Y : {Y : Ω → ℝ // MemLp Y ⊤ P ∧ StronglyMeasurable[m] Y ∧
            X + Y ∈ acceptanceSet m P γ} => fun ω => ((Y.1 ω : ℝ) : EReal))
        (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal)) ∧
    IsEssInf P
        (fun Y : {Y : Ω → ℝ // MemLp Y ⊤ P ∧ StronglyMeasurable[m] Y ∧
            (P[fun x => Real.exp (-γ * X x) | m]) ≤ᵐ[P] fun ω => Real.exp (γ * Y ω)} =>
          fun ω => ((Y.1 ω : ℝ) : EReal))
        (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal)) := by
  set c : Ω → ℝ := P[fun x => Real.exp (-γ * X x) | m] with hc_def
  set ρ : Ω → ℝ := rhoGamma m P γ X with hρ_def
  have hρc : ∀ ω, ρ ω = γ⁻¹ * Real.log (c ω) := fun ω => rfl
  obtain ⟨C, hC⟩ := aux_rgei_bound hX
  have hint := aux_rgei_int γ hγ hX
  -- bounds on the conditional expectation
  have hlow : ∀ᵐ ω ∂P, Real.exp (-(γ * C)) ≤ c ω := by
    have h := condExp_mono (m := m) (integrable_const (Real.exp (-(γ * C)))) hint
      (by
        filter_upwards [hC] with ω hω
        apply Real.exp_le_exp.2
        have h1 : X ω ≤ C := le_trans (le_abs_self _) hω
        nlinarith)
    rw [condExp_const hm] at h
    exact h
  have hup : ∀ᵐ ω ∂P, c ω ≤ Real.exp (γ * C) := by
    have h := condExp_mono (m := m) hint (integrable_const (Real.exp (γ * C)))
      (by
        filter_upwards [hC] with ω hω
        apply Real.exp_le_exp.2
        have h1 : -X ω ≤ C := le_trans (neg_le_abs _) hω
        nlinarith)
    rw [condExp_const hm] at h
    exact h
  have hpos : ∀ᵐ ω ∂P, 0 < c ω := by
    filter_upwards [hlow] with ω hω
    exact lt_of_lt_of_le (Real.exp_pos _) hω
  -- measurability and boundedness of ρ
  have hcsm : StronglyMeasurable[m] c := stronglyMeasurable_condExp
  have hρsm : StronglyMeasurable[m] ρ := by
    have : Measurable[m] (fun ω => γ⁻¹ * Real.log (c ω)) :=
      (Real.measurable_log.comp hcsm.measurable).const_mul γ⁻¹
    exact this.stronglyMeasurable
  have hρmem : MemLp ρ ⊤ P := by
    refine memLp_top_of_bound (hρsm.mono hm).aestronglyMeasurable C ?_
    filter_upwards [hlow, hup, hpos] with ω h1 h2 h3
    rw [Real.norm_eq_abs, hρc, abs_le]
    have l1 : -(γ * C) ≤ Real.log (c ω) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    have l2 : Real.log (c ω) ≤ γ * C := by
      have := Real.log_le_log h3 h2
      rwa [Real.log_exp] at this
    constructor
    · rw [le_inv_mul_iff₀ hγ]; linarith
    · rw [inv_mul_le_iff₀ hγ]; exact l2
  have hexpρ : ∀ᵐ ω ∂P, Real.exp (γ * ρ ω) = c ω := by
    filter_upwards [hpos] with ω h
    rw [hρc, ← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul, Real.exp_log h]
  -- pull-out property
  have key : ∀ Y : Ω → ℝ, StronglyMeasurable[m] Y → MemLp Y ⊤ P →
      P[fun x => Real.exp (-γ * (X + Y) x) | m] =ᵐ[P] fun ω => Real.exp (-γ * Y ω) * c ω := by
    intro Y hYsm hYmem
    obtain ⟨D, hD⟩ := aux_rgei_bound hYmem
    have hfun : (fun x => Real.exp (-γ * (X + Y) x)) =
        (fun x => Real.exp (-γ * Y x)) * (fun x => Real.exp (-γ * X x)) := by
      funext x
      simp only [Pi.add_apply, Pi.mul_apply, ← Real.exp_add]
      ring_nf
    rw [hfun]
    have hfsm : StronglyMeasurable[m] (fun x => Real.exp (-γ * Y x)) := by
      have : Measurable[m] (fun x => Real.exp (-γ * Y x)) :=
        Real.measurable_exp.comp (hYsm.measurable.const_mul (-γ))
      exact this.stronglyMeasurable
    have h := condExp_stronglyMeasurable_mul_of_bound hm hfsm hint (Real.exp (γ * D)) (by
      filter_upwards [hD] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have h1 : -Y ω ≤ D := le_trans (neg_le_abs _) hω
      nlinarith)
    filter_upwards [h] with ω hω
    rw [hω]
    rfl
  -- lower bound: condition `c ≤ exp(γ Y)` implies `ρ ≤ Y`
  have lower : ∀ Y : Ω → ℝ, (c ≤ᵐ[P] fun ω => Real.exp (γ * Y ω)) →
      (fun ω => ((ρ ω : ℝ) : EReal)) ≤ᵐ[P] fun ω => ((Y ω : ℝ) : EReal) := by
    intro Y hY
    filter_upwards [hY, hpos] with ω h1 h2
    rw [EReal.coe_le_coe_iff, hρc, inv_mul_le_iff₀ hγ]
    have := Real.log_le_log h2 h1
    rwa [Real.log_exp] at this
  -- set-1 condition implies set-2 condition
  have acc_to : ∀ Y : Ω → ℝ, StronglyMeasurable[m] Y → MemLp Y ⊤ P →
      X + Y ∈ acceptanceSet m P γ → (c ≤ᵐ[P] fun ω => Real.exp (γ * Y ω)) := by
    intro Y hYsm hYmem hacc
    filter_upwards [hacc.2, key Y hYsm hYmem] with ω h1 h2
    rw [h2] at h1
    have h3 : Real.exp (γ * Y ω) * (Real.exp (-γ * Y ω) * c ω) = c ω := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [← h3]
    calc Real.exp (γ * Y ω) * (Real.exp (-γ * Y ω) * c ω)
        ≤ Real.exp (γ * Y ω) * 1 :=
          mul_le_mul_of_nonneg_left (by simpa using h1) (Real.exp_pos _).le
      _ = Real.exp (γ * Y ω) := mul_one _
  -- ρ itself belongs to both sets
  have hρ2 : c ≤ᵐ[P] fun ω => Real.exp (γ * ρ ω) := by
    filter_upwards [hexpρ] with ω h
    rw [h]
  have hρ1 : X + ρ ∈ acceptanceSet m P γ := by
    refine ⟨hX.add hρmem, ?_⟩
    filter_upwards [key ρ hρsm hρmem, hexpρ, hpos] with ω h1 h2 h3
    rw [h1]
    have h4 : Real.exp (-γ * ρ ω) * c ω = 1 := by
      rw [← h2, ← Real.exp_add]
      ring_nf
      simp
    rw [h4]
    rfl
  have hZmeas : AEMeasurable (fun ω => ((ρ ω : ℝ) : EReal)) P :=
    (measurable_coe_real_ereal.comp (hρsm.mono hm).measurable).aemeasurable
  refine ⟨⟨hZmeas, ?_, ?_⟩, ⟨hZmeas, ?_, ?_⟩⟩
  · rintro ⟨Y, hYmem, hYsm, hacc⟩
    exact lower Y (acc_to Y hYsm hYmem hacc)
  · intro W _ hW
    exact hW ⟨ρ, hρmem, hρsm, hρ1⟩
  · rintro ⟨Y, hYmem, hYsm, hY⟩
    exact lower Y hY
  · intro W _ hW
    exact hW ⟨ρ, hρmem, hρsm, hρ2⟩
