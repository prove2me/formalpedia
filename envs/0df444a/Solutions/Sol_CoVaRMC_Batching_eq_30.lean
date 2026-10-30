-- Prove2me | solution 1 for CoVaRMC.Batching.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:25:53.989986+00:00
-- url     : https://prove2.me/submissions/a0dbe5e9-89c3-46d8-a134-38b1cdc485ed

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Theorems.Thm_CoVaRMC_Batching_lemma_3
import Theorems.Thm_CoVaRMC_Batching_cond_density

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaREq30Aux

lemma card_le_iff {k : ℕ} (w : Fin k → ℝ) (j : Fin k) (y : ℝ) :
    (j : ℕ) + 1 ≤ (Finset.univ.filter fun i => w i ≤ y).card ↔ w (Tuple.sort w j) ≤ y := by
  set σ := Tuple.sort w
  have hmono : Monotone (w ∘ σ) := Tuple.monotone_sort w
  constructor
  · intro hcard
    by_contra hlt
    push Not at hlt
    have hsub : (Finset.univ.filter fun i => w i ≤ y) ⊆ (Finset.Iio j).image σ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_image]
      refine ⟨σ.symm i, ?_, by simp⟩
      rw [Finset.mem_Iio]
      by_contra hge
      push Not at hge
      have := hmono hge
      simp only [Function.comp, Equiv.apply_symm_apply] at this
      linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iio] at this
    omega
  · intro hj
    have hsub : (Finset.Iic j).image σ ⊆ (Finset.univ.filter fun i => w i ≤ y) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_Iic] at hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hmono hl).trans hj
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic] at this
    omega

open CoVaRMC.Batching in
/-- `Ŷ^BE ≤ y ↔ F̂_k(y) ≥ β`. -/
lemma ybe_le_iff {Ω : Type*} (S : ℕ × ℕ → Ω → ℝ × ℝ) (α β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (k m : ℕ) (hk : 0 < k) (ω : Ω) (y : ℝ) :
    YBE S α β k m ω ≤ y ↔ β ≤ FkHat S α k m y ω := by
  set w : Fin k → ℝ := fun i => Yhat S α m i ω with hw
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < ⌈β * k⌉₊ := Nat.ceil_pos.mpr (mul_pos hβ.1 hkR)
  have hle : ⌈β * k⌉₊ ≤ k := Nat.ceil_le.mpr (by nlinarith [hβ.2])
  have hr : ((rankIdx β k hk : Fin k) : ℕ) = ⌈β * k⌉₊ - 1 := by
    simp only [rankIdx]; omega
  have hY : YBE S α β k m ω = w (Tuple.sort w (rankIdx β k hk)) := by
    simp only [YBE, dif_pos hk, ImpactInvesting.Portfolio.orderStat]
    rfl
  rw [hY]
  simp only [FkHat, empCDF]
  rw [← card_le_iff w (rankIdx β k hk) y, hr]
  rw [show β ≤ (k : ℝ)⁻¹ * ((Finset.univ.filter fun i => w i ≤ y).card : ℝ) ↔
      β * k ≤ ((Finset.univ.filter fun i => w i ≤ y).card : ℝ) by
    rw [inv_mul_eq_div, le_div_iff₀ hkR]]
  rw [← Nat.ceil_le]
  omega

end CoVaREq30Aux

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop)
    (t : ℝ) :
    (∀ ν, {ω | √(k ν : ℝ) / Aconst D β v c * (YBE S α β (k ν) (m ν) ω - c) ≤ t} =
        {ω | β ≤ FkHat S α (k ν) (m ν) (yk c (Aconst D β v c) t (k ν)) ω}) ∧
    (∀ ν, 0 < sigmaHat P S α (m ν) (yk c (Aconst D β v c) t (k ν)) →
      {ω | β ≤ FkHat S α (k ν) (m ν) (yk c (Aconst D β v c) t (k ν)) ω} =
        {ω | cmk P S α β c (Aconst D β v c) t (k ν) (m ν) ≤
          √(k ν : ℝ) / sigmaHat P S α (m ν) (yk c (Aconst D β v c) t (k ν)) *
            (FkHat S α (k ν) (m ν) (yk c (Aconst D β v c) t (k ν)) ω - pHat P S α (m ν) (yk c (Aconst D β v c) t (k ν)))}) ∧
    Tendsto (fun ν => sigmaHat P S α (m ν) (yk c (Aconst D β v c) t (k ν))) atTop (𝓝 √(β * (1 - β))) := by
  have hA1' := hA1
  obtain ⟨h𝒳o, hv𝒳, h𝒴o, hc𝒴, -, -, -, -, -⟩ := hA1'
  have hcd := CoVaRMC.Batching.cond_density D Fc v c 𝒳 𝒴 hFc hA1 v hv𝒳 c hc𝒴
  set A := Aconst D β v c with hAdef
  have hApos : 0 < A := by
    simp only [hAdef, Aconst]
    exact div_pos (Real.sqrt_pos.mpr (mul_pos hβ.1 (by linarith [hβ.2]))) hcd.2
  refine ⟨?_, ?_, ?_⟩
  · intro ν
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [← CoVaREq30Aux.ybe_le_iff S α β hβ (k ν) (m ν) (hk0 ν) ω]
    have hkR : (0 : ℝ) < √(k ν : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk0 ν)
    simp only [yk]
    rw [div_mul_eq_mul_div, div_le_iff₀ hApos, ← sub_le_iff_le_add', le_div_iff₀ hkR, mul_comm]
  · intro ν hσ
    ext ω
    simp only [Set.mem_ofPred_eq, cmk]
    have hkR : (0 : ℝ) < √(k ν : ℝ) / sigmaHat P S α (m ν) (yk c A t (k ν)) :=
      div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hk0 ν)) hσ
    rw [mul_le_mul_iff_right₀ hkR]
    constructor <;> intro h <;> linarith
  · -- `y_k → c`
    have hyk : Tendsto (fun ν => yk c A t (k ν)) atTop (𝓝 c) := by
      simp only [yk]
      have h1 : Tendsto (fun ν => √(k ν : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hk)
      have h2 : Tendsto (fun ν => t * A / √(k ν : ℝ)) atTop (𝓝 0) :=
        h1.const_div_atTop _
      simpa using h2.const_add c
    -- `F(y_k | v) → β`
    have hF : Tendsto (fun ν => Fc (yk c A t (k ν)) v) atTop (𝓝 β) := by
      rw [← hc]
      exact (hcd.1.continuousAt.tendsto).comp hyk
    -- bias → 0
    obtain ⟨C, hC⟩ := CoVaRMC.Batching.lemma_3 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM hM1 hM2
      P S hSm hSi hSl
    have hev1 : ∀ᶠ ν in atTop, ∀ y ∈ 𝒴, |pHat P S α (m ν) y - Fc y v| ≤ C / m ν :=
      hm.eventually hC
    have hev2 : ∀ᶠ ν in atTop, yk c A t (k ν) ∈ 𝒴 := hyk.eventually (h𝒴o.mem_nhds hc𝒴)
    have hCm : Tendsto (fun ν => C / (m ν : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hm)
    have hp : Tendsto (fun ν => pHat P S α (m ν) (yk c A t (k ν))) atTop (𝓝 β) := by
      have hdiff : Tendsto (fun ν => pHat P S α (m ν) (yk c A t (k ν)) - Fc (yk c A t (k ν)) v)
          atTop (𝓝 0) := by
        rw [tendsto_zero_iff_abs_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hCm
        filter_upwards [hev1, hev2] with ν h1 h2
        exact h1 _ h2
      simpa using hdiff.add hF
    simp only [sigmaHat]
    exact ((hp.mul (tendsto_const_nhds.sub hp)).sqrt)
