-- Prove2me | solution 1 for ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d0f044f0-7ba8-5977-8a63-9281650b8bff

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace ProdMeasurable

open Topology

theorem measurable_of_continuous {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (f : X × Y → ℂ) (hf : Continuous f) : Measurable f := by

  let gens : Set C(X × Y, ℂ) :=
    {F | ∃ g : C(X, ℂ), F = g.comp ⟨Prod.fst, continuous_fst⟩} ∪ {F | ∃ h : C(Y, ℂ), F = h.comp ⟨Prod.snd, continuous_snd⟩}
  let A : StarSubalgebra ℂ C(X × Y, ℂ) := StarAlgebra.adjoin ℂ gens
  have hsep : A.SeparatesPoints := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hne
    by_cases hx : x₁ = x₂
    · subst hx
      have hy : y₁ ≠ y₂ := fun h => hne (by rw [h])

      obtain ⟨h, h1, h2⟩ : ∃ h : C(Y, ℝ), h y₁ = 0 ∧ h y₂ = 1 := by
        obtain ⟨h, h1, h2, -⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := y₁))
          (isClosed_singleton (x := y₂)) (Set.disjoint_singleton.mpr hy)
        exact ⟨h, h1 rfl, h2 rfl⟩
      let hC : C(Y, ℂ) := ⟨fun y => ((h y : ℝ) : ℂ), Complex.continuous_ofReal.comp h.continuous⟩
      refine ⟨hC.comp ⟨Prod.snd, continuous_snd⟩, ⟨_, StarAlgebra.subset_adjoin ℂ gens (Or.inr ⟨hC, rfl⟩), rfl⟩, ?_⟩
      show ¬ ((h y₁ : ℝ) : ℂ) = ((h y₂ : ℝ) : ℂ)
      rw [h1, h2]; norm_num
    · obtain ⟨g, g1, g2⟩ : ∃ g : C(X, ℝ), g x₁ = 0 ∧ g x₂ = 1 := by
        obtain ⟨g, g1, g2, -⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := x₁))
          (isClosed_singleton (x := x₂)) (Set.disjoint_singleton.mpr hx)
        exact ⟨g, g1 rfl, g2 rfl⟩
      let gC : C(X, ℂ) := ⟨fun x => ((g x : ℝ) : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
      refine ⟨gC.comp ⟨Prod.fst, continuous_fst⟩, ⟨_, StarAlgebra.subset_adjoin ℂ gens (Or.inl ⟨gC, rfl⟩), rfl⟩, ?_⟩
      show ¬ ((g x₁ : ℝ) : ℂ) = ((g x₂ : ℝ) : ℂ)
      rw [g1, g2]; norm_num
  have hdense : A.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep

  have hmeasA : ∀ F ∈ A, Measurable (F : X × Y → ℂ) := by
    intro F hF
    refine StarAlgebra.adjoin_induction (R := ℂ) (s := gens)
      (p := fun (F : C(X × Y, ℂ)) (_ : F ∈ StarAlgebra.adjoin ℂ gens) => Measurable (F : X × Y → ℂ)) ?_ ?_ ?_ ?_ ?_ hF
    · rintro F (⟨g, rfl⟩ | ⟨h, rfl⟩)
      · exact g.continuous.measurable.comp measurable_fst
      · exact h.continuous.measurable.comp measurable_snd
    · intro r; exact measurable_const
    · intro F G _ _ hF hG; exact hF.add hG
    · intro F G _ _ hF hG; exact hF.mul hG
    · intro F _ hF
      show Measurable fun p => star (F p)
      exact (Complex.continuous_conj.measurable).comp hF

  let fC : C(X × Y, ℂ) := ⟨f, hf⟩
  have hfcl : fC ∈ A.topologicalClosure := by rw [hdense]; trivial
  have hfcl' : fC ∈ closure (A : Set C(X × Y, ℂ)) := hfcl
  obtain ⟨u, huA, hu⟩ := mem_closure_iff_seq_limit.mp hfcl'
  have hpt : Filter.Tendsto (fun n => (u n : X × Y → ℂ)) Filter.atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro p
    exact ((ContinuousEvalConst.continuous_eval_const p).tendsto fC).comp hu
  exact measurable_of_tendsto_metrizable (fun n => hmeasA _ (huA n)) hpt

end ProdMeasurable

namespace AvgConvBounds

theorem exists_bound {C : Type*} [TopologicalSpace C] [CompactSpace C] [Nonempty C] {w : C → ℂ} (hw : Continuous w) :
    ∃ M : ℝ, ∀ c : C, ‖w c‖ ≤ M := by
  obtain ⟨c₀, -, hc₀⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hw.norm.continuousOn
  exact ⟨‖w c₀‖, fun c => hc₀ (Set.mem_univ c)⟩

end AvgConvBounds

namespace AvgConv

theorem hasCompactSupport_of_compactSpace' {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Zero Y] [TopologicalSpace Y]
    (f : X → Y) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _)

variable {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
  [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v)

include hSb hSc

omit hSb in
theorem continuous_integrand (w : C → ℂ) (hw : Continuous w) (v : H) : Continuous fun c : C => w c • S c v :=
  hw.smul (hSc v)

theorem integrable_integrand (w : C → ℂ) (hw : Continuous w) (v : H) : Integrable (fun c : C => w c • S c v) μ :=
  (continuous_integrand S hSc w hw v).integrable_of_hasCompactSupport (hasCompactSupport_of_compactSpace' _)

theorem apply_integral (w : C → ℂ) (hw : Continuous w) (v : H) (d : C) :
    S d (∫ c, w c • S c v ∂μ) = ∫ c, w (d⁻¹ * c) • S c v ∂μ := by
  rw [← ContinuousLinearMap.integral_comp_comm (S d) (integrable_integrand μ S B hSb hSc w hw v)]
  have h1 : (fun c => S d (w c • S c v)) = fun c => (fun c' => w (d⁻¹ * c') • S c' v) (d * c) := by
    funext c
    simp only [ContinuousLinearMap.map_smul, inv_mul_cancel_left]
    congr 1
    rw [map_mul]; rfl
  rw [h1]
  exact integral_mul_left_eq_self (fun c' => w (d⁻¹ * c') • S c' v) d

theorem comp_eq (w₁ w₂ : C → ℂ) (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) (A₁ A₂ A₁₂ : H →L[ℂ] H)
    (h₁ : ∀ v : H, A₁ v = ∫ c, w₁ c • S c v ∂μ) (h₂ : ∀ v : H, A₂ v = ∫ c, w₂ c • S c v ∂μ)
    (h₁₂ : ∀ v : H, A₁₂ v = ∫ c, (∫ d, w₁ d * w₂ (d⁻¹ * c) ∂μ) • S c v ∂μ) :
    A₁.comp A₂ = A₁₂ := by
  ext v
  rw [ContinuousLinearMap.comp_apply, h₁₂, h₁]

  have step : ∀ d, w₁ d • S d (A₂ v) = ∫ c, (w₁ d * w₂ (d⁻¹ * c)) • S c v ∂μ := by
    intro d
    rw [h₂, apply_integral μ S B hSb hSc w₂ hw₂ v d, ← integral_smul]
    congr 1; funext c; rw [smul_smul]
  simp_rw [step]

  have ha : Measurable fun p : C × C => w₁ p.1 * w₂ (p.1⁻¹ * p.2) :=
    ProdMeasurable.measurable_of_continuous _
      ((hw₁.comp continuous_fst).mul (hw₂.comp ((continuous_fst.inv).mul continuous_snd)))
  have hb : StronglyMeasurable fun p : C × C => S p.2 v :=
    (((hSc v).stronglyMeasurable_of_hasCompactSupport (hasCompactSupport_of_compactSpace' _)).comp_measurable
      measurable_snd)
  obtain ⟨M₁, hM₁⟩ := AvgConvBounds.exists_bound hw₁
  obtain ⟨M₂, hM₂⟩ := AvgConvBounds.exists_bound hw₂
  have hB : 0 ≤ B := (norm_nonneg _).trans (hSb 1)
  have hI : Integrable (Function.uncurry fun d c => (w₁ d * w₂ (d⁻¹ * c)) • S c v) (μ.prod μ) := by
    refine Integrable.mono' (integrable_const (M₁ * M₂ * (B * ‖v‖)))
      (ha.stronglyMeasurable.smul hb).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    show ‖(w₁ p.1 * w₂ (p.1⁻¹ * p.2)) • S p.2 v‖ ≤ M₁ * M₂ * (B * ‖v‖)
    rw [norm_smul, norm_mul]
    have h0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 1)
    gcongr
    · exact mul_nonneg (h0.trans (le_refl _)) ((norm_nonneg _).trans (hM₂ 1)) |>.trans (le_refl _) |> fun _ => by positivity
    · exact hM₁ _
    · exact hM₂ _
    · exact (S p.2).le_of_opNorm_le (hSb _) v
  rw [integral_integral_swap hI]
  congr 1; funext c
  rw [← integral_smul_const]

theorem one_clause (A : H →L[ℂ] H) (hA : ∀ v : H, A v = ∫ c, S c v ∂μ) :
    (∀ v : H, A v = v ↔ ∀ c : C, S c v = v) ∧ A.comp A = A := by
  have hA' : ∀ v : H, A v = ∫ c, (fun _ => (1 : ℂ)) c • S c v ∂μ := fun v => by simp [hA]
  have hfix : ∀ (v : H) (d : C), S d (A v) = A v := by
    intro v d
    rw [hA' v, apply_integral μ S B hSb hSc (fun _ => (1 : ℂ)) continuous_const v d]
  have hconst : ∀ v : H, (∀ c : C, S c v = v) → A v = v := by
    intro v hv
    rw [hA]
    simp_rw [hv]
    simp
  refine ⟨fun v => ⟨fun h c => by rw [← h]; exact hfix v c, hconst v⟩, ?_⟩
  ext v
  exact hconst (A v) (hfix v)

end AvgConv

theorem solution
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v) :
    (∀ (w₁ w₂ : C → ℂ), Continuous w₁ → Continuous w₂ →
      ∀ (A₁ A₂ A₁₂ : H →L[ℂ] H),
        (∀ v : H, A₁ v = ∫ c, (w₁ c) • (S c v) ∂μ) → (∀ v : H, A₂ v = ∫ c, (w₂ c) • (S c v) ∂μ) →
        (∀ v : H, A₁₂ v = ∫ c, (∫ d, w₁ d * w₂ (d⁻¹ * c) ∂μ) • (S c v) ∂μ) →
        A₁.comp A₂ = A₁₂) ∧
    (∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ c, S c v ∂μ) →
      (∀ v : H, A v = v ↔ ∀ c : C, S c v = v) ∧ A.comp A = A)  :=
  ⟨fun w₁ w₂ hw₁ hw₂ A₁ A₂ A₁₂ h₁ h₂ h₁₂ => AvgConv.comp_eq μ S B hSb hSc w₁ w₂ hw₁ hw₂ A₁ A₂ A₁₂ h₁ h₂ h₁₂,
    fun A hA => AvgConv.one_clause μ S B hSb hSc A hA⟩

end S_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
end P2MW
export P2MW.S_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution (solution)
