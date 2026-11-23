-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.goodPI_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:26.392278+00:00
-- url     : https://prove2.me/submissions/9fe6501d-7e45-4a02-8a52-e1b289771eca

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_exists_common_eigenvector
import Theorems.Thm_CompanionTheory_D_gk_admitted_eq_top_of_minimal
import Theorems.Thm_CompanionTheory_D_gk_admitted_integral_mem_of_forall_mem
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (hS : SmallPI) : GoodPI := by
  intro G _ _ _ _ _ K _ _ _ μ _ _ st S hKS e d M he hfin hM ι _ _ ρ hρ E hE g
  obtain ⟨φ, hφc, hφ⟩ := hfin
  obtain ⟨h, hinj, htri⟩ := hρ.tri
  rw [← LinearMap.ker_eq_top]
  refine eq_top_of_minimal (fun x => ρ x) (fun x => ⟨st x, hρ.adj x⟩) _ fun W hW0 hWs hmin => ?_
  obtain ⟨w₀, hw₀, hne, heig⟩ := exists_common_eigenvector h hinj W hW0
  have hcont : Continuous fun x : K => ρ x *ᵥ w₀ :=
    (hρ.cont.comp continuous_subtype_val).matrix_mulVec continuous_const
  have hint : ∀ i, Integrable (fun x : K => φ i x • (ρ x *ᵥ w₀)) μ := fun i =>
    ((hφc i).smul hcont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set θ : Fin d → ι → ℂ := fun i => ∫ x : K, φ i x • (ρ x *ᵥ w₀) ∂μ with hθ
  set U : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range fun k : K => ρ k *ᵥ w₀) with hU
  have hUW : U = W := by
    refine hmin U ?_ ?_ ?_
    · intro hb
      have : w₀ ∈ U := Submodule.subset_span ⟨1, by simp⟩
      rw [hb, Submodule.mem_bot] at this
      exact hne this
    · intro x
      have : U ≤ U.comap (Matrix.toLin' (ρ x)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        obtain ⟨k', hk', s, hs, hks⟩ := hKS (x * k)
        obtain ⟨c, hc⟩ := heig (ρ s) (htri s hs) (hWs s)
        have e1 : ρ x *ᵥ (ρ k *ᵥ w₀) = c • (ρ k' *ᵥ w₀) := by
          rw [mulVec_mulVec, ← map_mul, hks, map_mul, ← mulVec_mulVec, hc, mulVec_smul]
        show Matrix.toLin' (ρ x) (ρ k *ᵥ w₀) ∈ U
        rw [Matrix.toLin'_apply, e1]
        exact U.smul_mem _ (Submodule.subset_span ⟨⟨k', hk'⟩, rfl⟩)
      intro w hw
      simpa using this hw
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact hWs k w₀ hw₀
  set Y : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range θ) with hY
  have hYW : Y ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact integral_mem_of_forall_mem μ W _ (hint i) fun x => W.smul_mem _ (hWs x w₀ hw₀)
  have hEY : W ≤ Y.comap E := by
    rw [← hUW]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc⟩ := hφ k
    have e1 : E (ρ k *ᵥ w₀) = ∑ i, c i • θ i := by
      rw [hE, ← integral_mul_right_eq_self _ k⁻¹]
      have : ∀ x : K, e (x * k⁻¹) • (ρ ((x * k⁻¹ : K) : G) *ᵥ (ρ k *ᵥ w₀)) =
          ∑ i, c i • (φ i x • (ρ x *ᵥ w₀)) := by
        intro x
        rw [mulVec_mulVec, ← map_mul, hc, Finset.sum_smul]
        simp [smul_smul]
      simp only [this]
      rw [integral_finsetSum (f := fun i (x : K) => c i • (φ i x • (ρ x *ᵥ w₀))) _
        fun i _ => (hint i).smul (c i)]
      simp only [integral_smul, hθ]
    show E (ρ k *ᵥ w₀) ∈ Y
    rw [e1]
    exact Y.sum_mem fun i _ => Y.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrk : Module.finrank ℂ Y ≤ d := by
    have := finrank_range_le_card (R := ℂ) θ
    rwa [Fintype.card_fin] at this
  intro w hw
  exact hS (ι → ℂ) W Y hYW E (fun w hw => hEY hw) M
    (lt_of_le_of_lt (Nat.pow_le_pow_left hrk 2) hM) _ (fun i w hw => by simpa using hWs (g i) w hw) w hw
end CompanionTheory.D.gk.admitted
