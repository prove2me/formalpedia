-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.inj_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:43.438095+00:00
-- url     : https://prove2.me/submissions/cf733f94-bb1c-4f85-8bc7-e99fec2c0534

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_hw_in_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {W : Submodule K V} (hW : G.Stable W)
    (hWf : G.FinW W) (hvW : v ∈ W) (Φ : V →ₗ[K] V) (κ : Fin r → ℤ)
    (hΦE : ∀ x ∈ G.gS {v}, ∀ a b, a < b → Φ (G.E a b x) = G.E a b (Φ x))
    (hΦc : ∀ x ∈ G.gS {v}, ∀ ν, Φ (G.comp ν x) = G.comp (ν + κ) (Φ x)) (hΦv : Φ v ≠ 0) :
    ∀ x ∈ G.gS {v}, Φ x = 0 → x = 0 := by
  intro x hx hΦx
  by_contra hx0
  have hgr : G.Graded (G.gS {v}) := G.graded_of (G.gS_stable {v})
  let K0 : Submodule K V :=
    { carrier := {y | y ∈ G.gS {v} ∧ Φ y = 0}
      add_mem' := fun {y z} hy hz => ⟨(G.gS {v}).add_mem hy.1 hz.1, by rw [map_add, hy.2, hz.2, add_zero]⟩
      zero_mem' := ⟨(G.gS {v}).zero_mem, map_zero Φ⟩
      smul_mem' := fun c y hy => ⟨(G.gS {v}).smul_mem c hy.1, by rw [map_smul, hy.2, smul_zero]⟩ }
  have hmemK : ∀ y, y ∈ K0 ↔ y ∈ G.gS {v} ∧ Φ y = 0 := fun y => Iff.rfl
  have hgS_W : G.gS {v} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hvW) hW
  obtain ⟨S, hS⟩ := hWf
  have hKg : G.Graded K0 := by
    intro ν y hy
    rw [hmemK] at hy ⊢
    exact ⟨hgr ν y hy.1, by rw [hΦc y hy.1, hy.2, map_zero]⟩
  have hKr : G.Raising K0 := by
    intro a b hab y hy
    rw [hmemK] at hy ⊢
    exact ⟨G.gS_stable {v} a b y hy.1, by rw [hΦE y hy.1 a b hab, hy.2, map_zero]⟩
  have hKf : G.FinW K0 := ⟨S, fun y hy ν hν => hS y (hgS_W ((hmemK y).mp hy).1) ν hν⟩
  have hnle : ¬ K0 ≤ ⊥ := by
    intro hle
    exact hx0 ((Submodule.mem_bot K).mp (hle ((hmemK x).mpr ⟨hx, hΦx⟩)))
  obtain ⟨y, hyK, hy0, μ, hyw, hyr⟩ := G.exists_hwmod hKg hKr hKf hnle
  rw [hmemK] at hyK
  have hyHW : G.IsHW μ y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  obtain ⟨_, c, hc⟩ := G.hw_in_gS hv hW ⟨S, hS⟩ hvW hyK.1 hyHW hy0'
  have h1 := hyK.2
  rw [hc, map_smul] at h1
  rcases smul_eq_zero.mp h1 with h2 | h2
  · apply hy0'
    rw [hc, h2, zero_smul]
  · exact hΦv h2
end Formalism.GM.DimensionMonotonicity.GlW
