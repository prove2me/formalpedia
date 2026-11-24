-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.hw_IsoW_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:17.275933+00:00
-- url     : https://prove2.me/submissions/e76ed4b5-6eaf-4bf6-990b-f8acbcc75478

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_IsoW_le
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_IsoW_le_iSup
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_cprod_mod
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_gen_kill
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la mu : Fin n → ℤ}
    (hne : mu ≠ la) {x : V} (hx : G.IsHW la x) (hxI : x ∈ IsoW G W mu) : x = 0 := by
  by_contra hx0
  have hxw : G.comp la x = x ∧ ∀ a b, a < b → G.E a b x = 0 := hx
  have hbot : G.Stable (⊥ : Submodule K V) := by
    intro a b y hy
    rw [Submodule.mem_bot] at hy ⊢
    rw [hy, map_zero]
  have hr : ∀ a b, a < b → G.E a b x ∈ (⊥ : Submodule K V) := fun a b hab => by
    rw [hxw.2 a b hab]
    exact Submodule.zero_mem _
  have hxW : x ∈ W := IsoW_le G hW mu hxI
  have hdom : DomW la := G.dom_of_hwmod hbot hW hWf hxW (by rwa [Submodule.mem_bot]) hxw.1 hr
  obtain ⟨S, hS⟩ := hWf
  have hkill : ∀ y ∈ IsoW G W mu, G.cprod (GlX.qlist S (GlW.casI la)) (G.comp la y) = 0 := by
    intro y hy
    have hle : (⨆ v : {v : V // G.IsHW mu v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        LinearMap.ker ((G.cprod (GlX.qlist S (GlW.casI la))) ∘ₗ G.comp la) := by
      refine iSup_le fun v => ?_
      by_cases hv0 : (v : V) = 0
      · intro z hz
        have hz0 : z ∈ (⊥ : Submodule K V) := G.gS_le (by
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw, hv0]
          exact Submodule.zero_mem _) hbot hz
        rw [Submodule.mem_bot] at hz0
        rw [hz0]
        exact Submodule.zero_mem _
      · intro z hz
        exact LinearMap.mem_ker.mpr (GlX.gen_kill (G := G) hW hS v.2.1 v.2.2 hv0 hdom
          ⟨fun _ => le_refl _, rfl⟩ (fun _ => hne) z hz)
    exact LinearMap.mem_ker.mp (hle (IsoW_le_iSup G W mu hy))
  have h1 := hkill x hxI
  rw [hxw.1] at h1
  have h2 := GlX.cprod_mod (G := G) (μ := la) hbot hxw.1 hr (GlX.qlist S (GlW.casI la))
  rw [h1, zero_sub, neg_mem_iff, Submodule.mem_bot] at h2
  have hprod : ((GlX.qlist S (GlW.casI la)).map (fun c => ((GlW.casI la - c : ℤ) : K))).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    intro hmem
    obtain ⟨c, hc, hc0⟩ := List.mem_map.mp hmem
    have hc1 : GlW.casI la - c = 0 := by exact_mod_cast hc0
    have hc2 : c ∈ (S.image GlW.casI).erase (GlW.casI la) := Finset.mem_toList.mp hc
    exact (Finset.mem_erase.mp hc2).1 (by omega)
  rcases smul_eq_zero.mp h2 with h | h
  · exact hprod h
  · exact hx0 h
end Formalism.InvariantFactorPaths.PW
