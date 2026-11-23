-- Prove2me | solution 1 for Formalism.ExtensionFiltration.den_smul_idealSmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:46.377146+00:00
-- url     : https://prove2.me/submissions/c0a3b682-8c30-43ad-af12-5506516f0c87

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
omit [StarRing K] [IsTotallyComplex K]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (M : Submodule (𝓞 K) V) :
    (Ideal.span {(I.den : 𝓞 K)}) • Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M = I.num • M := by
  have hmem : ∀ a ∈ (I : Submodule (𝓞 K) K), ∃ c ∈ I.num,
      (algebraMap (𝓞 K) K c) = (I.den : 𝓞 K) • a := by
    intro a ha
    have h1 : I.den • a ∈ I.den • (I : Submodule (𝓞 K) K) := Submodule.smul_mem_pointwise_smul a I.den _ ha
    rw [FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨c, hc, hca⟩ := h1
    exact ⟨c, hc, hca⟩
  have hmem2 : ∀ c ∈ I.num, ∃ a ∈ (I : Submodule (𝓞 K) K),
      (I.den : 𝓞 K) • a = algebraMap (𝓞 K) K c := by
    intro c hc
    have h1 : algebraMap (𝓞 K) K c ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := ⟨c, hc, rfl⟩
    rw [← FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨a, ha, hax⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨a, ha, hax⟩
  unfold Formalism.HermitianLatticesTheory.idealSmul
  rw [Submodule.ideal_span_singleton_smul]
  apply le_antisymm
  · have key : Submodule.span (𝓞 K) {z | ∃ a ∈ (I : Submodule (𝓞 K) K), ∃ x ∈ M, z = a • x} ≤
        (I.num • M).comap (LinearMap.lsmul (𝓞 K) V (I.den : 𝓞 K)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, x, hx, rfl⟩
      obtain ⟨c, hc, hca⟩ := hmem a ha
      show (I.den : 𝓞 K) • (a • x) ∈ I.num • M
      rw [← smul_assoc, ← hca, algebraMap_smul]
      exact Submodule.smul_mem_smul hc hx
    rintro _ ⟨n, hn, rfl⟩
    exact key hn
  · rw [Submodule.smul_le]
    intro c hc x hx
    obtain ⟨a, ha, hax⟩ := hmem2 c hc
    have h1 : a • x ∈ Submodule.span (𝓞 K) {z | ∃ a ∈ (I : Submodule (𝓞 K) K), ∃ x ∈ M, z = a • x} :=
      Submodule.subset_span ⟨a, ha, x, hx, rfl⟩
    have h2 := Submodule.smul_mem_pointwise_smul (a • x) (I.den : 𝓞 K) _ h1
    rw [← smul_assoc, hax, algebraMap_smul] at h2
    exact h2
end Formalism.ExtensionFiltration
