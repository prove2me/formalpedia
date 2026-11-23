-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:38.464486+00:00
-- url     : https://prove2.me/submissions/e385fad4-06dc-40d5-9bc3-94492a851aa1

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementLoc
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_lix_locP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
section Gen
private theorem mem_localization_iff_exists_smul_mem {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl
private theorem locP_inf' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A B : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) = Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B := by
  ext x
  rw [Submodule.mem_inf, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [Submodule.mem_inf] at h
    exact ⟨⟨s, hs, h.1⟩, ⟨s, hs, h.2⟩⟩
  · rintro ⟨⟨s, hs, h1⟩, ⟨t, ht, h2⟩⟩
    refine ⟨t * s, p.primeCompl.mul_mem ht hs, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_smul]
      exact A.smul_mem t h1
    · rw [mul_comm, mul_smul]
      exact B.smul_mem s h2
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Gen
section Instance
variable (K : Type) [Field K] [NumberField K] [StarRing K]
end Instance
end Formalism.EigenvalueLevelCeiling
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (A X₃ X₄ : Submodule (𝓞 K) Z)
    (h : localization₂ w.asIdeal X₃ ≤ localization₂ w.asIdeal X₄) :
    lix w A (X₃ ⊓ X₄) = lix w A X₃ := by
  rw [lix_locP w A (X₃ ⊓ X₄), lix_locP w A X₃, locP_inf', inf_eq_left.mpr h]
end Formalism.EigenvalueLevelCeiling
