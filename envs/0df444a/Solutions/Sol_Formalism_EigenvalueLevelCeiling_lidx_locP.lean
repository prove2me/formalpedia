-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.lidx_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:20.074336+00:00
-- url     : https://prove2.me/submissions/f502b670-ed84-4ea9-82c1-2b16832b2d04

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementLoc
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_locLen_congr
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
private theorem locP_locP' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A) = Formalism.HermitianLatticesTheory.localization₂ p A := by
  ext x
  rw [mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [mem_localization_iff_exists_smul_mem] at h
    obtain ⟨t, ht, h⟩ := h
    exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact h⟩
  · intro hx
    exact ⟨1, p.primeCompl.one_mem, by rw [one_smul, mem_localization_iff_exists_smul_mem]; exact hx⟩
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
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (A B : Submodule R W) : lidx p A B = lidx p (localization₂ p A) (localization₂ p B) := by
  have e1 := locP_locP' p A
  have e3 := locP_locP' p B
  have e2 : Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B) = Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) := by
    rw [locP_inf', locP_locP', locP_locP', locP_inf']
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [locLen_congr p e1.symm e2.symm, locLen_congr p e3.symm e2.symm]
end Formalism.EigenvalueLevelCeiling
