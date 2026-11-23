-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovolBound_dualAt_gmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:04.536484+00:00
-- url     : https://prove2.me/submissions/801a4dea-ae7d-46df-9601-22cf73802fa3

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap


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
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (p : Ideal (𝓞 K)) (X : Submodule (𝓞 K) V) :
    dualAt h p (gmap g X) = gmap g (dualAt h p X) := by
  ext x
  simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    isomAct_mem_gmap]
  constructor
  · intro H z hz
    have := H (g z) (by simpa using hz)
    rwa [show h (g z) x = h z (g.symm x) by
      conv_lhs => rw [show x = g (g.symm x) by simp]
      exact hg z (g.symm x)] at this
  · intro H y hy
    have := H (g.symm y) hy
    rwa [show h (g.symm y) (g.symm x) = h y x by
      conv_rhs => rw [show y = g (g.symm y) by simp, show x = g (g.symm x) by simp]
      exact (hg (g.symm y) (g.symm x)).symm] at this
end Formalism.HermitianLatticesTheory
