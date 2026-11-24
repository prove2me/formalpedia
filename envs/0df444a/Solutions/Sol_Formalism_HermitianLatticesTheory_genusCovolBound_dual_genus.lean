-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovolBound_dual_genus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:16.887164+00:00
-- url     : https://prove2.me/submissions/035124da-8644-41fe-b129-1034dc715884

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_dualAt_gmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual


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
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K))
    (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (M : Submodule (𝓞 K) V)
    (hM : M ∈ genus h L) : dual h M ∈ genus h (dual h L) := by
  obtain ⟨hMl, hMg⟩ := hM
  refine ⟨(dualLattice (𝓞 K) K V h hs hnd hstar M hMl).1, ?_⟩
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hMg p hp
  refine ⟨g, hg, ?_⟩
  have hL1 := (locDual (𝓞 K) K V h hs hstar L hL.fg).1 p hp.isPrime
  have hM1 := (locDual (𝓞 K) K V h hs hstar M hMl.fg).1 p hp.isPrime
  calc gmap g (loc (K := K) p (dual h L))
      = gmap g (dualAt h p (loc (K := K) p L)) := by rw [hL1.1, hL1.2]
    _ = dualAt h p (gmap g (loc (K := K) p L)) :=
        (genusCovolBound_dualAt_gmap h g hg p _).symm
    _ = dualAt h p (loc (K := K) p M) := by rw [hgL]
    _ = loc (K := K) p (dual h M) := by rw [hM1.2, hM1.1]
end Formalism.HermitianLatticesTheory
