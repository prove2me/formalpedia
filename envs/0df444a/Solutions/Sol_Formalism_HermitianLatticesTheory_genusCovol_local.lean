-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.73192+00:00
-- url     : https://prove2.me/submissions/fb811533-1d32-413b-b0d3-c50fa263af22

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_gmap_locS_comm
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_gmap_gmap_inv
import Theorems.Thm_Formalism_HermitianLatticesTheory_genus_covolume_local_dual_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_inv
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le


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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule (𝓞 K) V) (hLfg : L.FG)
    (hMfg : M.FG) (P : Ideal (𝓞 K)) [P.IsPrime] (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (hgL : gmap g (loc (K := K) P L) = loc (K := K) P M) :
    gmap g (locS P.primeCompl L) = locS P.primeCompl M ∧
    gmap g (locS P.primeCompl (genusCovol_tdual h L)) =
      locS P.primeCompl (genusCovol_tdual h M) := by
  have hle := locBasic_hcompl_le (K := K) P
  refine ⟨?_, ?_⟩
  · rw [← genusCovol_locS_locS hle L, gmap_locS_comm]
    change locS P.primeCompl (gmap g (loc (K := K) P L)) = _
    rw [hgL]
    exact genusCovol_locS_locS hle M
  · apply le_antisymm
    · exact genus_covolume_local_dual_le h g hg P L M hMfg (hgL ▸ genusCovol_le_locS _ M)
    · have hL' : L ≤ gmap g⁻¹ (loc (K := K) P M) := by
        rw [← hgL, genusBasic_gmap_inv]
        exact genusCovol_le_locS _ L
      have := genus_covolume_local_dual_le h g⁻¹ ((isom h).inv_mem hg) P M L hLfg hL'
      have h2 := Submodule.map_mono (f := ((g : V →ₗ[K] V).restrictScalars (𝓞 K))) this
      change gmap g (gmap g⁻¹ _) ≤ gmap g _ at h2
      rwa [genusCovol_gmap_gmap_inv] at h2
end Formalism.HermitianLatticesTheory
