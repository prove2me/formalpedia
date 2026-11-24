-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_isom_locF_of_vd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:58.366816+00:00
-- url     : https://prove2.me/submissions/0379f39d-2f5a-41db-bd3a-09d6f5673dff

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isSD_loc
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_gmap_eq_of_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_sd_main
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isHermSemilocal_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isUnimodularAt_iff_vd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_locF_eq_loc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A B : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B)
    (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h A) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hvA : vd h A 𝔭 = 0) (hvB : vd h B 𝔭 = 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 A) = locF 𝔭 B := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨π, hπ, -, -⟩ := U0.exists_isUnif hF hP
  rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
  obtain ⟨g, hg, -, hgM⟩ := U0.sd_main (WA.isHermSemilocal_locRing hK hP) hπ hs hda _ ⊤ ⊤ _ _ 1
    le_rfl
    (U0.isSD_loc hA hP.isPrime ((isUnimodularAt_iff_vd hK hF hs hd hA hAi hP).mpr hvA))
    (U0.isSD_loc hB hP.isPrime ((isUnimodularAt_iff_vd hK hF hs hd hB hBi hP).mpr hvB))
    (one_mem _) (fun _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  exact ⟨g, hg, U0.gmap_eq_of_iff hgM⟩
end Formalism.HermitianLattices.Ext.L3
