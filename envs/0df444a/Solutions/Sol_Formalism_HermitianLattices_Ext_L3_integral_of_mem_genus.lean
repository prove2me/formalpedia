-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integral_of_mem_genus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:43.638998+00:00
-- url     : https://prove2.me/submissions/f69d7d95-fbea-4ea3-8d4b-e0f9203fefe1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanEqProd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_normD_eq_tprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_discrIdeal_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_form_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_iInf_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_locF_eq_loc
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_vd_locF


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
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {M : Submodule (𝓞 K) V} (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h M ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭) ∧
      normD h M = normD h L := by
  obtain ⟨hMl, hMg⟩ := hM
  have key : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 M := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact hMg P hP
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
    intro x hx y hy
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭.1 𝔭.2
    exact BrA.form_mem_locF hF hLi 𝔭.2.isPrime hg (e ▸ LocF.le_locF 𝔭.1 M hx)
      (e ▸ LocF.le_locF 𝔭.1 M hy)
  have hvd : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭 h𝔭
    rw [← localizedQuotients.vd_locF hF h M h𝔭, ← localizedQuotients.vd_locF hF h L h𝔭, ← e]
    unfold vd
    rw [BrA.discrIdeal_gmap hg]
  refine ⟨hMi, hvd, ?_⟩
  rw [BrA.normD_eq_tprod hK hF hs hd hMl hMi, BrA.normD_eq_tprod hK hF hs hd hL hLi]
  exact tprod_congr fun 𝔭 => by rw [hvd 𝔭.1 𝔭.2]
end Formalism.HermitianLattices.Ext.L3
