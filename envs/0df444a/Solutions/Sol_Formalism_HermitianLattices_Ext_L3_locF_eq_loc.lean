-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.locF_eq_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:20.016546+00:00
-- url     : https://prove2.me/submissions/26d8ef23-c6b4-4ae6-8957-217f0bd01250

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_hcompl_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (L : Submodule (𝓞 K) V) :
    locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = Formalism.HermitianLatticesTheory.loc (K := K) P L := by
  have hPp := hP.isPrime
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime := Ideal.comap_isPrime _ _
  ext x
  rw [LocF.mem_locF_iff hp]
  unfold Formalism.HermitianLatticesTheory.loc
  rw [Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨_, ?_, hx⟩
    rw [WA.mem_hcompl_iff hPp, WA.mem_conjIdeal_iff,
      (conjO_eq_iff_mem_range hF _).mpr ⟨t, rfl⟩]
    exact ⟨ht, ht⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨h1, h2⟩ := (WA.mem_hcompl_iff hPp s).mp hs
    rw [WA.mem_conjIdeal_iff] at h2
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF (conjO K s * s)).mp
      (by rw [map_mul, conjO_conjO, mul_comm])
    refine ⟨t, ?_, ?_⟩
    · rw [Ideal.mem_comap, ht]
      exact fun h => (hPp.mem_or_mem h).elim h2 h1
    · rw [ht, mul_smul]
      exact L.smul_mem _ hx
end Formalism.HermitianLattices.Ext.L3
