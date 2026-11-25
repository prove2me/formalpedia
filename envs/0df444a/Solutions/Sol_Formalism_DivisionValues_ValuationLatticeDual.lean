-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationLatticeDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:26:10.375588+00:00
-- url     : https://prove2.me/submissions/a42ef266-f08b-4b72-a8d8-5dcb6593fa1f

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_map_isLattice
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_hstar
import Theorems.Thm_P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_herm_cut
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_E_inj
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_Pr_surj
import Theorems.Thm_Formalism_DivisionValues_projection_dual_lattice
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_idxB
import Theorems.Thm_Formalism_DivisionValues_exponent_index_local
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_nondeg_of_adj
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_cutLat
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_matLat
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mulVec_osmul
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_cut_isLattice
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_coe_natCast
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_isSymm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_nondeg
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : BoundsIVGen := by
  intro K _ _ _ n d H hH hdet E Pr hO A B hA DG hDG hB w a ha haB
  have hs := hform_isSymm H (herm_entry' hH)
  have hn := hform_nondeg H hs hdet.ne_zero
  have hsZ := hform_isSymm _ (herm_entry' (herm_cut hH E))
  have hnZ := nondeg_of_adj (hform H) hn (hform (Eᴴ * H * E)) hsZ (Matrix.mulVecLin E)
    (Matrix.mulVecLin Pr) (adj hH hO) (E_inj hO)
  have hT : Submodule.IsLattice K (matLat Pr A) :=
    map_isLattice (Matrix.mulVecLin Pr) (Pr_surj hO) A hA
  have hC : Submodule.IsLattice K (cutLat E A) := cut_isLattice E (E_inj hO) A hA
  have hCT : cutLat E A ≤ matLat Pr A := by
    intro z hz
    exact (mem_matLat _ _ _).mpr ⟨E.mulVec z, hz, by simp [Matrix.mulVec_mulVec, hO.1]⟩
  refine ⟨hT, hC, hCT, ?_⟩
  have hTh : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A)) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (Fin d → K) _ hsZ hnZ hstar _ hT).1
  have hL1 := projection_dual_lattice K n d H hH E Pr hO A
  have hDG0 : (DG : 𝓞 K) ≠ 0 := by exact_mod_cast hDG.ne'
  have ha' : (a : K) ≠ 0 := by simpa using ha
  have hDG' : (DG : K) ≠ 0 := by exact_mod_cast hDG.ne'
  have h2 := exponent_index_local K d (cutLat E A) _ hC hTh w (a * (DG : 𝓞 K)) (mul_ne_zero ha hDG0)
    (by
      intro z hz
      obtain ⟨s, hs, hsz⟩ := haB z hz
      refine ⟨s, hs, ?_⟩
      rw [mem_cutLat, mulVec_osmul, mulVec_osmul] at hsz
      rw [hL1, mem_cutLat, mulVec_osmul, mulVec_osmul]
      have := hB _ hsz
      have e : s • (a * (DG : 𝓞 K)) • E.mulVec z = (DG : 𝓞 K) • s • a • E.mulVec z := by
        simp only [smul_smul]
        congr 1
        ring
      rw [e]
      exact this)
  have hv : vw w ((a * (DG : 𝓞 K) : 𝓞 K) : K) = vw w (a : K) + vw w (DG : K) := by
    rw [show ((a * (DG : 𝓞 K) : 𝓞 K) : K) = (a : K) * ((DG : 𝓞 K) : K) from
      map_mul (algebraMap (𝓞 K) K) a _, coe_natCast, ValuationRepresentative.vw_mul w _ _ ha' hDG']
  rw [hv] at h2
  have h3 := idxB w (matLat Pr A) (cutLat E A) _ hT hC hTh
  change idx w (matLat Pr A) (Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A)) ≤ _
  rw [h3.2.1, h3.2.2 hCT]
  linarith
end Formalism.DivisionValues
