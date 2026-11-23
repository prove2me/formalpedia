-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:35.919107+00:00
-- url     : https://prove2.me/submissions/490da857-b981-4893-88d7-80fe2ec19652

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_sigma_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_lg
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : IsIntegralLat h L) : IsIntegralLat h M := by
  intro x hx y hy
  apply genusBasic_lg (K := K) (1 : Submodule R K) (h x y)
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hx' : x ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hx
  have hy' : y ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hy
  rw [isomAct_mem_gmap] at hx' hy'
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.1 hx'
  obtain ⟨t, ht, hty⟩ := locBasic_mem_locS.1 hy'
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg (g.symm x) (g.symm y)
    simpa using e.symm
  refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s * t,
    Submonoid.mul_mem _ (genusBasic_sigma_mem hinj hstar p s hs) ht, ?_⟩
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  rw [Algebra.smul_def, map_mul]
  convert h1 using 1
  ring
end Formalism.HermitianLatticesTheory
