-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusScale_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:58.55387+00:00
-- url     : https://prove2.me/submissions/03bb1f56-cf87-4e72-b8cd-5057926d9925

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_lg
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_sigma_mem
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
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : ∀ x ∈ L, ∀ y ∈ L, c * h x y ∈ (1 : Submodule R K)) :
    ∀ x ∈ M, ∀ y ∈ M, c * h x y ∈ (1 : Submodule R K) := by
  intro x hx y hy
  refine genusBasic_lg (K := K) (1 : Submodule R K) (c * h x y) ?_
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hxM : x ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hx
  have hyM : y ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hy
  rw [← hgL, isomAct_mem_gmap] at hxM hyM
  obtain ⟨s, hsS, hsx⟩ := locBasic_mem_locS.mp hxM
  obtain ⟨t, htS, hty⟩ := locBasic_mem_locS.mp hyM
  have hg' : ∀ u v : V, h (g u) (g v) = h u v := hg
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg' (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    exact e.symm
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  refine locBasic_mem_locS.mpr ⟨locBasic_sigma hinj hstar s * t,
    (hcompl (K := K) p).mul_mem (genusBasic_sigma_mem hinj hstar p s hsS) htS, ?_⟩
  have e : (locBasic_sigma hinj hstar s * t) • (c * h x y) =
      c * (algebraMap R K (locBasic_sigma hinj hstar s) * (algebraMap R K t * h x y)) := by
    rw [Algebra.smul_def, map_mul]
    ring
  rw [e]
  exact h1
end Formalism.HermitianLatticesTheory
