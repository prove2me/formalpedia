-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genus_covolume_local_dual_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:50.945413+00:00
-- url     : https://prove2.me/submissions/ee337558-34f2-430e-bfdc-9e2bda1832ef

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_sigma_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (P : Ideal (𝓞 K)) [P.IsPrime] (L M : Submodule (𝓞 K) V) (hM : M.FG)
    (hML : M ≤ gmap g (loc (K := K) P L)) :
    gmap g (locS P.primeCompl (genusCovol_tdual h L)) ≤
      locS P.primeCompl (genusCovol_tdual h M) := by
  classical
  have hg' : ∀ x y, h (g x) (g y) = h x y := hg
  obtain ⟨F, hF⟩ := hM
  have hgen : ∀ m ∈ F, ∃ t ∈ hcompl (K := K) P, t • g.symm m ∈ L := by
    intro m hm
    have : m ∈ gmap g (loc (K := K) P L) := hML (hF ▸ Submodule.subset_span hm)
    rw [isomAct_mem_gmap] at this
    exact this
  choose! t ht htL using hgen
  set T := ∏ m ∈ F, t m with hT
  have hTmem : T ∈ hcompl (K := K) P := Submonoid.prod_mem _ (fun m hm => ht m hm)
  let f : V →ₗ[𝓞 K] V := T • (g.symm : V →ₗ[K] V).restrictScalars (𝓞 K)
  have hMf : M ≤ L.comap f := by
    rw [← hF, Submodule.span_le]
    intro m hm
    change T • g.symm m ∈ L
    rw [hT, ← Finset.mul_prod_erase F t hm, mul_comm, mul_smul]
    exact L.smul_mem _ (htL m hm)
  intro x hx
  rw [isomAct_mem_gmap] at hx
  obtain ⟨s, hs, hsx⟩ := hx
  set σT := locBasic_sigma genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range T with hσT
  have hσmem : σT ∈ hcompl (K := K) P := genusBasic_sigma_mem genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range P T hTmem
  refine ⟨σT * s, P.primeCompl.mul_mem (locBasic_hcompl_le (K := K) P hσmem) hs, ?_⟩
  intro m hm
  obtain ⟨z, hz⟩ := hsx (T • g.symm m) (hMf hm)
  refine ⟨z, ?_⟩
  rw [← hz]
  congr 1
  rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right,
    genusBasic_hsmul_right, ← hg' (g.symm m) (g.symm x), LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, map_mul, mul_assoc]
end Formalism.HermitianLatticesTheory
