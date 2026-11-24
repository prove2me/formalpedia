-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_dual_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.135088+00:00
-- url     : https://prove2.me/submissions/e2151916-6bd1-4675-829a-f6944495f094

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_sigma_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_lg
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_loc_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
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
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLfg : L.FG) (hLM : SameGenus h L M)
    (hL : IsUnimodular h L) : dual h M ≤ M := by
  intro z hz
  rw [dualBasic_mem_dual] at hz
  apply genusBasic_lg (K := K) M z
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  rw [← hgL, isomAct_mem_gmap]
  have hmem : g.symm z ∈ loc (K := K) p (dual h L) := by
    apply genusBasic_loc_dual hinj hstar h p L hLfg
    intro v hv
    have hgv : g v ∈ loc (K := K) p M := by
      rw [← hgL, isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
      exact locBasic_le_locS _ _ hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 hgv
    have h1 := hz _ hsv
    rw [genusBasic_hsmul_left hinj hstar] at h1
    have hiso : h (g v) z = h v (g.symm z) := by
      have e := hg v (g.symm z)
      simpa using e
    refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s,
      genusBasic_sigma_mem hinj hstar p s hs, ?_⟩
    rw [Algebra.smul_def, ← hiso]
    exact h1
  rwa [show dual h L = L from hL] at hmem
end Formalism.HermitianLatticesTheory
