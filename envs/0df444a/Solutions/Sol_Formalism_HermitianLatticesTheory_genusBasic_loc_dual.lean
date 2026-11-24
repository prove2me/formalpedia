-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_loc_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:54.90968+00:00
-- url     : https://prove2.me/submissions/f1345f43-d12d-4cda-b818-9dbf7ca56c20

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_mem_one_mul
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_common
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
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
    (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (hL : L.FG) (z : V)
    (hz : ∀ v ∈ L, h v z ∈ loc (K := K) p (1 : Submodule R K)) :
    z ∈ loc (K := K) p (dual h L) := by
  obtain ⟨gens, rfl⟩ := hL
  have hgen : ∀ v ∈ gens, ∃ u ∈ hcompl (K := K) p,
      algebraMap R K u * h v z ∈ (1 : Submodule R K) := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 (hz v (Submodule.subset_span hv))
    exact ⟨s, hs, by rw [← Algebra.smul_def]; exact hsv⟩
  obtain ⟨u, hu, hall⟩ := genusBasic_common (hcompl (K := K) p) gens (fun v => h v z) hgen
  refine locBasic_mem_locS.2 ⟨u, hu, ?_⟩
  rw [dualBasic_mem_dual]
  intro y hy
  rw [genusBasic_hsmul_right]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hall x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply, mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
    exact genusBasic_mem_one_mul _ hx _
end Formalism.HermitianLatticesTheory
