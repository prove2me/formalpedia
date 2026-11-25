-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:35.694134+00:00
-- url     : https://prove2.me/submissions/0b6d023d-b3ee-40e4-adae-cadb9ed01fc4

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_Imports
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompact
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_coord_tmul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_exists_sub_mem_intAd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_mem_SS_of_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem exists_basis_mem_intOE :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) F E, ∀ i, b i ∈ intOE E := by
  classical
  let c := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  have hyF : IsUnit ((y : ℤ) : F) := (Int.cast_ne_zero.mpr hy0).isUnit
  refine ⟨_, c.isUnitSMul (w := fun _ => ((y : ℤ) : F)) (fun _ => hyF), fun i => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul F]
  exact ⟨⟨_, (mem_integralClosure_iff ℤ E).mpr (hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i)))⟩, rfl⟩
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
theorem _root_.solution (x : AE F E) : ∃ e : E, x - inclE (F := F) (AF F) e ∈ SS F E := by
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  choose u hu using fun i => exists_sub_mem_intAd (F := F) (coord b i x)
  refine ⟨∑ i, u i • b i, mem_SS_of_coord b hb _ fun i => ?_⟩
  have h1 : inclE (F := F) (AF F) (∑ j, u j • b j) = (∑ j, u j • b j) ⊗ₜ[F] (1 : AF F) := rfl
  rw [map_sub, h1, coord_tmul, b.repr_sum_self, ← Algebra.algebraMap_eq_smul_one]
  exact hu i
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
