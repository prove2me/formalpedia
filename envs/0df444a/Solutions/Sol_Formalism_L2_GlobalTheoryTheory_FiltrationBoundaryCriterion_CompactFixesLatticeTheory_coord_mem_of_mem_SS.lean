-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.coord_mem_of_mem_SS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:13:54.878811+00:00
-- url     : https://prove2.me/submissions/932216f5-6e8c-4dae-8ea8-e88cae15e79c

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CoordMulTmul
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_mem_closure_of_mem_SS
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_coord_tmul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_smul_mem_intAd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
theorem _root_.solution {ι : Type} (b : Module.Basis ι F E) (D : 𝓞 F)
    (hD : ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range)
    {x : AE F E} (hx : x ∈ SS F E) (i : ι) : (D : F) • coord b i x ∈ intAd F := by
  have hx' := mem_closure_of_mem_SS hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, he, a, ha, rfl⟩ := hy
    obtain ⟨m, hm⟩ := hD e he i
    rw [coord_tmul, smul_smul, ← hm]
    exact smul_mem_intAd m ha
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [map_add, smul_add]; exact add_mem hu hv
  | neg u _ hu => rw [map_neg, smul_neg]; exact neg_mem hu
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
