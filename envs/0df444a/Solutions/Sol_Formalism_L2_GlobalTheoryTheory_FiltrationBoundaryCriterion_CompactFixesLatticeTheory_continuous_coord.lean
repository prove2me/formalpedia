-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.continuous_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:19.435157+00:00
-- url     : https://prove2.me/submissions/5bcb5605-e856-4a2f-88d5-1888d253e189

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CompactFixesLattice
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CoordMulTmul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_coord_mul_tmul

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
theorem _root_.solution {ι : Type} (b : Module.Basis ι F E) (i : ι) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (coord b i) := by
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  letI : Algebra (AF F) (AE F E) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let f : AE F E →ₗ[AF F] AF F :=
    { toFun := coord b i
      map_add' := map_add _
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [Algebra.smul_def, mul_comm,
          show algebraMap (AF F) (AE F E) r = (1 : E) ⊗ₜ[F] r from rfl, coord_mul_tmul, mul_comm] }
  exact IsModuleTopology.continuous_of_linearMap f
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
