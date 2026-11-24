-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps.crd_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:25.827864+00:00
-- url     : https://prove2.me/submissions/87dc799f-735d-46ca-8263-b4d01b4c6eb7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_AdelicBounds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL5_PClassSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps
theorem _root_.solution {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (r : 𝓞 E) {x : Fin M → E} (hx : x ∈ crdOf b L0) :
    (r : E) • x ∈ crdOf b L0 := by
  show ∑ i, ((r : E) • x) i • b i ∈ L0
  have e : ∑ i, ((r : E) • x) i • b i = r • ∑ i, x i • b i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_smul, algebraMap_smul]
  rw [e]
  exact L0.smul_mem r hx
end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps
