-- Prove2me | solution 1 for Formalism.L2.G.congChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:59.22386+00:00
-- url     : https://prove2.me/submissions/a6f600d1-52c1-4fb7-8013-0e627c8f6fed

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.G
theorem _root_.solution {Z : Type} [Group Z] (ι : R →+* A) (hι : Function.Injective ι) (I : Ideal R)
    (H : Subgroup (GL n (R ⧸ I))) (lam : H →* Z) (g : GL n R) (hg : redGL I g ∈ H) (hm : bc ι g ∈ congPre ι I H) :
    congChar ι hι I H lam ⟨bc ι g, hm⟩ = lam ⟨redGL I g, hg⟩ := by
  have h : ((H.comap (redGL I)).equivMapOfInjective (bc ι) (bc_injective ι hι)).symm ⟨bc ι g, hm⟩ =
      (⟨g, hg⟩ : H.comap (redGL I)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  exact congrArg (fun z => lam ((redGL I).subgroupComap H z)) h
end Formalism.L2.G
