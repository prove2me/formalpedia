-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:38.158357+00:00
-- url     : https://prove2.me/submissions/dd5bf36a-b04d-4d9a-806d-33472c656fdb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution {n : ℕ} (w : Fin (n + 1) → V) (hw : LinearIndependent E w) :
    ∃ f : V →ₗ[E] E, f (w (Fin.last n)) = 1 ∧ ∀ i : Fin n, f (w i.castSucc) = 0 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply (Fin.last n)).comp hw.repr)
  refine ⟨g, ?_, fun i => ?_⟩
  · have h := congrArg (fun h => h ⟨w (Fin.last n), Submodule.subset_span ⟨_, rfl⟩⟩) hg
    simpa [hw.repr_eq_single (Fin.last n) ⟨w (Fin.last n), Submodule.subset_span ⟨_, rfl⟩⟩ rfl] using h
  · have hne := (Fin.castSucc_lt_last i).ne
    have h := congrArg (fun h => h ⟨w i.castSucc, Submodule.subset_span ⟨_, rfl⟩⟩) hg
    simpa [hw.repr_eq_single i.castSucc ⟨w i.castSucc, Submodule.subset_span ⟨_, rfl⟩⟩ rfl, Finsupp.single_apply, hne] using h
end Formalism.L2.SG.Pf.LatEx
