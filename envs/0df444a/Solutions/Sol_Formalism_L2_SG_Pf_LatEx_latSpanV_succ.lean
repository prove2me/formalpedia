-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.latSpanV_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:41.273596+00:00
-- url     : https://prove2.me/submissions/b6c19e94-cddf-4ce7-83bd-642d120a8bb5

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
theorem _root_.solution {n : ℕ} (c : Fin (n + 1) → 𝓕) (v : Fin (n + 1) → V) :
    latSpanV c v = latSpanV (Fin.init c) (Fin.init v) ⊔ lineV (c (Fin.last n)) (v (Fin.last n)) := by
  unfold latSpanV lineV
  rw [← Submodule.span_union]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_union, Fin.exists_fin_succ', Fin.init]
end Formalism.L2.SG.Pf.LatEx
