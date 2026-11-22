-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_mem_par
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:01:57.165084+00:00
-- url     : https://prove2.me/submissions/ceaec8fd-ffa0-4f06-9567-91228574ad82

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {𝔽 : Type} [Field 𝔽]
namespace Formalism.UG.P
theorem _root_.solution [Finite 𝔽] (n j : ℕ) (g : GL (Fin n) 𝔽) :
    g ∈ tjcosets_par n j ↔
      ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin n) (Fin n) 𝔽) a b = 0 := Iff.rfl
end Formalism.UG.P
