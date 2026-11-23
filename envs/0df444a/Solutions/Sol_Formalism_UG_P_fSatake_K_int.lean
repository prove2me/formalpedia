-- Prove2me | solution 1 for Formalism.UG.P.fSatake_K_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:28.16763+00:00
-- url     : https://prove2.me/submissions/241e360d-4f45-45d2-b68c-d45017b0b275

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution {k : GU σ n} (hk : k ∈ KU σ n) (i j : Fin n) : ⟪k⟫ i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf] at hk
  obtain ⟨g, hg⟩ := hk.2
  rw [← hg, bc]
  exact (g.val i j).2
end Formalism.UG.P
