-- Prove2me | solution 1 for Formalism.REAL.reverse_of_fn_noncompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:14.756179+00:00
-- url     : https://prove2.me/submissions/259cc4d1-c29a-4c90-a4df-9e3ffd897045

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution {j : ℕ} (α : Fin j → Fin n × Fin n) (h : ∀ i, ε (α i).1 ≠ ε (α i).2) :
    ∀ p ∈ (List.ofFn α).reverse, ε p.1 ≠ ε p.2 := by
  intro p hp
  rw [List.mem_reverse, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  exact h i
end Formalism.REAL
