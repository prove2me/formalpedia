-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.Tr.yx_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.153834+00:00
-- url     : https://prove2.me/submissions/3c757d8b-c08c-47be-804b-c407bdf6b8c6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer Formalism.IndefR.LatticeTransfer.Lat
open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}
variable {p₀ p : V →ₗ[K] V} {x y : Fin n → V →ₗ[K] V} {c : Matrix (Fin n) (Fin n) K}
namespace Formalism.IndefR.LatticeTransfer.Lat
namespace Tr
theorem _root_.solution (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j) (i : Fin n) :
    y i (∑ j, x j (a j)) = ∑ j, c i j • a j := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => h.2.2.2.2.2.1 i j _ (ha j)
end Tr
end Formalism.IndefR.LatticeTransfer.Lat
