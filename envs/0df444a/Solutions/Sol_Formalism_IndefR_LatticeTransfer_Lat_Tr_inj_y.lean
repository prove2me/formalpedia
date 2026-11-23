-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.Tr.inj_y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:05.381724+00:00
-- url     : https://prove2.me/submissions/77795eec-e5c8-4969-a4ff-4fbf56a21d61

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
theorem _root_.solution (h : Tr p₀ p x y c) (a : V) (ha : p a = a) (h0 : ∀ i, y i a = 0) : a = 0 := by
  rw [← h.2.2.2.2.2.2 a ha]
  simp [h0]
end Tr
end Formalism.IndefR.LatticeTransfer.Lat
