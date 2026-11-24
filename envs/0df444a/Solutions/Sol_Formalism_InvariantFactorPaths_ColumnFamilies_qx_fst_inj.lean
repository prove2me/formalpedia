-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_fst_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.348481+00:00
-- url     : https://prove2.me/submissions/551273d8-54fc-40aa-8ce7-8065aad420b1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxFstInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} {M M' : GLMod n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (CF : ColFam M) (nu0 : Fin n → ℤ) (x y : {x : qx_J Str CF // (x.2 : Fin n → ℤ) = nu0})
    (h : x.1.1 = y.1.1) : x = y := by
  obtain ⟨⟨j, nu, hnu⟩, hx⟩ := x
  obtain ⟨⟨j', nu', hnu'⟩, hy⟩ := y
  simp only at h hx hy
  subst h
  subst hx
  subst hy
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
