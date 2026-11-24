-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.Tr.first_axis_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:26.387662+00:00
-- url     : https://prove2.me/submissions/dc1cbda7-3318-411a-bd1f-ad524669305d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_yx_sum

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
theorem _root_.solution (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j)
    (h0 : ∑ j, x j (a j) = 0) : a = 0 := by
  have h1 : ∀ i, ∑ j, c i j • a j = 0 := fun i => by
    rw [← h.yx_sum a ha i, h0, map_zero]
  have hu : IsUnit c.det := isUnit_iff_ne_zero.mpr h.2.2.2.2.1
  funext k
  have h2 : ∑ i, c⁻¹ k i • ∑ j, c i j • a j = a k := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]
    simp
  rw [← h2]
  simp [h1]
end Tr
end Formalism.IndefR.LatticeTransfer.Lat
