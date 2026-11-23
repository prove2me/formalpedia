-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.map_inv_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:35.023545+00:00
-- url     : https://prove2.me/submissions/67faf847-e74d-4db7-be6b-d3828a69a4c3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)
variable {σ I}
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) {θ e : A} (he : (θ - σ θ) * e = 1) : σ e = -e := by

  have h1 : (θ - σ θ) * (-σ e) = 1 := by
    have h0 := congrArg σ he
    rw [map_mul, map_sub, hσ, map_one] at h0
    linear_combination h0
  have h2 : e = -σ e := by
    calc e = e * ((θ - σ θ) * (-σ e)) := by rw [h1, mul_one]
      _ = ((θ - σ θ) * e) * (-σ e) := by ring
      _ = -σ e := by rw [he, one_mul]
  linear_combination h2
end Formalism.HermitianLattices.Ext.L3.NormLifting
