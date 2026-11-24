-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame.isUnit_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:07.16583+00:00
-- url     : https://prove2.me/submissions/b1941cb9-3be5-4137-846b-5e66b15debd0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
theorem _root_.solution (π : A →+* A') (hπ : Function.Surjective π)
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {u : A} (hu : IsUnit (π u)) :
    IsUnit u := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨z, hz⟩ := hπ (↑w⁻¹ : A')
  have hker : u * z - 1 ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hz, ← hw, Units.mul_inv, sub_self]
  have hsq := h2 _ hker _ hker
  have h1 : u * (z * (1 - (u * z - 1))) = 1 := by linear_combination -hsq
  exact ⟨⟨u, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
end Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
