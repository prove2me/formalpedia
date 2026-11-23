-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanA.mem_pow_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:25.331914+00:00
-- url     : https://prove2.me/submissions/aff54613-4f82-4d77-8caa-4b01ce91fa0b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_exists_mul_sub_one_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
set_option linter.deprecated false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanA
namespace Formalism.HermitianLattices.Ext.L3.MeanA
theorem _root_.solution {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t c : R}
    (ht : t ∉ 𝔭) {k : ℕ} (h : t * c ∈ 𝔭 ^ k) : c ∈ 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : c = u * (t * c) - (u * t - 1) * c := by ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ u h) (Ideal.mul_mem_right c _ hu)
end Formalism.HermitianLattices.Ext.L3.MeanA
