-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:29:44.469196+00:00
-- url     : https://prove2.me/submissions/524c016a-4b24-42e4-b022-4fa74566349c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    ∃ (r : ℕ) (u : 𝓞 F), u ∉ 𝔭 ∧ ∀ x ∈ 𝔭 ^ r, c ∣ u * x := by
  have hc' : Ideal.span {c} ≠ (0 : Ideal (𝓞 F)) := by simpa using hc
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]; exact h𝔭.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.mp hnd
  refine ⟨multiplicity 𝔭 (Ideal.span {c}), t, htp, fun x hx => ?_⟩
  rw [← Ideal.mem_span_singleton, hb, mul_comm t]
  exact Ideal.mul_mem_mul hx htb
end Formalism.HermitianLattices.Ext.L3.D2
