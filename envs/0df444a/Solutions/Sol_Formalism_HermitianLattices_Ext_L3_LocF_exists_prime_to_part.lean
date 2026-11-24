-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.exists_prime_to_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.928668+00:00
-- url     : https://prove2.me/submissions/ac6a385e-2d4e-4f82-8094-4092ab6cb3ef

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {c : 𝓞 F} (hc : c ≠ 0) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsMaximal) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal → 𝔮 ≠ 𝔭 → ∃ u : 𝓞 F, u ∉ 𝔮 ∧ c ∣ u * t := by
  have hc' : Ideal.span {c} ≠ (0 : Ideal (𝓞 F)) := by
    simpa using hc
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact hp.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.mp hnd
  refine ⟨t, htp, fun 𝔮 hq hne => ?_⟩
  have h1 : ¬ 𝔭 ^ multiplicity 𝔭 (Ideal.span {c}) ≤ 𝔮 := by
    intro hle
    exact hne (hp.eq_of_le hq.ne_top (hq.isPrime.le_of_pow_le hle)).symm
  obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.mp h1
  refine ⟨u, hu2, ?_⟩
  rw [← Ideal.mem_span_singleton, hb]
  exact Ideal.mul_mem_mul hu1 htb
end Formalism.HermitianLattices.Ext.L3.LocF
