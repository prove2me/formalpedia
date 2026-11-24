-- Prove2me | solution 1 for Formalism.UG.P.csCovol_discr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:10.261638+00:00
-- url     : https://prove2.me/submissions/be9830d8-2ab4-48f5-80dd-63de8c9a8aff

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, Algebra.trace ℚ K ((a : K) * z) ∈ Set.range (algebraMap ℤ ℚ)) :
    ((discr K : ℚ) : K) * z ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hmem : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨n, hn⟩ := hz a'
    exact ⟨n, hn⟩
  have hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
    (1 : Submodule (𝓞 K) K) (b := NumberField.integralBasis K)
    (fun i => by
      rw [NumberField.integralBasis_apply]
      exact NumberField.RingOfIntegers.isIntegral_coe _) hone hmem
  rw [← NumberField.coe_discr, Algebra.smul_def, mul_one] at hint
  refine ⟨⟨_, hint⟩, ?_⟩
  simp
end Formalism.UG.P
