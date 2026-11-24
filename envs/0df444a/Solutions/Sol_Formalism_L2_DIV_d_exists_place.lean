-- Prove2me | solution 1 for Formalism.L2.DIV.d_exists_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:45.042797+00:00
-- url     : https://prove2.me/submissions/19c19f69-cc5e-41d8-9a5c-d29ab577640b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (F : Type) [Field F] [NumberField F] (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 F), plc v = p := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨M, hM, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
  have hpM : ((p : ℕ) : 𝓞 F) ∈ M := by
    have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hover.over, Ideal.under_def, Ideal.mem_comap] at h1
    simpa using h1
  have hne : M ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpM
    exact hp.ne_zero (by exact_mod_cast hpM)
  refine ⟨⟨M, hM.isPrime, hne⟩, ?_⟩
  show ringChar (𝓞 F ⧸ M) = p
  have : Nontrivial (𝓞 F ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hM.ne_top
  have h0 : ((p : ℕ) : 𝓞 F ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    exact hpM
  exact ((Nat.dvd_prime hp).mp (ringChar.dvd h0)).resolve_left CharP.ringChar_ne_one
end Formalism.L2.DIV
