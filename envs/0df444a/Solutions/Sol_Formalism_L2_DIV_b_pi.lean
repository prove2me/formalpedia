-- Prove2me | solution 1 for Formalism.L2.DIV.b_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:18.638261+00:00
-- url     : https://prove2.me/submissions/bcb3a56a-e763-4380-bb17-93405c8d7aa2

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, π ∈ v.asIdeal ∧ ∀ v' : HeightOneSpectrum (𝓞 F), v' ≠ v → π ∉ v'.asIdeal := by
  classical
  have hv0 : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have h1 : ClassGroup.mk0 (⟨v.asIdeal, hv0⟩ ^ h) = 1 := by
    rw [map_pow, hh, pow_card_eq_one]
  have h2 : (v.asIdeal ^ h).IsPrincipal := by
    have h3 : v.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv0 h
    rw [← ClassGroup.mk0_eq_one_iff h3, ← h1]
    rfl
  obtain ⟨π, hπ⟩ := h2
  have hπ' : v.asIdeal ^ h = Ideal.span {π} := hπ
  have hmem : π ∈ v.asIdeal ^ h := by rw [hπ']; exact Ideal.mem_span_singleton_self π
  refine ⟨π, Ideal.pow_le_self hpos.ne' hmem, fun v' hv' hc => hv' ?_⟩
  have hle : v.asIdeal ^ h ≤ v'.asIdeal := by
    rw [hπ', Ideal.span_singleton_le_iff_mem]; exact hc
  have hle' : v.asIdeal ≤ v'.asIdeal := v'.isPrime.le_of_pow_le hle
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle').symm
end Formalism.L2.DIV
