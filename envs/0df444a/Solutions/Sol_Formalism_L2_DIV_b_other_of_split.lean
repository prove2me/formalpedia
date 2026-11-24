-- Prove2me | solution 1 for Formalism.L2.DIV.b_other_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:33:49.025544+00:00
-- url     : https://prove2.me/submissions/27948e2e-88d7-49d9-beb5-a4033f0fcf33

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
section
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
namespace Formalism.L2.DIV
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E]
end Gen
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Main
section A2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
end A2
section C
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
end C
section B
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end B
section B2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end B2
section B3
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {L : Type} [Field L]
end B3
section B4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
private theorem hs_eq_lemma_2 {P Q : HeightOneSpectrum (𝓞 E)} (h : P.asIdeal = Q.asIdeal) : P = Q := by
  first
  | exact HeightOneSpectrum.ext h
  | (cases P; cases Q; cases h; rfl)
end B4
section D1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end D1
section D2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom
end D2
end Formalism.L2.DIV
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (P P' Q : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (hQ : Q ≠ P) (hQ' : Q ≠ P') :
    Q.asIdeal.under (𝓞 F) ≠ v.asIdeal := by
  intro hQv
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hQv.symm)
  rw [h] at hle
  rcases (Ideal.IsPrime.mul_le Q.isPrime).mp hle with h1 | h1
  · exact hQ (hs_eq_lemma_2 (P.isMaximal.eq_of_le Q.isPrime.ne_top h1).symm)
  · exact hQ' (hs_eq_lemma_2 (P'.isMaximal.eq_of_le Q.isPrime.ne_top h1).symm)
end Formalism.L2.DIV
