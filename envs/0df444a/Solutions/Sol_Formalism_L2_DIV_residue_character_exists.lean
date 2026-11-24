-- Prove2me | solution 1 for Formalism.L2.DIV.residue_character_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:15:55.890503+00:00
-- url     : https://prove2.me/submissions/c1d2bbb9-9e89-42d0-99ea-136957905827

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_P2M_Formalism_L2_DIV_tpExU_proof__f73447c0298f
import Theorems.Thm_Formalism_L2_DIV_b_same

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
variable {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution : ResCharEx := by
  intro F E _ _ _ _ _ L _ ξ hξ P
  classical
  set v := bUnder F P with hv
  have hPv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  choose U B hB hU hUP hUP' using tpExU_proof' P v hPv
  have key : ∀ (u : (RInt F E)ˣ) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a →
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)) →
      ξ (Units.map (RInt F E).subtype.toMonoidHom u) = ξ (Units.map (RInt F E).subtype.toMonoidHom (U a)) := by
    intro u a b hb hu huP huP'
    apply b_same ξ hξ v u (U a) hu (hU a)
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      have hbb : b - B a ∈ Q.asIdeal := by
        rw [← Ideal.Quotient.eq, hb, hB]
      have : (u : RInt F E) - U a = ((u : RInt F E) - toRInt F E b) - ((U a : RInt F E) - toRInt F E (B a)) +
          toRInt F E (b - B a) := by rw [map_sub]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.sub_mem _ huP (hUP a)) (Ideal.mem_map_of_mem _ hbb)
    · have : (u : RInt F E) - U a = ((u : RInt F E) - 1) - ((U a : RInt F E) - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (huP' Q hQ) (hUP' a Q hQ)
  let χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ := MonoidHom.mk' (fun a => ξ (Units.map (RInt F E).subtype.toMonoidHom (U a))) (by
    intro a a'
    rw [← map_mul, ← map_mul]
    symm
    apply key (U a * U a') (a * a') (B a * B a')
    · rw [map_mul, hB, hB, Units.val_mul]
    · rw [map_mul]; exact mul_mem (hU a) (hU a')
    · have : ((U a * U a' : (RInt F E)ˣ) : RInt F E) - toRInt F E (B a * B a') =
          ((U a : RInt F E) - toRInt F E (B a)) * (U a' : RInt F E) +
            toRInt F E (B a) * ((U a' : RInt F E) - toRInt F E (B a')) := by
        rw [map_mul, Units.val_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hUP a)) (Ideal.mul_mem_left _ _ (hUP a'))
    · intro P' hP'
      have : ((U a * U a' : (RInt F E)ˣ) : RInt F E) - 1 =
          ((U a : RInt F E) - 1) * (U a' : RInt F E) + ((U a' : RInt F E) - 1) := by
        rw [Units.val_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hUP' a P' hP')) (hUP' a' P' hP'))
  refine ⟨χ, ?_, ?_⟩
  · intro v' hv' u a b hb hu huP huP'
    have : v' = v := HeightOneSpectrum.ext (hv'.symm.trans hPv)
    subst this
    exact key u a b hb hu huP huP'
  · intro χ' hχ'
    ext a
    rw [← hχ' v hPv (U a) a (B a) (hB a) (hU a) (hUP a) (hUP' a)]
    rfl
end Formalism.L2.DIV
