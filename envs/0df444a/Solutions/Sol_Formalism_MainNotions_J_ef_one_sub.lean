-- Prove2me | solution 1 for Formalism.MainNotions.J.ef_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:46.267201+00:00
-- url     : https://prove2.me/submissions/0ffe3706-3219-415c-a0d4-409e490b5205

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_pI_ne_bot
import Theorems.Thm_Formalism_MainNotions_J_pI_max
import Theorems.Thm_Formalism_MainNotions_J_liesOver_ne_bot
import Theorems.Thm_Formalism_MainNotions_J_map_pI_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
variable (L : Type) [Field L] [NumberField L] [Algebra K L]
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime)
    (hL : ∀ Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L),
      (span {(p : ℤ)}).ramificationIdx' Q * (span {(p : ℤ)}).inertiaDeg' Q = 1) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by
  intro P hP
  haveI := pI_max p hp
  obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hP
  have hPne : P ≠ ⊥ := liesOver_ne_bot K p hp P hPl
  haveI : P.IsMaximal := hPp.isMaximal hPne

  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P
  haveI := hQl
  haveI hQp : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  have hQ : Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 L)).mpr ⟨hQm.isPrime, hQp⟩
  have h1 := hL Q hQ
  have hmapP : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P ≠ ⊥ := by
    intro h
    apply hPne
    have h2 : P ≤ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P).comap (algebraMap (𝓞 K) (𝓞 L)) := Ideal.le_comap_map
    rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))] at h2
    exact le_bot_iff.mp h2
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hQl.over
  have he := Ideal.ramificationIdx'_algebra_tower (p := span {(p : ℤ)}) (P := P) (Q := Q) hmapP
    (map_pI_ne_bot L p hp) hle
  have hf := Ideal.inertiaDeg'_algebra_tower (span {(p : ℤ)}) P Q
  rw [he, hf] at h1
  have h3 : ((span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P) *
      (P.ramificationIdx' Q * P.inertiaDeg' Q) = 1 := by
    rw [← h1]
    ring
  exact Nat.eq_one_of_mul_eq_one_right h3
end Formalism.MainNotions.J
