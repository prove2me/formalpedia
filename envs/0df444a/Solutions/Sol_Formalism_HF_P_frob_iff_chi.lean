-- Prove2me | solution 1 for Formalism.HF.P.frob_iff_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:35.60307+00:00
-- url     : https://prove2.me/submissions/2a712721-8d6d-4a0c-9df1-4ffcc858016f

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Theorems.Thm_Formalism_HF_P_span_maximal
import Theorems.Thm_Formalism_Q3_hostFrob


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Filter Topology Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (q : Fin 3 → ℕ) (hq : Hyp3 q) (E : Type) [Field E] [NumberField E]
    (α : Fin 3 → E) (hE : IsHost q α) (g : Gal3) (p : ℕ) (hp : p.Prime)
    (hpq : ∀ i, p ≠ q i) :
    (∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ)),
        IsArithFrobAt ℤ σ P → galSign α σ = g) ↔
      ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro H i
    have := span_maximal p hp
    obtain ⟨P, hPm, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (span {(p : ℤ)})
    have : P.IsPrime := hPm.isPrime
    have := hPl
    obtain ⟨σ, hσ⟩ := (hostFrob q hq E α hE p hpq P).1
    have h1 := H P σ hσ
    have h2 := ((hostFrob q hq E α hE p hpq P).2 σ).1 hσ i
    rw [← h2, h1]
  · intro H P _ _ σ hσ
    have h2 := ((hostFrob q hq E α hE p hpq P).2 σ).1 hσ
    funext i
    exact Units.ext ((h2 i).trans (H i))
end Formalism.HF.P
