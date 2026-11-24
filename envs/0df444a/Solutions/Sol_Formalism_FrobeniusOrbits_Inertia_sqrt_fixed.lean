-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.sqrt_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:34:18.112292+00:00
-- url     : https://prove2.me/submissions/62d36c24-8135-4245-95e9-42778cd4f598

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_omega_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution {F : Type} [Field F] [NumberField F] {r p : ℕ} (hr : r.Prime) (hr4 : r % 4 = 3)
    (hp : p.Prime) (hpr : p ≠ r) (P : Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : F ≃ₐ[ℚ] F) {X : F} (hX : X ^ 2 = -(r : F)) (hσX : σ X = -X) :
    ¬ ∀ y : 𝓞 F, σ • y - y ∈ P := by
  intro hall
  set ω : 𝓞 F := ⟨(1 + X) / 2, omega_integral hr4 hX⟩ with hωdef
  have hmem := hall ω
  have hval : algebraMap (𝓞 F) F (σ • ω - ω) = -X := by
    show σ ((1 + X) / 2) - (1 + X) / 2 = -X
    rw [map_div₀, map_add, map_one, hσX, map_ofNat]
    ring
  have hy2 : (σ • ω - ω) * (σ • ω - ω) = -((r : ℤ) : 𝓞 F) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, hval, map_neg, map_intCast]
    push_cast
    linear_combination hX
  have hrP : ((r : ℤ) : 𝓞 F) ∈ P := by
    have h1 := P.mul_mem_left (σ • ω - ω) hmem
    rw [hy2] at h1
    simpa using P.neg_mem h1
  have hr' : (r : ℤ) ∈ Ideal.span {(p : ℤ)} := by
    rw [Ideal.over_def P (Ideal.span {(p : ℤ)})]
    show algebraMap ℤ (𝓞 F) (r : ℤ) ∈ P
    simpa using hrP
  rw [Ideal.mem_span_singleton] at hr'
  have hpr' : p ∣ r := by exact_mod_cast hr'
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 hpr')
end Formalism.FrobeniusOrbits.Inertia
