-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:01.809806+00:00
-- url     : https://prove2.me/submissions/4b7b9f02-9e0e-4524-8b3d-1cd45393c479

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {S : Type*} [CommRing S] [HenselianLocalRing S]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (T N d s₀ t₀ : S)
    (h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S)
    (h1 : IsUnit (2 * s₀ + T * t₀)) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  set f : S[X] := X ^ 2 + C (T * t₀) * X + C (N * t₀ ^ 2 - d) with hfdef
  have hf : f.Monic := by rw [hfdef]; monicity!
  have he : f.eval s₀ = s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d := by
    rw [hfdef]; simp; ring
  have hd : f.derivative.eval s₀ = 2 * s₀ + T * t₀ := by
    rw [hfdef]; simp only [derivative_add, derivative_C, derivative_X_pow, derivative_C_mul_X, add_zero]
    simp
  obtain ⟨s, hs, -⟩ := HenselianLocalRing.is_henselian f hf s₀ (he ▸ h0) (hd ▸ h1)
  refine ⟨s, t₀, ?_⟩
  have h2 : f.eval s = 0 := hs
  rw [hfdef] at h2
  simp at h2
  linear_combination h2
end Formalism.HermitianLatticesTheory
