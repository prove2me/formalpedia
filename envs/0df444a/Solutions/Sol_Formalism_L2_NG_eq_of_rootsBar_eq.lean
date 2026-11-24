-- Prove2me | solution 1 for Formalism.L2.NG.eq_of_rootsBar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:21:04.708811+00:00
-- url     : https://prove2.me/submissions/4ec1f704-4382-4059-b410-4e3cb7de0fed

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
variable {A : ValuationSubring Ω} {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar p}
  {teich : Formalism.CyclotomicNorms.Fbar p →* ℂ} {I : Set (Ω ≃ₐ[E] Ω)} {n : ℕ} {P : (Ω ≃ₐ[E] Ω) → ℂ[X]} {f f' : (ZMod p)[X]}
namespace Formalism.L2.NG
theorem _root_.solution (hf : f.Monic) (hf' : f'.Monic) (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by
  have e1 := (IsAlgClosed.splits (f.map (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)))).eq_prod_roots_of_monic (hf.map _)
  have e2 := (IsAlgClosed.splits (f'.map (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)))).eq_prod_roots_of_monic (hf'.map _)
  unfold Formalism.CyclotomicNorms.rootsBar at h
  rw [h, ← e2] at e1
  exact Polynomial.map_injective _ (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)).injective e1
end Formalism.L2.NG
