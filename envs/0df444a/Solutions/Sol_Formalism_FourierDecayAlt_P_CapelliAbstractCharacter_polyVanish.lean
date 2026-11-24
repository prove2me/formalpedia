-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.polyVanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:28.223691+00:00
-- url     : https://prove2.me/submissions/9fe52f5b-fd4c-41e1-a561-551636d13aa4

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {X : Type} [AddCommGroup X] [Module ℂ X] (d : ℕ) (c : ℕ → X) (F : Finset ℂ)
    (h : ∀ u : ℂ, u ∉ F → ∑ s ∈ Finset.range d, (u ^ s) • c s = 0) : ∀ s ∈ Finset.range d, c s = 0 := by
  intro s hs
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (c s)).mp
  intro φ
  obtain ⟨p, hp⟩ : ∃ p : ℂ[X], p = ∑ j ∈ Finset.range d, Polynomial.C (φ (c j)) * Polynomial.X ^ j := ⟨_, rfl⟩
  have hroot : ∀ u : ℂ, u ∉ F → p.eval u = 0 := by
    intro u hu
    have h1 := congrArg φ (h u hu)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h1
    rw [hp, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    calc _ = ∑ j ∈ Finset.range d, u ^ j * φ (c j) := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = 0 := h1
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ F.finite_toSet.infinite_compl
    intro u hu
    exact hroot u hu
  have hc : p.coeff s = 0 := by rw [hp0, Polynomial.coeff_zero]
  rw [hp, Polynomial.finset_sum_coeff] at hc
  simpa [Polynomial.coeff_C_mul_X_pow, Finset.mem_range.mp hs] using hc
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
