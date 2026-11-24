-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.ch_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:36:35.388823+00:00
-- url     : https://prove2.me/submissions/3f556130-4a9c-4a47-8651-5da4844d2bd7

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_polyVanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_pow_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_main
import Theorems.Thm_PI_QmLemDWork_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
section pol
variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
end pol
private theorem shift_sum_lemma {W : Type} [AddCommGroup W] [Module ℂ W] (d : ℕ) (a : ℕ → W) (u : ℂ) :
    ∑ s ∈ Finset.range (d + 1), u ^ s • shiftC a s = u • ∑ s ∈ Finset.range d, u ^ s • a s := by
  rw [Finset.sum_range_succ', Finset.smul_sum]
  simp only [shiftC, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s _ => by rw [pow_succ', mul_smul])
private theorem ite_sum_lemma_2 {W : Type} [AddCommGroup W] [Module ℂ W] (d : ℕ) (b : ℕ → W) (u : ℂ) :
    ∑ s ∈ Finset.range (d + 1), u ^ s • (if s < d then b s else 0) = ∑ s ∈ Finset.range d, u ^ s • b s := by
  rw [Finset.sum_range_succ]
  simp only [lt_irrefl, if_false, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s hs => by rw [if_pos (Finset.mem_range.mp hs)])
private theorem coeff_sum_lemma_3 {W : Type} [AddCommGroup W] [Module ℂ W] (d : ℕ) (P : ℂ[X])
    (hP : P.natDegree < d + 1) (Y : W) (u : ℂ) :
    ∑ s ∈ Finset.range (d + 1), u ^ s • (P.coeff s • Y) = P.eval u • Y := by
  rw [Polynomial.eval_eq_sum_range' hP, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun s _ => by rw [← mul_smul, mul_comm])
section ring
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}
end ring
section cov
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
end cov
section main
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
end main
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
end
end

set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W] (G : Submodule ℂ W) (K : Module.End ℂ W)
    (hK : ∀ X ∈ G, K X ∈ G) (d : ℕ) (A : ℕ → W → W) (P : ℂ[X]) (hP : P.natDegree < d + 1)
    (h : ∀ (u : ℂ), ∀ X ∈ G, u • (∑ s ∈ Finset.range d, u ^ s • A s X) - ∑ s ∈ Finset.range d, u ^ s • A s (K X) =
      P.eval u • X) :
    ∀ X ∈ G, Polynomial.aeval K P X = 0 := by
  have hcoef : ∀ Y ∈ G, ∀ s ∈ Finset.range (d + 1),
      shiftC (fun t => A t Y) s - (if s < d then A s (K Y) else 0) - P.coeff s • Y = 0 := by
    intro Y hY
    apply polyVanish (d + 1) _ ∅
    intro u _
    have h1 := h u Y hY
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [shift_sum_lemma, ite_sum_lemma_2, coeff_sum_lemma_3 d P hP Y u, h1, sub_self]
  intro X hX
  rw [Polynomial.aeval_eq_sum_range' hP, LinearMap.sum_apply]
  have hterm : ∀ i ∈ Finset.range (d + 1), (P.coeff i • (K ^ i)) X =
      shiftC (fun t => A t ((K ^ i) X)) i - (if i < d then A i ((K ^ (i + 1)) X) else 0) := by
    intro i hi
    have h1 := hcoef ((K ^ i) X) (Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.pow_mem G K hK i X hX) i hi
    rw [sub_eq_zero] at h1
    rw [LinearMap.smul_apply, pow_succ']
    first
      | rw [Module.End.mul_apply]
      | rw [LinearMap.mul_apply]
    exact h1.symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ, Finset.sum_sub_distrib]
  have hg : ∀ i ∈ Finset.range d, (if i < d then A i ((K ^ (i + 1)) X) else 0) =
      shiftC (fun t => A t ((K ^ (i + 1)) X)) (i + 1) := by
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
    rfl
  rw [Finset.sum_congr rfl hg, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun i => shiftC (fun t => A t ((K ^ i) X)) i)]
  simp [shiftC]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
