-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:56:32.615859+00:00
-- url     : https://prove2.me/submissions/b8e9bf88-7fe5-4aca-97c4-071f2f2f6bf3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_half
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_qm_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ)
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc ((m + 1 : ℕ) : ℕ∞) Φ g) :
    qminorOp (Q.EH k r) a (b ∘ Equiv.swap i.castSucc i.succ) u Φ g = -qminorOp (Q.EH k r) a b u Φ g := by
  have hne : i.castSucc ≠ i.succ := (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne
  have hsg : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (σ * Equiv.swap i.castSucc i.succ) : ℤ) : ℂ) = -((Equiv.Perm.sign σ : ℤ) : ℂ) := by
    intro σ
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
    push_cast
    ring
  have hre : ∀ c : Fin (m + 1) → Fin (2 * r + k + 1),
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a c u (σ * Equiv.swap i.castSucc i.succ) Φ g =
        -∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a c u σ Φ g := by
    intro c
    rw [← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i.castSucc i.succ)) _ _
      (fun σ => by simp only [Equiv.coe_mulRight, hsg, neg_smul, neg_neg])
  have hsum : ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (PP a b u σ Φ g - PP a b u (σ * Equiv.swap i.castSucc i.succ) Φ g
        + PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g
        - PP a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) Φ g) = 0 :=
    Finset.sum_eq_zero fun σ _ => by rw [key a b i u σ Φ g hg hloc, smul_zero]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hre] at hsum
  rw [qm_eq, qm_eq]
  have h2 := half _ (show ((∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a b u σ Φ g) +
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g) +
      ((∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a b u σ Φ g) +
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g) = 0
    by rw [← hsum]; abel)
  exact eq_neg_of_add_eq_zero_right h2
end Formalism.FourierDecayAlt.P.FourTermExpansion
