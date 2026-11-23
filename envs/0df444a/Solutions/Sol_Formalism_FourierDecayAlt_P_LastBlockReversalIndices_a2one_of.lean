-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LastBlockReversalIndices.a2one_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:14.296692+00:00
-- url     : https://prove2.me/submissions/7b7dc54b-ccb4-4f84-8153-e3612128f36e

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_LastBlockReversalIndices_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_LastBlockReversalIndices_lam_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LastBlockReversalIndices
open Formalism.DoubleCosetMeasures MeasureTheory
namespace Formalism.FourierDecayAlt.P.LastBlockReversalIndices
theorem _root_.solution
    (hW : ∀ (K : Type) [CommRing K] (l : List ℕ) (t : ℕ → Kˣ) (N : Fin (l ++ [1]).sum),
      N.val + 1 = (l ++ [1]).sum → (pt (l ++ [1]) t)⁻¹ N N = (((t l.length)⁻¹ : Kˣ) : K)) :
    Formalism.FourierDecayAlt.A.LevelOneKernelPoint := by
  intro K _ _ _ R l t ψ C _ _ e lam μ₁ μ₂ hB
  obtain ⟨p, hp⟩ : ∃ p, phi R (l ++ [1]) t ψ C e lam p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hB
    unfold BB
    rw [show phi R (l ++ [1]) t ψ C e lam = fun _ => 0 from funext hcon]
    simp
  unfold phi at hp
  have h1 := left_ne_zero_of_mul hp
  split_ifs at h1 with hI
  · have h2 : Nat.card (isoSet R ((((p.1 : GL (Fin (l ++ [1]).sum) K)) :
        Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K) * pt (l ++ [1]) t *
        ((p.2 : GL (Fin (l ++ [1]).sum) K) : Matrix (Fin (l ++ [1]).sum) (Fin (l ++ [1]).sum) K))
        C e lam) ≠ 0 := by exact_mod_cast h1
    obtain ⟨⟨φ, hφ1, hφ2⟩⟩ := (Nat.card_ne_zero.mp h2).1
    have hN : ((⟨l.sum, by simp⟩ : Fin (l ++ [1]).sum) : ℕ) + 1 = (l ++ [1]).sum := by simp
    rw [← hφ1, eZ, hφ2, lam_last R ⟨l.sum, by simp⟩ hN, entry _ hN _ _ _ p.1.2.1 p.2.2,
      hW K l t _ hN]
  · exact absurd rfl h1
end Formalism.FourierDecayAlt.P.LastBlockReversalIndices
