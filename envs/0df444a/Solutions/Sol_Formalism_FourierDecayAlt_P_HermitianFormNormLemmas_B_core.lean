-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:56.709816+00:00
-- url     : https://prove2.me/submissions/3b370c33-673f-4a0d-a984-4c5c2189218b

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution (hS4 : Formalism.HermitianLatticeCounting.S4.Step4) (L : LocalNG Cl Nu) (κ : ℕ) (Xp Yp : L.P → ℝ)
    (hX : ∀ p, 1 ≤ Xp p) (hY : ∀ p, 1 ≤ Yp p) (hb : L.Basic)
    (h1 : ∀ p ∈ L.Om, ∑ d, L.wt p d * ‖L.aN p d‖ ^ 2 ≤ Xp p * ((L.q p : ℝ) ^ κ)⁻¹ * L.nn p)
    (h2 : ∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ Xp p * L.nn p)
    (h3 : ∀ p, L.nn p ≤ Yp p * L.ngen p) :
    ∑ d, (∏ p, L.wt p (d p)) * ‖L.ampNG d‖ ^ 2 ≤
      (4 : ℝ) ^ L.Om.card * (∏ p, Xp p * Yp p) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, L.ngen p := by
  unfold Formalism.HermitianLatticeCounting.S4.Step4 at hS4
  have hb' := hb
  unfold LocalNG.Basic at hb'
  obtain ⟨hw, _, hq, _, hnn, _, _⟩ := hb'
  have key := hS4 L.P L.Om L.D L.wt L.aN L.aZ (fun _ => 1) (fun p => Xp p * L.nn p)
    (fun p => Xp p * Yp p * L.ngen p) L.q 0 κ hw (fun _ => le_refl _) hq
    (fun p => mul_nonneg (by linarith [hX p]) (hnn p))
    (fun p hp => (h1 p hp).trans (le_of_eq (by simp only [pow_zero, one_mul]; ring)))
    (fun p => (h2 p).trans (le_of_eq (by simp only [pow_zero, one_mul])))
    (fun p => by
      simp only [pow_zero, one_mul]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h3 p) (by linarith [hX p]))
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · unfold LocalNG.ampNG
    first
    | rfl
    | congr!
  · simp only [Finset.prod_const_one, one_pow, mul_one, Finset.prod_mul_distrib] <;> ring
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
