-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.low_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:56.732311+00:00
-- url     : https://prove2.me/submissions/6e77e407-b741-40dd-b91d-542382b84e04

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sec_clsM_outM
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sec_clsM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_surj
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_int
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (R : Subring K) :
    Function.Bijective (fun p : (Quotient (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))) ×
        Quotient (QuotientGroup.rightRel (intSub R (lowW K g.1 g.2)))) ×
        Matrix (Fin g.1.sum) (Fin h.1.sum) (KR R) =>
      (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2)))
        (lowJ hN hW (p.1.1.out, p.1.2.out) (outM R p.2)))) := by
  have key : ∀ (a a' : lowW K h.1 h.2 × lowW K g.1 g.2) (x x' : Matrix (Fin g.1.sum) (Fin h.1.sum) K),
      Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) (lowJ hN hW a x) =
        Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) (lowJ hN hW a' x') →
      ∃ b : lowW K h.1 h.2 × lowW K g.1 g.2, ∃ ρ : Matrix (Fin g.1.sum) (Fin h.1.sum) K,
        (b.1 ∈ intSub R (lowW K h.1 h.2) ∧ b.2 ∈ intSub R (lowW K g.1 g.2)) ∧ (∀ i j, ρ i j ∈ R) ∧
          a' = b * a ∧ x' = ρ + sec_m b.2 * x * (sec_m b.1)⁻¹ := by
    intro a a' x x' e
    obtain ⟨k, hk, e2⟩ := (sec_right_eq _ _ _).1 e
    obtain ⟨b, ρ, rfl⟩ := lowJ_surj hN hW k
    rw [lowJ_mul] at e2
    obtain ⟨h1, h2⟩ := lowJ_inj hN hW e2
    exact ⟨b, ρ, ((lowJ_int hN hW R b ρ).1 hk).1, ((lowJ_int hN hW R b ρ).1 hk).2, h1, h2⟩
  have conv : ∀ (a b : lowW K h.1 h.2 × lowW K g.1 g.2) (x ρ : Matrix (Fin g.1.sum) (Fin h.1.sum) K),
      (b.1 ∈ intSub R (lowW K h.1 h.2) ∧ b.2 ∈ intSub R (lowW K g.1 g.2)) → (∀ i j, ρ i j ∈ R) →
      Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) (lowJ hN hW a x) =
        Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2)))
          (lowJ hN hW (b * a) (ρ + sec_m b.2 * x * (sec_m b.1)⁻¹)) := by
    intro a b x ρ hb hρ
    exact (sec_right_eq _ _ _).2 ⟨lowJ hN hW b ρ, (lowJ_int hN hW R b ρ).2 ⟨hb, hρ⟩,
      (lowJ_mul hN hW b a ρ x).symm⟩
  refine sec_fib
    (fun a : lowW K h.1 h.2 × lowW K g.1 g.2 =>
      (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))) a.1,
        Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K g.1 g.2))) a.2))
    (fun q => (q.1.out, q.2.out))
    (fun q => Prod.ext (Quotient.out_eq q.1) (Quotient.out_eq q.2))
    (clsM R) (outM R) (sec_clsM_outM R)
    (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))))
    Quotient.mk_surjective (fun a x => lowJ hN hW a x) (lowJ_surj hN hW) ?_ ?_ ?_
  · intro a x a' x' e
    obtain ⟨b, ρ, ⟨hb1, hb2⟩, -, rfl, -⟩ := key a a' x x' e
    refine Prod.ext ((sec_right_eq _ _ _).2 ⟨b.1, hb1, ?_⟩) ((sec_right_eq _ _ _).2 ⟨b.2, hb2, ?_⟩)
    · rfl
    · rfl
  · intro a x x'
    constructor
    · intro e
      obtain ⟨b, ρ, -, hρ, hab, rfl⟩ := key a a x x' e
      have hb : b = 1 := mul_right_cancel (hab.symm.trans (one_mul a).symm)
      subst hb
      rw [sec_clsM_eq]
      intro i j
      simpa [sec_m] using hρ i j
    · intro e
      rw [sec_clsM_eq] at e
      have := conv a 1 x (x' - x) ⟨one_mem _, one_mem _⟩ e
      simpa [sec_m] using this
  · intro a a' e x
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    obtain ⟨g1, hg1, hg1e⟩ := (sec_right_eq _ _ _).1 e1
    obtain ⟨g2, hg2, hg2e⟩ := (sec_right_eq _ _ _).1 e2
    refine ⟨sec_m (a' * a⁻¹).2 * x * (sec_m (a' * a⁻¹).1)⁻¹, ?_⟩
    have m1 : (a' * a⁻¹).1 ∈ intSub R (lowW K h.1 h.2) := by
      rw [show (a' * a⁻¹).1 = g1 by simp [hg1e]]
      exact hg1
    have m2 : (a' * a⁻¹).2 ∈ intSub R (lowW K g.1 g.2) := by
      rw [show (a' * a⁻¹).2 = g2 by simp [hg2e]]
      exact hg2
    have := conv a (a' * a⁻¹) x 0 ⟨m1, m2⟩ (fun i j => by simp)
    simpa using this
end Formalism.FourierDecayAlt.P.TwoBlockPoint
