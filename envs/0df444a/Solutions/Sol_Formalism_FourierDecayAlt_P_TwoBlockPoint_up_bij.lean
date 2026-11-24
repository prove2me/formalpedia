-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.up_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:59.58179+00:00
-- url     : https://prove2.me/submissions/87384f74-fadf-455d-b7bd-93159fec1851

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sec_clsM_outM
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sec_clsM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_upJ_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_upJ_surj
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_upJ_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_upJ_int
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
    Function.Bijective (fun p : ((upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)) ×
        (upUniG K g.1.sum ⧸ intSub R (upUniG K g.1.sum))) ×
        Matrix (Fin h.1.sum) (Fin g.1.sum) (KR R) =>
      ((upJ hN (p.1.1.out, p.1.2.out) (outM R p.2) : upUniG K w.1.sum) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum))) := by
  have key : ∀ (a a' : upUniG K h.1.sum × upUniG K g.1.sum) (x x' : Matrix (Fin h.1.sum) (Fin g.1.sum) K),
      (QuotientGroup.mk (upJ hN a x) : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) =
        QuotientGroup.mk (upJ hN a' x') →
      ∃ b : upUniG K h.1.sum × upUniG K g.1.sum, ∃ ρ : Matrix (Fin h.1.sum) (Fin g.1.sum) K,
        (b.1 ∈ intSub R (upUniG K h.1.sum) ∧ b.2 ∈ intSub R (upUniG K g.1.sum)) ∧ (∀ i j, ρ i j ∈ R) ∧
          a' = a * b ∧ x' = ρ + (sec_m b.1)⁻¹ * x * sec_m b.2 := by
    intro a a' x x' e
    rw [QuotientGroup.eq] at e
    obtain ⟨b, ρ, hk⟩ := upJ_surj hN ((upJ hN a x)⁻¹ * upJ hN a' x')
    rw [hk] at e
    have e2 : upJ hN a' x' = upJ hN a x * upJ hN b ρ := by
      rw [← hk, mul_inv_cancel_left]
    rw [upJ_mul] at e2
    obtain ⟨h1, h2⟩ := upJ_inj hN e2
    exact ⟨b, ρ, ((upJ_int hN R b ρ).1 e).1, ((upJ_int hN R b ρ).1 e).2, h1, h2⟩
  have conv : ∀ (a b : upUniG K h.1.sum × upUniG K g.1.sum) (x ρ : Matrix (Fin h.1.sum) (Fin g.1.sum) K),
      (b.1 ∈ intSub R (upUniG K h.1.sum) ∧ b.2 ∈ intSub R (upUniG K g.1.sum)) → (∀ i j, ρ i j ∈ R) →
      (QuotientGroup.mk (upJ hN a x) : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) =
        QuotientGroup.mk (upJ hN (a * b) (ρ + (sec_m b.1)⁻¹ * x * sec_m b.2)) := by
    intro a b x ρ hb hρ
    rw [QuotientGroup.eq, ← upJ_mul, inv_mul_cancel_left]
    exact (upJ_int hN R b ρ).2 ⟨hb, hρ⟩
  refine sec_fib
    (fun a : upUniG K h.1.sum × upUniG K g.1.sum =>
      ((a.1 : upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)),
        (a.2 : upUniG K g.1.sum ⧸ intSub R (upUniG K g.1.sum))))
    (fun q => (q.1.out, q.2.out))
    (fun q => Prod.ext (QuotientGroup.out_eq' q.1) (QuotientGroup.out_eq' q.2))
    (clsM R) (outM R) (sec_clsM_outM R)
    (QuotientGroup.mk : upUniG K w.1.sum → upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum))
    QuotientGroup.mk_surjective (fun a x => upJ hN a x) (upJ_surj hN) ?_ ?_ ?_
  · intro a x a' x' e
    obtain ⟨b, ρ, ⟨hb1, hb2⟩, -, rfl, -⟩ := key a a' x x' e
    refine Prod.ext (QuotientGroup.eq.2 ?_) (QuotientGroup.eq.2 ?_)
    · simpa using hb1
    · simpa using hb2
  · intro a x x'
    constructor
    · intro e
      obtain ⟨b, ρ, -, hρ, hab, rfl⟩ := key a a x x' e
      have hb : b = 1 := mul_left_cancel (hab.symm.trans (mul_one a).symm)
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
    rw [QuotientGroup.eq] at e1 e2
    refine ⟨(sec_m (a⁻¹ * a').1)⁻¹ * x * sec_m (a⁻¹ * a').2, ?_⟩
    have := conv a (a⁻¹ * a') x 0 ⟨by simpa using e1, by simpa using e2⟩ (fun i j => by simp)
    simpa using this
end Formalism.FourierDecayAlt.P.TwoBlockPoint
