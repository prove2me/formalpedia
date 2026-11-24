-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:27.975118+00:00
-- url     : https://prove2.me/submissions/37ae772d-d079-451d-8c32-bd7a8c6bc1d3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_orbZ_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_phase_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sigma_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_term_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_Fz_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_bbZ_eq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_toCos_rep
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_psi_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite
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
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
include hW
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution [TopologicalSpace K] [IsTopologicalRing K] (ψ : AddChar K ℂ)
    (hD : LocalDatum K R ψ) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) :
    bbZ R ψ w Z' = omPhi R ψ g (PhiH R ψ h Z') := by
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A6x4.psi_one hD hr
  set T : Cos R w → ℂ := fun q => Fz R Z' (orbZ w (rep R q)) * phase ψ (rep R q) with hT
  have hfin : (Function.support T).Finite := by
    refine (integral_points_finite K R ψ hD w).subset fun q hq => ?_
    by_contra hc
    apply hq
    have hc' : ¬ IsInt R (orbZ w (rep R q)) := hc
    simp only [hT, Fz, if_neg hc', zero_mul]
  let β : Par R h g → Cos R w := fun t => toCos R (sigma R hN hW t)
  have hβ : Function.Bijective β := sigma_bij R hN hW
  let e : Cos R g × (Cos R h × Matrix (Fin g.1.sum) (Fin h.1.sum) (KR R) ×
      Matrix (Fin h.1.sum) (Fin g.1.sum) (KR R)) ≃ Par R h g :=
    { toFun := fun x => ((x.2.1, x.1), x.2.2)
      invFun := fun t => (t.1.2, (t.1.1, t.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hβe : Function.Bijective (β ∘ e) := hβ.comp e.bijective
  have hfin2 : (Function.support (T ∘ (β ∘ e))).Finite := by
    rw [Function.support_comp_eq_preimage]
    exact hfin.preimage hβe.injective.injOn
  rw [bbZ_eq]
  rw [← finsum_eq_of_bijective (β ∘ e) hβe (fun x => rfl : ∀ x, (T ∘ (β ∘ e)) x = T ((β ∘ e) x))]
  rw [finsum_curry _ hfin2]
  unfold omPhi
  refine finsum_congr fun q => ?_
  unfold PhiH
  rw [mul_comm, ← smul_eq_mul, smul_finsum]
  refine finsum_congr fun τ => ?_
  show T (toCos R (sigma R hN hW ((τ.1, q), τ.2))) = _
  rw [hT]
  show Fz R Z' (orbZ w (rep R (toCos R (sigma R hN hW ((τ.1, q), τ.2))))) *
    phase ψ (rep R (toCos R (sigma R hN hW ((τ.1, q), τ.2)))) = _
  rw [term_inv R ψ hψ w Z' _ (sigma R hN hW ((τ.1, q), τ.2)) (A5x8.inv_toCos_rep R _)]
  unfold sigma
  rw [orbZ_J, phase_J, Fz_cast]
  show Fz R Z' (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) (orbZ g (rep R q))) *
    (phase ψ (rep R τ.1) * ψ (cornL (outM R τ.2.1) + cornU (outM R τ.2.2)) * phase ψ (rep R q)) = _
  rw [smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.TwoBlockPoint
