-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.intK_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:53.239406+00:00
-- url     : https://prove2.me/submissions/22f9aca2-ebf1-4917-8d19-8eed2da2085d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat__081cc429fc9c
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_smul_inv_smul__6c6ecc43c969
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Hess_quotE_out
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
theorem _root_.solution (R : Subring K) (b : Kˣ) (Λ : AddSubgroup K)
    (hvol : volL R (mulLat (b : K) Λ) = modK R (b : K) * volL R Λ) {d : ℕ}
    (f f' : (Fin d → K) → ℂ) (hff : ∀ ξ, f' ((b : K) • ξ) = f ξ) (hinv : LatInvN Λ f) :
    LatInvN (mulLat (b : K) Λ) f' ∧
      intK R (mulLat (b : K) Λ) d f' = ((modK R (b : K) : ℝ) : ℂ) ^ d * intK R Λ d f := by
  have hI : LatInvN (mulLat (b : K) Λ) f' := by
    intro x l hl
    have hl' : ∀ i, (((b⁻¹ : Kˣ) : K) • l) i ∈ Λ := fun i => (mem_mulLat' b Λ (l i)).1 (hl i)
    have := hinv (((b⁻¹ : Kˣ) : K) • x) (((b⁻¹ : Kˣ) : K) • l) hl'
    rw [← hff, ← hff, smul_add, smul_inv_smul', smul_inv_smul'] at this
    exact this
  refine ⟨hI, ?_⟩
  unfold intK
  rw [hvol, Complex.ofReal_mul, mul_pow, mul_assoc]
  congr 2
  rw [← finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin d => (quotE b Λ).toEquiv)]
  refine finsum_congr fun y => ?_
  rw [← hff]
  have := hI ((b : K) • fun i => (Quotient.out (y i) : K))
    (fun i => (Quotient.out (quotE b Λ (y i)) : K) - (b : K) * (Quotient.out (y i) : K))
    (fun i => quotE_out b Λ (y i))
  rw [← this]
  congr 1
  ext i
  simp
end Formalism.FourierDecayAlt.P.A6x7.Hess
