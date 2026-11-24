-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_R_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.507314+00:00
-- url     : https://prove2.me/submissions/34ef7a74-64c5-4677-8a61-53d44375ed1a

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_xi_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
variable {N r : ℕ} [NeZero r] {D : BlockData N}
omit [NeZero r]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {t b : ℕ} (c : Fin r) {g : MvPolynomial (BVar N r t) ℚ_[p]} (hg : g ∈ po_R p N r t b) :
    pderiv (xiVar N r t c) g ∈ po_R p N r t (b - 1) := by
  classical
  rw [mem_restrictSupport_iff] at hg ⊢
  intro m hm
  have hm' : m + Finsupp.single (xiVar N r t c) 1 ∈ g.support := by
    rw [Finset.mem_coe, mem_support_iff, coeff_pderiv] at hm
    rw [mem_support_iff]
    exact left_ne_zero_of_mul hm
  obtain ⟨h1, h2⟩ := hg (Finset.mem_coe.mpr hm')
  refine ⟨fun v hv => h1 v ?_, ?_⟩
  · rw [Finsupp.mem_support_iff] at hv ⊢
    rw [Finsupp.add_apply]
    omega
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h2
    rw [Finset.sum_eq_single c (fun d _ hd => Finsupp.single_eq_of_ne (fun h => hd (po_xi_inj h)))
      (fun h => absurd (Finset.mem_univ c) h), Finsupp.single_eq_same] at h2
    omega
end Formalism.InvariantFactorPaths.KP.LL
