-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem_comm_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.237721+00:00
-- url     : https://prove2.me/submissions/4239278d-9144-45f4-abf9-3792ff4a1a50

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (k : G) :
    centralIdem ρ * MonoidAlgebra.of ℂ G k = MonoidAlgebra.of ℂ G k * centralIdem ρ := by
  have hc : ∀ h : G, ρ.character (k⁻¹ * (h * k)) = ρ.character h := by
    first
      | exact fun h => by simpa [mul_assoc] using ρ.char_conj h k⁻¹
      | (intro h; unfold Representation.character; done)
  unfold centralIdem
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ (fun g => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, smul_mul_assoc,
    mul_smul_comm, ← map_mul, mul_inv_rev, mul_assoc, hc, mul_inv_cancel_left]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
