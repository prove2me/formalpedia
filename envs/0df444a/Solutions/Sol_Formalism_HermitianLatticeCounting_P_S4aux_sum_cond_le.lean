-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.sum_cond_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:26.639821+00:00
-- url     : https://prove2.me/submissions/17a63dba-4521-46a3-8d63-362ed663e89a

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {Ψ : Type*} [Fintype Ψ] (cond : Ψ → ℕ) (g B : ℕ → ℝ)
    (hb : ∀ i, ((univ.filter fun ψ => cond ψ = i).card : ℝ) * g i ≤ B i) :
    ∃ N, ∀ N' ≥ N, ∑ ψ, g (cond ψ) ≤ ∑ i ∈ range N', B i := by
  refine ⟨(univ.sup cond) + 1, fun N' hN' => ?_⟩
  have hmaps : ∀ ψ ∈ (univ : Finset Ψ), cond ψ ∈ range N' := fun ψ _ => by
    have := Finset.le_sup (f := cond) (Finset.mem_univ ψ)
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun i _ => ?_
  refine le_trans (le_of_eq ?_) (hb i)
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [(Finset.mem_filter.1 hψ).2] : ∀ ψ ∈ univ.filter (fun ψ => cond ψ = i), g (cond ψ) = g i),
    Finset.sum_const, nsmul_eq_mul]
end Formalism.HermitianLatticeCounting.P.S4aux
