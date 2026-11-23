-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.thMParts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:16.500862+00:00
-- url     : https://prove2.me/submissions/c7e3e786-5957-4fbf-a5b2-4130346e0451

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_sum_mem_lat

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
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H : SpanCharRing) : ThMParts := by
  intro E _ V _ _ O abelian₂ θ hθ hL n f f' hli hf hf' α α' hmem
  have h := (H E V O θ hθ n f f' hli α α').mp hmem
  have hα' : ∀ i, α' i ∈ O := fun i => (h i).1
  have hα : ∀ i, α i ∈ O := fun i => by
    obtain ⟨x, hx, e⟩ := (h i).2
    have : α i = θ * x - α' i := by rw [← e]; ring
    rw [this]; exact O.sub_mem (O.mul_mem hθ hx) (hα' i)
  exact ⟨fun i => ⟨hα i, hα' i⟩, sum_mem_lat hL hf hα, sum_mem_lat hL hf' hα'⟩
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
