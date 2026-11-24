-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.leakage_algebraic_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:24.26205+00:00
-- url     : https://prove2.me/submissions/f4817b4e-dd0c-487e-9fd1-2e42201b8059

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_Final_eichMove


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
theorem _root_.solution : LeakAlg := by
  intro E _ _ V _ _ h O abelian₂ th x x' u y v s hH hL hu hs h1 h2 h3
  have mv := Formalism.SL.Final.eichMove E V h x x' u s hH h1 h2 v h3
  refine ⟨?_, ?_, ?_⟩
  · rw [mv]; module
  · rintro ⟨w, hw, he⟩ ⟨d, hd, hk⟩
    refine ⟨w + d • (u + s • x), abelian₂.add_mem hw (hL d hd _ (abelian₂.add_mem hu hs)), ?_⟩
    rw [mv] at he
    rw [hk] at he
    have : y + h v u • x + (v + h v u • x') = (y + (v + h v u • (x + x') - (th * d) • (u + s • x))) + (th * d) • (u + s • x) := by module
    rw [this, he]; module
  · rw [mv]; module
end Formalism.HermitianLatticeCounting.P.S4aux
