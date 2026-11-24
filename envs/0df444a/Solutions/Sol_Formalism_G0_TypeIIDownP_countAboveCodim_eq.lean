-- Prove2me | solution 1 for Formalism.G0.TypeIIDownP.countAboveCodim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:46.57295+00:00
-- url     : https://prove2.me/submissions/06bcaf2a-812c-4369-9df7-694f6e27bf69

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.G0
namespace TypeIIDownP
open QVandermondeP
end TypeIIDownP
end Formalism.G0
namespace Formalism.G0
namespace TypeIIDownP
open QVandermondeP
private theorem finrank_map_mkQ_add_finrank_eq {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q]
    [Module.Finite F Q] (R U : Submodule F Q) (h : R ≤ U) :
    Module.finrank F (U.map R.mkQ) + Module.finrank F R = Module.finrank F U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (R.mkQ.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h1
  rw [← h1, (Submodule.comapSubtypeEquivOfLe h).finrank_eq]
private theorem le_comap_mkQ' {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q]
    (R : Submodule F Q) (V : Submodule F (Q ⧸ R)) : R ≤ V.comap R.mkQ := by
  intro x hx
  have h0 : R.mkQ x = 0 := by simpa using hx
  rw [Submodule.mem_comap, h0]
  exact V.zero_mem
private theorem mkQ_surjective' {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q]
    (R : Submodule F Q) : Function.Surjective R.mkQ :=
  LinearMap.range_eq_top.mp (Submodule.range_mkQ R)
end TypeIIDownP
end Formalism.G0
namespace Formalism.G0
namespace TypeIIDownP
open QVandermondeP
end TypeIIDownP
open TypeIIDownP QVandermondeP
end Formalism.G0
namespace Formalism.G0
end Formalism.G0
end

set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TypeIIDownP
open QVandermondeP
namespace Formalism.G0.TypeIIDownP
theorem _root_.solution {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q] [Finite Q]
    (R : Submodule F Q) (n j : ℕ) (hn : Module.finrank F Q = n) :
    Nat.card {U : Submodule F Q // R ≤ U ∧ Module.finrank F U + j = n} =
      Nat.card {V : Submodule F (Q ⧸ R) // Module.finrank F V + j = Module.finrank F (Q ⧸ R)} := by
  have : Module.Finite F Q := Module.Finite.of_finite
  have hQ := Submodule.finrank_quotient_add_finrank R
  exact Nat.card_congr
    { toFun := fun U => ⟨U.1.map R.mkQ, by
        have h1 := finrank_map_mkQ_add_finrank_eq R U.1 U.2.1
        have h2 := U.2.2
        omega⟩
      invFun := fun V => ⟨V.1.comap R.mkQ, le_comap_mkQ' R V.1, by
        have h1 := finrank_map_mkQ_add_finrank_eq R (V.1.comap R.mkQ) (le_comap_mkQ' R V.1)
        rw [Submodule.map_comap_eq_of_surjective (mkQ_surjective' R)] at h1
        have h2 := V.2
        omega⟩
      left_inv := fun U => Subtype.ext (by
        show Submodule.comap R.mkQ (Submodule.map R.mkQ U.1) = U.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr U.2.1])
      right_inv := fun V => Subtype.ext (by
        show Submodule.map R.mkQ (Submodule.comap R.mkQ V.1) = V.1
        exact Submodule.map_comap_eq_of_surjective (mkQ_surjective' R) V.1) }
end Formalism.G0.TypeIIDownP
