-- Prove2me | solution 1 for Formalism.L2.SG.Sub.mem_stabT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:24.929287+00:00
-- url     : https://prove2.me/submissions/17687c1d-b131-45e7-bb33-5c7c3ec05b9c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Sub
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
namespace Formalism.L2.SG.Sub
theorem _root_.solution {a : ℕ} (X : Fin a → Fin n → E) (g : HA R σ J) :
    g ∈ stabT R σ J X ↔ ∀ b, lin R σ J g (ratV (F := F) R (X b)) = ratV (F := F) R (X b) := by
  rw [stabT, MulAction.mem_stabilizer_iff]
  constructor
  · intro h b
    exact congrFun h b
  · intro h
    funext b
    exact h b
end Formalism.L2.SG.Sub
