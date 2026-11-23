-- Prove2me | solution 1 for Formalism.UG.P.cT_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:33.78214+00:00
-- url     : https://prove2.me/submissions/9f2bff48-b270-4e97-92e6-1a14a289256f

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) {m p : Type} (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm
end Formalism.UG.P
