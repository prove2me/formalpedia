-- Prove2me | solution 1 for Formalism.L2.DIV.fk_det_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:38.243713+00:00
-- url     : https://prove2.me/submissions/e5ca2616-fbcc-4213-bf09-c69c2af6dc5f

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)
namespace Formalism.L2.DIV
theorem _root_.solution {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (hG : ∀ a b, G a b ∈ K0) : G.det ∈ K0 := by
  let G0 : Matrix (Fin n) (Fin n) K0 := fun a b => ⟨G a b, hG a b⟩
  have hG0 : G = G0.map K0.subtype := by
    ext a b
    rfl
  rw [hG0, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (G0.det).2
end Formalism.L2.DIV
