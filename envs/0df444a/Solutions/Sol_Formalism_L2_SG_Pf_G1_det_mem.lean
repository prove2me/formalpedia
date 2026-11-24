-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:31.051938+00:00
-- url     : https://prove2.me/submissions/a2c5b70c-0570-4318-99c7-4ecb243596c4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K}
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} (x : Fin n → V) (hx : ∀ i j, h (x i) (x j) ∈ S) :
    (U0.gram h x).det ∈ S := by
  have key := RingHom.map_det S.subtype (Matrix.of fun i j => (⟨h (x i) (x j), hx i j⟩ : S))
  have e : S.subtype.mapMatrix (Matrix.of fun i j => (⟨h (x i) (x j), hx i j⟩ : S)) = U0.gram h x := by
    ext i j
    rfl
  rw [e] at key
  rw [← key]
  exact Subtype.mem _
end Formalism.L2.SG.Pf.G1
