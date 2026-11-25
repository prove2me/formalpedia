-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.splitAt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:03.506805+00:00
-- url     : https://prove2.me/submissions/e2cec7d6-1ea6-4f88-91a6-03f8c8351848

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hE : ExactAt S π h)
    (hR : RebaseAt S π h) : SplitAt S π h := by
  intro ι _ _ b e i₀ horth hunit hmin ξ hξ hξu
  obtain ⟨X, hX, hXX⟩ := hE ι b e i₀ horth hunit hmin ξ hξ hξu
  have hXu : IsUnitIn S (h X X * (π ^ e i₀)⁻¹) := by rw [hXX]; exact hξu
  obtain ⟨c, hco, hcu, hc0, hsp, hmem⟩ := hR ι b e i₀ horth hunit hmin X hX hXu
  exact ⟨c, hco, hcu, by rw [hc0, hXX], hsp, hmem⟩
end Formalism.L2.SG.Pf.G3
