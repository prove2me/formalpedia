-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:47.341361+00:00
-- url     : https://prove2.me/submissions/fb89a6ae-dc47-472d-bb5c-292eb5997b0a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplPick
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplNeg
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplEdge
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {C₂ : ℝ} (hC₂ : 0 < C₂) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (T δ E : ℝ) (s : ℂ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hδ0 : 0 < δ) (him : |s.im| ≤ T + 1) (hE : 1 / ‖s - 1‖ ≤ E) (hE0 : 0 ≤ E)
    (h : ‖negLD χ s‖ ≤ C₂ * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0)) :
    ‖negLD χ s‖ ≤ C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + E := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 := exm_log_le (M : ℝ) T |s.im| hM' hT (abs_nonneg _) him
  have h2 : (if χ = 1 then 1 / ‖s - 1‖ else 0) ≤ E := by split_ifs <;> assumption
  refine h.trans (add_le_add ?_ h2)
  gcongr
end Formalism.HermitianLattices.Ext.PrimesInProgressions
