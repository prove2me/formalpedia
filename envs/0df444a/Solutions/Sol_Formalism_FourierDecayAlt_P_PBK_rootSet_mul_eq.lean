-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.rootSet_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:49.23626+00:00
-- url     : https://prove2.me/submissions/7a50e786-2804-441a-a4af-41581931b3f4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0) (hz : z ^ s = w) (hρ : ρ ^ s = l)
    (hl : l ≠ 0) : G.rootSet s (l * w) = (G.rootSet s 1).image (fun ζ => ζ * ρ * z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hz, zero_pow hs])
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hl (by rw [← hρ, zero_pow hs])
  ext y
  rw [Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs, Finset.mem_image]
  constructor
  · intro hy
    refine ⟨y / (ρ * z), (Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mpr ?_, ?_⟩
    · rw [div_pow, mul_pow, hρ, hz, hy, div_self (mul_ne_zero hl hw)]
    · field_simp
  · rintro ⟨ζ, hζ, rfl⟩
    rw [Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs] at hζ
    rw [mul_pow, mul_pow, hζ, hρ, hz, one_mul]
end Formalism.FourierDecayAlt.P.PBK
