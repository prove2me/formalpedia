-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.filtered_mul_mul_sub_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:42.337115+00:00
-- url     : https://prove2.me/submissions/faa8b761-9dfe-44dc-9163-114c6ae9af0e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_add
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_mono
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k : ℕ}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {a b c : Matrix ι ι K} (ha : InPat lv k (a - 1)) (hb : InPat lv k (b - 1))
    (hc : InPat lv k (c - 1)) : InPat lv (k + k) (a * b * c - 1 - ((a - 1) + (b - 1) + (c - 1))) := by
  obtain ⟨A, rfl⟩ : ∃ A, a = 1 + A := ⟨a - 1, by abel⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = 1 + B := ⟨b - 1, by abel⟩
  obtain ⟨C, rfl⟩ : ∃ C, c = 1 + C := ⟨c - 1, by abel⟩
  simp only [add_sub_cancel_left] at ha hb hc ⊢
  have e : (1 + A) * (1 + B) * (1 + C) - 1 - (A + B + C) = A * B + A * C + B * C + A * B * C := by
    noncomm_ring
  rw [e]
  exact inPat_add (inPat_add (inPat_add (inPat_mul ha hb) (inPat_mul ha hc))
    (inPat_mul hb hc)) (inPat_mono (by omega) (inPat_mul (inPat_mul ha hb) hc))
end Formalism.L2.SG.Pf.Unip
