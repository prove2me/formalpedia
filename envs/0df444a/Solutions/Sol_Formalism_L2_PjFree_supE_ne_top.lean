-- Prove2me | solution 1 for Formalism.L2.PjFree.supE_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:58.271459+00:00
-- url     : https://prove2.me/submissions/2d40369f-9215-4f66-9b08-9faa0d6b9bf8

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Theorems.Thm_Formalism_L2_PjFree_supE_add_le
import Theorems.Thm_Formalism_L2_PjFree_supE_smul
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)
namespace Formalism.L2.PjFree
theorem _root_.solution [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc _ ≤ C p.1 := hC p.1 p.2.1 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| :=
        Finset.single_le_sum (f := fun c => |C c|) (fun c _ => abs_nonneg _) (Finset.mem_univ _)
  | zero =>
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 0)) (iSup_le fun p => ?_)
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    simp
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP
end Formalism.L2.PjFree
