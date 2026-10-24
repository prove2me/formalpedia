-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_affineSubtract_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:25:21.113485+00:00
-- url     : https://prove2.me/submissions/4a02c4ad-3b79-4d8f-b04f-aba87be90963

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Translation by a finite real value commutes with an arbitrary EReal supremum. -/
theorem FunctionalInequalities.Analysis.iSup_add_coe {ι : Type*} (F : ι → EReal) (b : ℝ) :
    (⨆ i, F i + (b : EReal)) = (⨆ i, F i) + (b : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact add_le_add (le_iSup F i) le_rfl
  · apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot b)) (.inl (EReal.coe_ne_top b))).mp
    apply iSup_le
    intro i
    exact (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot b)) (.inl (EReal.coe_ne_top b))).mpr
      (le_iSup (fun j => F j + (b : EReal)) i)
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Exact conjugate formula, including infinite input/conjugate values. -/
theorem solution (f : E → EReal) (a : E) (b : ℝ) (y : E) :
    FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.affineSubtract f a b) y = FunctionalInequalities.Analysis.legendre f (y + a) + (b : EReal) := by
  have hterm (x : E) :
      (inner ℝ x y : EReal) - FunctionalInequalities.Analysis.affineSubtract f a b x =
        ((inner ℝ x (y + a) : EReal) - f x) + (b : EReal) := by
    change (inner ℝ x y : EReal) - (f x - ((inner ℝ a x + b : ℝ) : EReal)) =
      ((inner ℝ x (y + a) : EReal) - f x) + (b : EReal)
    generalize hz : f x = z
    induction z with
    | bot => simp
    | top =>
      rw [EReal.top_sub_coe]
      simp
    | coe z =>
      norm_cast
      simp only [inner_add_right, real_inner_comm a x]
      ring
  unfold FunctionalInequalities.Analysis.legendre
  simp_rw [hterm]
  exact FunctionalInequalities.Analysis.iSup_add_coe _ b
