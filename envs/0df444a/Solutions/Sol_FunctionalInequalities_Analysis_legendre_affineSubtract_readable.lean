-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_affineSubtract_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:17.879327+00:00
-- url     : https://prove2.me/submissions/f3c774d3-f528-47fb-bcbb-63833aadf673

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine

noncomputable section
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
