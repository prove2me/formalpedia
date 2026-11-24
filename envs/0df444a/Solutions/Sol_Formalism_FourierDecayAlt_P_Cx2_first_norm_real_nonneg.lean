-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.first_norm_real_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:39.484575+00:00
-- url     : https://prove2.me/submissions/1b11af48-036c-48c3-9dd7-6b9a0986363c

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx1_psd_pullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_schur_product


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (S : HidaSetting E Wp Wq) (hP : ThmPPos S) (ε : ℝ) (hε : 0 < ε) (i : ℕ)
    (hi : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (hκ : TB.PSDOn Y κ) (c : J.CV E) :
    ∃ x : ℝ, 0 ≤ x ∧ S.N1 ε i w.1 Y κ c = x := by
  classical
  let k : Option (Fin S.f) → TB.Pt E → TB.Pt E → ℂ := fun o => match o with
    | none => κ
    | some v => fun h h' => S.gramLoc v ε i (w.1 v) (loc (S.σ v) h ++ [(1, c (S.pl v))])
        (loc (S.σ v) h' ++ [(1, c (S.pl v))])
  have hk : ∀ o, TB.PSDOn Y (k o) := by
    intro o
    cases o with
    | none => exact hκ
    | some v =>
      exact Cx1.psd_pullback Y (fun h => loc (S.σ v) h ++ [(1, c (S.pl v))]) _ _
        (fun x hx => Finset.mem_image_of_mem _ hx) (hP v ε hε i hi w _)
  have hM := schur_product (TB.Pt E) (Option (Fin S.f)) Y k hk
  have hsum : 0 ≤ ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))]) := by
    have h3 : ∀ F : TB.Pt E → TB.Pt E → ℂ,
        ∑ a ∈ Y.attach, ∑ b ∈ Y.attach, F a b = ∑ a ∈ Y, ∑ b ∈ Y, F a b := by
      intro F
      rw [← Finset.sum_attach Y (fun a => ∑ b ∈ Y, F a b)]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_attach Y (F a)
    have := hM.dotProduct_mulVec_nonneg (fun _ => 1)
    simp [dotProduct, Matrix.mulVec, Fintype.prod_option, k] at this
    exact this.trans_eq (h3 (fun h h' => κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))])))
  have hsize : 0 ≤ Word.size S.P w.1 :=
    Finset.prod_nonneg fun v _ => List.prod_nonneg (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨a, _, rfl⟩ := hx
      exact abs_nonneg _)
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hsum
  refine ⟨(∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))])).re /
      Word.size S.P w.1, div_nonneg hre hsize, ?_⟩
  show (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
      (Word.size S.P w.1 : ℂ) = _
  rw [Complex.ofReal_div]
  congr 1
  exact Complex.ext (by simp) (by simp [← him])
end Formalism.FourierDecayAlt.P.Cx2
