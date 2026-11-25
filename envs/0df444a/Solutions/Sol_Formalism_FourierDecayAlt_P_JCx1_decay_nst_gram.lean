-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.nst_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:41:34.707803+00:00
-- url     : https://prove2.me/submissions/84d8e03b-4f7b-4751-bcaa-06344824a3ad

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_psd_compress
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_psd_two_cs
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_join_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1
open NumberField
end Formalism.FourierDecayAlt.P.JCx1
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
section cutf
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.JCx1
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.JCx1
namespace Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
end cutf
section lemE
open Formalism.FourierDecayAlt Filter Topology
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end lemE
section decayPart
open Finset Formalism.FourierDecayAlt
noncomputable section decayNC
namespace Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)
private theorem psdOn_hadamard_mul_of_psdOn {α : Type} (F : Finset α) (A B : α → α → ℂ) (hA : PSDOn F A)
    (hB : PSDOn F B) : PSDOn F (fun x y => A x y * B x y) := by
  have hA' : Matrix.PosSemidef (Matrix.of fun x y : F => A x y) := hA
  have hB' : Matrix.PosSemidef (Matrix.of fun x y : F => B x y) := hB
  show Matrix.PosSemidef (Matrix.of fun x y : F => A x y * B x y)
  first
  | exact hA'.hadamard hB'
  | exact Matrix.PosSemidef.hadamard hA' hB'
  | obtain ⟨C, hC⟩ : ∃ C : Matrix F F ℂ, (Matrix.of fun x y : F => A x y) = C.conjTranspose * C := by
      first
      | exact ⟨hA'.sqrt, by rw [hA'.posSemidef_sqrt.1.eq, hA'.sqrt_mul_self]⟩
      | exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.1 hA'
      | exact Matrix.posSemidef_iff_exists_eq_conjTranspose_mul_self.1 hA'
    have hsum : (Matrix.of fun x y : F => A x y * B x y) =
        ∑ k : F, (Matrix.diagonal fun i => C k i).conjTranspose * (Matrix.of fun x y : F => B x y) *
          Matrix.diagonal fun i => C k i := by
      ext i j
      have hij : A i j = ∑ k : F, star (C k i) * C k j := by
        have := congrFun (congrFun hC i) j
        simpa [Matrix.mul_apply] using this
      rw [Matrix.sum_apply]
      simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply,
        Pi.star_apply]
      rw [hij, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero ?_
    intro k _
    exact hB'.conjTranspose_mul_mul_same _
end Formalism.FourierDecayAlt.P.JCx1.decay
end decayNC
end decayPart
section needsPart
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
namespace Formalism.FourierDecayAlt.P.JCx1.needs
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
section meas
open scoped Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E} {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
end meas
end
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end needsPart
end

set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : W)
    (Y : Finset (Pt E)) (T : Finset E) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn (pts Y s T) κ) (t t' : E)
    (ht : t ∈ T) (ht' : t' ∈ T) :
    PairingProductCorollary.PairingGramInequality (D.Nst ε i s w Y (blk κ s t t') t t') (D.Nst ε i s w Y (blk κ s t t) t t).re
      (D.Nst ε i s w Y (blk κ s t' t') t' t').re := by
  have hwt : 0 < D.wt w := hW w
  have hH : PSDOn (pts Y s T) (fun a b => κ a b * D.gram ε i w a b) :=
    psdOn_hadamard_mul_of_psdOn _ _ _ hκ (hG ε hε i w _)
  have hg : ∀ j : Fin 2, ∀ h ∈ Y, join h s (![t, t'] j) ∈ pts Y s T := by
    intro j h hh
    fin_cases j
    · exact join_mem Y s T t ht h hh
    · exact join_mem Y s T t' ht' h hh
  have hM := psd_two_cs _ (psd_compress (pts Y s T) _ hH (fun _ : Fin 2 => Y)
    (fun j h => join h s (![t, t'] j)) hg)
  have key : ∀ a b c : ℂ, ‖a‖ ^ 2 ≤ b.re * c.re →
      PairingProductCorollary.PairingGramInequality (a / (D.wt w : ℂ)) (b / (D.wt w : ℂ)).re (c / (D.wt w : ℂ)).re := by
    intro a b c h
    unfold PairingProductCorollary.PairingGramInequality
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hwt.le, Complex.div_ofReal_re,
      Complex.div_ofReal_re, div_pow, div_mul_div_comm, ← sq]
    gcongr
  exact key _ _ _ hM.1
end Formalism.FourierDecayAlt.P.JCx1.decay
