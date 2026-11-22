-- Prove2me | solution 1 for Formalism.HN.HeightGram.norm_det_gramPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:59.898201+00:00
-- url     : https://prove2.me/submissions/b873bf90-d433-4efb-94a1-1bdbf1e91bc2

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
open scoped ComplexOrder
namespace Formalism.HN.HeightGram
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) :
    ‖(gramPl b X v e).det‖ = (gramPl b X v e).det.re := by
  have hpsd : (gramPl b X v e).PosSemidef := by
    let B : Matrix ι (Fin j) ℂ := Matrix.of fun i a => Formalism.HermitianLatticesTheory.fcoord b X v (e a) i
    have hB : gramPl b X v e = Bᴴ * B := by
      ext a c
      simp [B, gramPl, Formalism.HermitianLatticesTheory.majAt, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hB]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  have h0 := hpsd.det_nonneg
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 h0
  have hz : (gramPl b X v e).det = ((gramPl b X v e).det.re : ℂ) :=
    Complex.ext (by simp) (by simp [← him])
  conv_lhs => rw [hz]
  rw [Complex.norm_real, Real.norm_of_nonneg hre]
end Formalism.HN.HeightGram
