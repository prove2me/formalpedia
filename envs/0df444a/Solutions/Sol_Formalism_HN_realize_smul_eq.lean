-- Prove2me | solution 1 for Formalism.HN.realize_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:25.90494+00:00
-- url     : https://prove2.me/submissions/30470e77-4b8c-45f8-a6fc-6abd03e3fadf

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
import Theorems.Thm_Formalism_HN_rscMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (c : InfinitePlace K → ℝ) (hX : ∀ v, IsUnit (X v).det) (hc : ∀ v, 0 < c v) (x : V) :
    Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x = rscMap c (Formalism.HermitianLatticesTheory.realize b X x) := by
  have hf : ∀ v, Formalism.HermitianLatticesTheory.fcoord b (fun w => ((c w : ℂ)) • X w) v x =
      ((c v : ℂ))⁻¹ • Formalism.HermitianLatticesTheory.fcoord b X v x := by
    intro v
    have hc0 : ((c v : ℂ)) ≠ 0 := by exact_mod_cast (hc v).ne'
    have hi : ((c v : ℂ) • X v)⁻¹ = ((c v : ℂ))⁻¹ • (X v)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.nonsing_inv_mul _ (hX v)]
    simp only [Formalism.HermitianLatticesTheory.fcoord, hi]
    first
      | exact Matrix.smul_mulVec _ _ _
      | exact Matrix.smul_mulVec_assoc _ _ _
      | (funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
  ext p
  rw [rscMap_apply]
  by_cases h : p.2.2 = 0
  · have e1 : (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x) p =
        (Formalism.HermitianLatticesTheory.fcoord b (fun v => ((c v : ℂ)) • X v) p.1 x p.2.1).re := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    have e2 : (Formalism.HermitianLatticesTheory.realize b X x) p = (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    rw [e1, e2, hf]
    simp [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  · have e1 : (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x) p =
        (Formalism.HermitianLatticesTheory.fcoord b (fun v => ((c v : ℂ)) • X v) p.1 x p.2.1).im := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    have e2 : (Formalism.HermitianLatticesTheory.realize b X x) p = (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    rw [e1, e2, hf]
    simp [← Complex.ofReal_inv, Complex.im_ofReal_mul]
end Formalism.HN
