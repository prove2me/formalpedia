-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.linIndep_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:23.982947+00:00
-- url     : https://prove2.me/submissions/e61ff925-0b21-48ca-a76e-22ef5a8da1c8

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply0
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply1
import Theorems.Thm_Formalism_HN_PlaceLattice_sum_embedding_eq_zero
import Theorems.Thm_Formalism_HN_PlaceLattice_vecAt_smul_basis

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
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceLattice
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (c : K) (hc : c ≠ 0) :
    LinearIndependent ℝ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι =>
      Formalism.HermitianLatticesTheory.realize b X (integralBasis K p.1 • c • b p.2)) := by
  rw [Fintype.linearIndependent_iff]
  intro t ht p
  have hcoord : ∀ v i r, ∑ q, t q * (Formalism.HermitianLatticesTheory.realize b X (integralBasis K q.1 • c • b q.2)) (v, i, r) = 0 := by
    intro v i r
    have := congrArg (fun z => z (v, i, r)) ht
    simpa using this
  have hC : ∀ v i, ∑ q, (t q : ℂ) * Formalism.HermitianLatticesTheory.fcoord b X v (integralBasis K q.1 • c • b q.2) i = 0 := by
    intro v i
    apply Complex.ext
    · have := hcoord v i 0
      simp only [realize_apply0] at this
      simpa [Complex.re_sum] using this
    · have := hcoord v i 1
      simp only [realize_apply1] at this
      simpa [Complex.im_sum] using this
  have hV : ∀ v, ∑ q, (t q : ℂ) • Formalism.HermitianLatticesTheory.vecAt b v (integralBasis K q.1 • c • b q.2) = 0 := by
    intro v
    have h0 : Matrix.mulVec (X v)⁻¹ (∑ q, (t q : ℂ) • Formalism.HermitianLatticesTheory.vecAt b v (integralBasis K q.1 • c • b q.2)) = 0 := by
      funext i
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      simpa [Formalism.HermitianLatticesTheory.fcoord] using hC v i
    have hinv : X v * (X v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v)
    calc _ = Matrix.mulVec (X v * (X v)⁻¹) (∑ q, (t q : ℂ) • Formalism.HermitianLatticesTheory.vecAt b v (integralBasis K q.1 • c • b q.2)) := by
          rw [hinv, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hS : ∀ v : InfinitePlace K, ∑ k, ((t (k, p.2) : ℝ) : ℂ) * v.embedding (integralBasis K k) = 0 := by
    intro v
    have h1 := congrFun (hV v) p.2
    simp only [smul_smul, vecAt_smul_basis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_prod_type, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, map_mul] at h1
    have hc' : v.embedding c ≠ 0 := by simpa using hc
    have h2 : (∑ k, (t (k, p.2) : ℂ) * v.embedding (integralBasis K k)) * v.embedding c = 0 := by
      rw [Finset.sum_mul]
      simpa [mul_assoc] using h1
    exact (mul_eq_zero.mp h2).resolve_right hc'
  have := sum_embedding_eq_zero hS
  exact congrFun this p.1
end Formalism.HN.PlaceLattice
