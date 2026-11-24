-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.prj_realize_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:18.621051+00:00
-- url     : https://prove2.me/submissions/b5f8ac7e-0a4f-48b7-984a-fef969ed7a01

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_realize_apply
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_apply
import Theorems.Thm_Formalism_HN_PlaceDecomposition_fcoord_osmul
import Theorems.Thm_Formalism_HN_PlaceDecomposition_re_comb
import Theorems.Thm_Formalism_HN_PlaceDecomposition_im_comb

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
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
variable [DecidableEq (InfinitePlace K)]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ)
    (hr : ∀ u : InfinitePlace K,
      ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = if u = v then 1 else 0)
    (x : V) :
    prj v (Formalism.HermitianLatticesTheory.realize b X x) =
      ∑ k, r k • Formalism.HermitianLatticesTheory.realize b X ((RingOfIntegers.basis K k : 𝓞 K) • x) := by
  ext p
  rw [prj_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    realize_apply, fcoord_osmul]
  by_cases h2 : p.2.2 = 0
  · simp only [h2, ↓reduceIte]
    rw [re_comb, hr p.1]
    by_cases h1 : p.1 = v <;> simp [h1]
  · simp only [h2, ↓reduceIte]
    rw [im_comb, hr p.1]
    by_cases h1 : p.1 = v <;> simp [h1]
end Formalism.HN.PlaceDecomposition
