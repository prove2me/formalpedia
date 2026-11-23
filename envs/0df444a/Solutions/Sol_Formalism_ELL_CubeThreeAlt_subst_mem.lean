-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.subst_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:13.330665+00:00
-- url     : https://prove2.me/submissions/6cc5a404-4676-49dc-87a9-14117789679c

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_mem_TT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace CubeThreeAlt
open WeierstrassChordSeries
section Alg
variable {R : Type*} [CommRing R]
end Alg
section Mser
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
private theorem hasSubst_of_cc_zero_lemma {τ : Type} [Finite τ] {a : τ → MvPowerSeries σ K} (ha : ∀ i, cc (a i) = 0) :
    MvPowerSeries.HasSubst a := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
variable {w : PowerSeries K}
end Mser
end CubeThreeAlt
end Formalism.ELL
namespace Formalism.ELL
open CubeThreeAlt WeierstrassChordSeries
end Formalism.ELL
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution {τ : Type} [Finite τ] {f : MvPowerSeries τ K} (hf : f ∈ TT W τ)
    {a : τ → MvPowerSeries σ K} (ha : ∀ i, a i ∈ TT W σ) (ha0 : ∀ i, cc (a i) = 0) :
    MvPowerSeries.subst a f ∈ TT W σ := by
  classical
  have hA : MvPowerSeries.HasSubst a := hasSubst_of_cc_zero_lemma ha0
  rw [mem_TT] at hf ⊢
  intro e
  rw [MvPowerSeries.coeff_subst hA, finsum_def]
  split_ifs with hfin
  · refine sum_mem fun d _ => ?_
    rw [smul_eq_mul]
    refine mul_mem (hf d) ?_
    have hp : (d.prod fun s n => a s ^ n) ∈ TT W σ := by
      unfold Finsupp.prod
      exact prod_mem fun i _ => pow_mem (ha i) _
    exact (mem_TT.mp hp) e
  · exact zero_mem _
end Formalism.ELL.CubeThreeAlt
