-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.nval_factProd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:14.686648+00:00
-- url     : https://prove2.me/submissions/e6eab614-c509-42e5-be51-9055c0392faf

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_resCharOf_prime
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_nval_natCast
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_legendre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (ho : OverLa la V ι e) {σ : Type} (α : σ →₀ ℕ) :
    nval V e (((α.prod fun _ t => t.factorial : ℕ) : K')) ≤
      (((ramOverZ la : ℝ) * (α.degree : ℝ) / ((resCharOf la : ℝ) - 1) : ℝ) : EReal) := by
  have hp := resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hp⟩
  have hne : (α.prod fun _ t => t.factorial) ≠ 0 := by
    simp only [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _
  rw [crv_nval_natCast la ho hne, EReal.coe_le_coe_iff]
  have hleg := crv_legendre (resCharOf la) α
  have hp1 : (1 : ℝ) < resCharOf la := by exact_mod_cast hp.one_lt
  have hsub : ((resCharOf la - 1 : ℕ) : ℝ) = (resCharOf la : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hleg' : ((resCharOf la : ℝ) - 1) *
      (padicValNat (resCharOf la) (α.prod fun _ t => t.factorial) : ℝ) ≤ α.degree := by
    rw [← hsub]
    exact_mod_cast hleg
  rw [le_div_iff₀ (by linarith)]
  push_cast
  have hr : (0 : ℝ) ≤ ramOverZ la := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hleg' hr]
end Formalism.L2.Pj.Crude
