-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.coeff_single_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:27.182784+00:00
-- url     : https://prove2.me/submissions/01bce417-5db4-4615-acd3-b85a22c6046a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_Formalism_FG_SolveVAux_degree_eq_one
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {R : Type} [CommRing R]
open Formalism.FG.SolveVAux
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
theorem _root_.solution {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (a : σ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hlow : ∀ s, Low 1 (a s) := fun s => (low_one_iff _).2 (ha s)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s : σ => Finsupp.single s 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (h := fun (s : σ) (e : ℕ) => a s ^ e) (pow_zero _), pow_one, smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single t 1) (e.prod fun s n => a s ^ n) = 0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
