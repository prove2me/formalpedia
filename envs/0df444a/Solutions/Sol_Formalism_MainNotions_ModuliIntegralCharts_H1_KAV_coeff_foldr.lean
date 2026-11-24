-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:54.374716+00:00
-- url     : https://prove2.me/submissions/91018a94-d957-4dd6-91ab-1aba892d05d5

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_coeff_iterate_pderiv

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
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
theorem _root_.solution {σ κ R : Type} [CommRing R] (φ : κ → σ) (m : κ → ℕ) (F : MvPowerSeries σ R) :
    ∀ (L : List κ), L.Nodup → (∀ p ∈ L, ∀ q ∈ L, φ p = φ q → p = q) → ∀ N : σ →₀ ℕ, (∀ p ∈ L, N (φ p) = 0) →
      coeff N (L.foldr (fun p g => (pderiv R (φ p))^[m p] g) F) =
        (L.map fun p => ((m p).factorial : R)).prod * coeff (N + (L.map fun p => m p • Finsupp.single (φ p) 1).sum) F
  | [], _, _, N, _ => by simp
  | p :: L, hnd, hinj, N, hN => by
    rw [List.foldr_cons, coeff_iterate_pderiv, hN p (List.mem_cons_self ..), solution φ m F L
      (List.nodup_cons.1 hnd).2 (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]
    · rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
      have hf : (∏ t ∈ Finset.range (m p), ((0 + t + 1 : ℕ) : R)) = ((m p).factorial : R) := by
        rw [← Finset.prod_range_add_one_eq_factorial]
        push_cast
        refine Finset.prod_congr rfl fun t _ => ?_
        ring
      rw [hf, add_assoc]
      ring
    · intro q hq
      have hpq : φ q ≠ φ p := fun h => (List.nodup_cons.1 hnd).1
        (hinj q (List.mem_cons_of_mem _ hq) p (List.mem_cons_self ..) h ▸ hq)
      simp [hN q (List.mem_cons_of_mem _ hq), hpq.symm]
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
