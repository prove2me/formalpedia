-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_prod_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:58.367685+00:00
-- url     : https://prove2.me/submissions/9cb52221-f8e0-4f65-8854-5da469798860

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace KAV
open MvPowerSeries
end KAV
namespace KAV
open MvPowerSeries
end KAV
namespace KAV
open MvPowerSeries
end KAV
namespace KAV
open MvPowerSeries
private theorem coeff_rename_mapDomain_lemma {σ τ R : Type} (f : σ → τ) [Filter.TendstoCofinite f]
    [CommSemiring R] (hf : Function.Injective f) (p : MvPowerSeries σ R) (x : σ →₀ ℕ) :
    coeff (Finsupp.mapDomain f x) (rename f p) = coeff x p := by
  classical
  rw [MvPowerSeries.coeff_rename]
  rw [Finset.sum_eq_single x]
  · intro y hy hne
    exfalso
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
    exact hne (Finsupp.mapDomain_injective hf hy)
  · intro h
    exfalso
    apply h
    simp
end KAV
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
theorem _root_.solution {S : Type} [CommRing S] {n d : ℕ} (g : Fin n → MvPowerSeries (Fin 1 × Fin d) S)
    (M : Fin n × Fin d →₀ ℕ) :
    coeff M (∏ b, rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) (g b)) =
      ∏ b, coeff (colPart b M) (g b) := by
  classical
  let ι : Fin n → Fin 1 × Fin d → Fin n × Fin d := fun b p => (b, p.2)
  let Mb : Fin n → (Fin n × Fin d →₀ ℕ) := fun b => Finsupp.mapDomain (ι b) (colPart b M)
  have hMb : ∀ b q, Mb b q = if q.1 = b then M q else 0 := by
    intro b q
    obtain ⟨b', j⟩ := q
    by_cases h : b' = b
    · subst h
      rw [if_pos rfl]
      show Finsupp.mapDomain (ι b') (colPart b' M) (ι b' (0, j)) = M (b', j)
      rw [Finsupp.mapDomain_apply (colEmb_inj b')]
      simp [colPart, Finsupp.comapDomain_apply, ι]
    · rw [if_neg h]
      apply Finsupp.mapDomain_notin_range
      rintro ⟨p, hp⟩
      simp only [ι, Prod.mk.injEq] at hp
      exact h hp.1.symm
  rw [MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm Mb)]
  · refine Finset.prod_congr rfl fun b _ => ?_
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact coeff_rename_mapDomain_lemma _ (colEmb_inj b) _ _
  · intro l hl hne
    by_contra hprod
    apply hne

    have hsupp : ∀ b q, q.1 ≠ b → l b q = 0 := by
      intro b q hq
      by_contra hlq
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
      apply MvPowerSeries.coeff_rename_eq_zero
      rintro ⟨x, hx⟩
      apply hlq
      rw [← hx]
      apply Finsupp.mapDomain_notin_range
      rintro ⟨p, hp⟩
      exact hq (by rw [← hp])
    have hsum := (Finset.mem_finsuppAntidiag.1 hl).1
    refine Finsupp.ext fun b => Finsupp.ext fun q => ?_
    rw [Finsupp.coe_equivFunOnFinite_symm, hMb]
    split_ifs with hqb
    · have hq := congrArg (fun F : Fin n × Fin d →₀ ℕ => F q) hsum
      simp only [Finsupp.finset_sum_apply] at hq
      rw [← hq, Finset.sum_eq_single b]
      · intro b' _ hb'
        exact hsupp b' q (by rw [hqb]; exact Ne.symm hb')
      · intro h; exact absurd (Finset.mem_univ b) h
    · exact hsupp b q hqb
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    ext q
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.coe_equivFunOnFinite_symm, hMb]
    simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
