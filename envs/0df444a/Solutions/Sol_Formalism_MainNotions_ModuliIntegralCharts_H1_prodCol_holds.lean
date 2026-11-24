-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.prodCol_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:00.296486+00:00
-- url     : https://prove2.me/submissions/2ee49fe9-ed5a-4b9f-afdf-658c5aa3be7a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_coeff_prod_cols

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : ProdColSt := by
  classical
  intro E _ _ _ H Dw S _ n g m
  unfold mVal expVal
  rw [KAV.coeff_prod_cols, Finset.prod_mul_distrib]
  have hcol : ∀ b ℓ, colOf m b ℓ = m ⟨ℓ.1, ℓ.2, b⟩ := fun b ℓ => rfl
  congr 1
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    simp only [fun b => Finsupp.prod_fintype (colOf m b) (fun _ e => (e.factorial : S)) (fun _ => by simp), hcol]
    rw [Finset.prod_comm, ← Fintype.prod_prod_type']
    exact Fintype.prod_equiv (ltEquiv Dw n) _ _ (fun p => rfl)
  · refine Finset.prod_congr rfl fun b _ => ?_
    congr 2
    have hκ : Function.Injective (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩)) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      apply (ltEquiv Dw n).injective
      show ((⟨p.1, p.2.1⟩ : Lt1 Dw), p.2.2) = ((⟨q.1, q.2.1⟩ : Lt1 Dw), q.2.2)
      rw [(ltIdx Dw).injective h.2, h.1]
    have hι : Function.Injective (fun ℓ : Lt1 Dw => ((0 : Fin 1), ltIdx Dw ℓ)) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      exact (ltIdx Dw).injective h.2
    refine Finsupp.ext fun ⟨z, j⟩ => ?_
    set ℓ := (ltIdx Dw).symm j with hℓ
    have e1 : ((z, j) : Fin 1 × Fin (dL Dw)) = ((0 : Fin 1), ltIdx Dw ℓ) := by
      rw [hℓ, Equiv.apply_symm_apply, Subsingleton.elim z 0]
    rw [e1, Finsupp.mapDomain_apply hι]
    unfold KAV.colPart colIdx
    rw [Finsupp.comapDomain_apply]
    dsimp only
    rw [show ((b, ltIdx Dw ℓ) : Fin n × Fin (dL Dw)) =
        (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩)) (⟨ℓ.1, ℓ.2, b⟩ : LtN Dw n) from rfl,
      Finsupp.mapDomain_apply hκ]
    rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1
