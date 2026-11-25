-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndRelPf.dim_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:56.917096+00:00
-- url     : https://prove2.me/submissions/70e0ea56-cb95-411d-91f1-43fe374e367c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndRelPf

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
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndRelPf
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndRelPf
theorem _root_.solution {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Fintype ι] {d : ℕ}
    (u : ι → Fin d → S) (h : ∀ v : Fin d → S, ∃! a : ι → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    d = Fintype.card ι := by
  let f : (ι → S) →ₗ[S] (Fin d → S) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * u ℓ j
      map_add' := by
        intro a b
        funext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext j
        simp [Finset.mul_sum, mul_assoc] }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨c, -, hc⟩ := h (f a)
      have ha : a = c := hc a (fun j => rfl)
      have hb : b = c := hc b (fun j => congrFun hab.symm j)
      rw [ha, hb]
    · intro v
      obtain ⟨a, ha, -⟩ := h v
      exact ⟨a, funext ha⟩
  have hr := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun] at hr
  exact hr.symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndRelPf
