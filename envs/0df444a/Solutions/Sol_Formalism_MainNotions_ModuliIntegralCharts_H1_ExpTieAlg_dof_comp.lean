-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.dof_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:19.876799+00:00
-- url     : https://prove2.me/submissions/ab3fb661-a133-42e1-a855-4c33d7e0a997

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_pderiv_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst0
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sum__259da4521e82
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_dof_addF
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_key
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
variable {N d : ℕ}
private theorem subst_C_lemma {σ τ : Type} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (c : S) :
    subst a (C c : MvPowerSeries σ S) = C c := by
  have hc : (C c : MvPowerSeries σ S) = c • (1 : MvPowerSeries σ S) := by
    rw [smul_eq_C_mul, mul_one]
  rw [hc, ← coe_substAlgHom ha, map_smul, map_one, smul_eq_C_mul, mul_one]
section Exp
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
end Exp
section Comp
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
  (h0 : ∀ j, constantCoeff (φ j) = 0) (w : Fin N → Fin d → S)
  (hlin : ∀ q j, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = w q j)
  (hhom : ∀ j, subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (F j) =
    subst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))
include h0 hlin hhom
end Comp
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj ExpTieAlg NumberField
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
variable {N d : ℕ}
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
  (h0 : ∀ j, constantCoeff (φ j) = 0) (w : Fin N → Fin d → S)
  (hlin : ∀ q j, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = w q j)
  (hhom : ∀ j, subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (F j) =
    subst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))
include h0 hlin hhom
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution (q : Fin N) (g : PS S 1 d) :
    Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) (Pi.single q 1) (subst (famL φ) g) =
      subst (famL φ) (Dof F (w q) g) := by
  classical
  have hL : HasSubst (famL φ) := hasSubst0 (fun p => h0 p.2)
  have hk : ∀ k : Fin d, pderiv S ((0 : Fin 1), q) (famL φ ((0 : Fin 1), k)) =
      ∑ i, subst (famL φ) (ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), i) (F k))) * C (w q i) :=
    fun k => key F φ h0 w hlin hhom q k
  rw [dof_addF, Finset.sum_eq_single q (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp only [Pi.single_eq_same, map_one, one_mul]
  rw [pderiv_subst hL, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [hk]
  rw [Dof, subst_sum' hL]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← coe_substAlgHom hL, map_mul, map_sum]
  simp only [map_mul, coe_substAlgHom, subst_C_lemma hL]
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
