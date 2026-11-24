-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:36.861667+00:00
-- url     : https://prove2.me/submissions/b06ad0c5-102d-4adc-8554-845368e5c520

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_pderiv_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst0
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sum__259da4521e82
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst_cpy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst_sz
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sz_cpy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_pderiv_cpy

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
variable {N d : ℕ}
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution (h0 : ∀ j, constantCoeff (φ j) = 0) (w : Fin N → Fin d → S)
    (hlin : ∀ q j, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = w q j)
    (hhom : ∀ j, subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (F j) =
      subst (fun r : Fin 1 × Fin N =>
        (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))
    (q : Fin N) (j : Fin d) :
    pderiv S ((0 : Fin 1), q) (φ j) =
      ∑ i, subst (famL φ) (ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), i) (F j))) * C (w q i) := by
  have hAs : HasSubst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) := hasSubst0 fun p =>
    constantCoeff_subst_eq_zero (hasSubst_cpy _) (fun r => by simp [cpy]) (h0 p.2)
  have hBs : HasSubst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) :=
    hasSubst0 fun r => by simp
  have hE := congrArg (fun G => subst (sz (S := S) (N := N)) (pderiv S ((1 : Fin 2), q) G)) (hhom j)

  have eR : subst (sz (S := S) (N := N)) (pderiv S ((1 : Fin 2), q) (subst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))) =
      pderiv S ((0 : Fin 1), q) (φ j) := by
    rw [pderiv_subst hBs]
    have hdB : ∀ r : Fin 1 × Fin N, pderiv S ((1 : Fin 2), q)
        (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S) =
        if r = ((0 : Fin 1), q) then 1 else 0 := by
      rintro ⟨i, r⟩
      fin_cases i
      rw [map_add, pderiv_X_of_ne (by simp [Prod.ext_iff]), zero_add]
      by_cases h : r = q
      · subst h; simp
      · rw [pderiv_X_of_ne (by simp [Prod.ext_iff, h]), if_neg (by simp [Prod.ext_iff, h])]
    simp only [hdB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [subst_comp_subst_apply hBs hasSubst_sz]
    have : (fun s : Fin 1 × Fin N => subst (sz (S := S) (N := N))
        ((X ((0 : Fin 2), s.2) + X ((1 : Fin 2), s.2) : MvPowerSeries (Fin 2 × Fin N) S))) = (X : Fin 1 × Fin N → MvPowerSeries (Fin 1 × Fin N) S) := by
      funext s; rcases s with ⟨i, r⟩; fin_cases i
      simp [sz, subst_add hasSubst_sz, subst_X hasSubst_sz]
    rw [this, subst_self]; rfl

  have hfam : ∀ g : PS S 2 d, subst (sz (S := S) (N := N)) (subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) g) =
      subst (famL φ) (ev (n := 1) ![pt S d 0, 0] g) := by
    intro g
    have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2) :=
      hasSubst0 fun p => by rcases p with ⟨b, i⟩; fin_cases b <;> simp [pt]
    unfold ev
    rw [subst_comp_subst_apply hAs hasSubst_sz, subst_comp_subst_apply h2 (hasSubst0 fun p => h0 p.2)]
    congr 1
    funext p
    rcases p with ⟨b, i⟩
    fin_cases b
    · simp [subst_sz_cpy, pt, subst_X (hasSubst0 fun p : Fin 1 × Fin d => h0 p.2)]
    · simp [subst_sz_cpy, h0]
      rw [← coe_substAlgHom (hasSubst0 fun p : Fin 1 × Fin d => h0 p.2), map_zero]
  rw [← eR, ← hE, pderiv_subst hAs, subst_sum' hasSubst_sz, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0s : subst (sz (S := S) (N := N)) (0 : MvPowerSeries (Fin 2 × Fin N) S) = 0 := by
    rw [← coe_substAlgHom hasSubst_sz, map_zero]
  simp only [pderiv_cpy, Fin.isValue, zero_ne_one, if_false, if_true, mul_zero, h0s, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [subst_mul hasSubst_sz, hfam, subst_sz_cpy, if_neg (by decide)]
  congr 2
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp [hlin]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
