-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.harm_kill_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:02.491203+00:00
-- url     : https://prove2.me/submissions/9bad517a-6b42-4edb-942b-8ec386170c63

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_sb_cc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_rename_col
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_subst_quadCol
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_sum_subst_quadCol
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_cc_quadCol
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvC_colIdx_degree
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvA_coeff_eq_of_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvA_psJet_prod_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_HarmInvA_psJet_subst_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_killAddValCol_of
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_prodCol_holds
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_psiCover_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_kernel_additive

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
section Col
variable {S : Type} [CommRing S] {n d : ℕ}
end Col
private theorem hasSubst_lemma {S σ τ : Type} [CommRing S] [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
private theorem prod_exp_lemma_2 {S σ ι : Type} [CommRing S] [Algebra ℚ S] (s : Finset ι)
    (x : ι → MvPowerSeries σ S) (hx : ∀ i, MvPowerSeries.constantCoeff (x i) = 0) :
    ∏ i ∈ s, PowerSeries.subst (x i) (PowerSeries.exp S) = PowerSeries.subst (∑ i ∈ s, x i) (PowerSeries.exp S) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (hx a)
      (by rw [map_sum]; exact Finset.sum_eq_zero (fun i _ => hx i))]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n D : ℕ)
    (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S)
    (hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1)
    (hj : ∀ b, psJet D (g' b) =
      psJet D (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)))
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (hD : ∀ m ∈ P.support, m.degree ≤ D) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by
  classical

  have hccQ : ∀ (r : S) {m' : ℕ}, MvPowerSeries.constantCoeff (r • TB.quadCol (n := m') β) = 0 := by
    intro r m'
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cc_quadCol, mul_zero]
  have hsb : ∀ b : Fin n, MvPowerSeries.HasSubst (sb (S := S) (n := n) (d := dL Dw) b) :=
    fun b => hasSubst_lemma (sb_cc b)
  have hR : ∀ (b : Fin n) (F : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
      MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) F =
        MvPowerSeries.subst (sb b) F := fun b F => rename_col b F

  have hE4 : ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
        (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)) =
      PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
        ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b) := by
    simp only [hR]
    simp only [MvPowerSeries.subst_mul (hsb _), Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    have hc : ∀ b : Fin n, MvPowerSeries.subst (sb (S := S) (n := n) (d := dL Dw) b)
        (PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)) =
        PowerSeries.subst (MvPowerSeries.subst (sb (S := S) (n := n) (d := dL Dw) b) ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β))
          (PowerSeries.exp S) := by
      intro b
      have hq : MvPowerSeries.HasSubst (fun _ : Unit => ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β)) :=
        hasSubst_lemma (fun _ => hccQ _)
      exact MvPowerSeries.subst_comp_subst_apply hq (hsb b) (PowerSeries.exp S)
    simp only [hc]
    rw [prod_exp_lemma_2 Finset.univ _ (fun b => ?_), sum_subst_quadCol]
    rw [subst_quadCol]
    simp [MvPowerSeries.smul_eq_C_mul]

  have hE2 : psJet D (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g' b)) =
      psJet D (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
        (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S))) := by
    refine Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_prod_congr D (fun b => ?_)
    rw [hR, hR]
    exact Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_subst_congr D (sb b) (sb_cc b) (hj b)

  have hK := Formalism.MainNotions.ModuliIntegralCharts.H1.killAddValCol_of ReciprocityTheory.ChartRestriction.G.TB.kernel_additive E H Dw l c S k n
    (PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
      ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b))
    β (Formalism.MainNotions.ModuliIntegralCharts.H1.psiCover_holds H) hβ a P hP
  have hcan : PowerSeries.subst (-((k : S)) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
      PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) = 1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (hccQ _) (hccQ _), neg_smul, neg_add_cancel,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.expS, ← mul_assoc, hcan, one_mul] at hK
  calc ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b)
      = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
            ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [← Formalism.MainNotions.ModuliIntegralCharts.H1.prodCol_holds E H Dw S n g' m, ← hE4]
        congr 1
        unfold Formalism.MainNotions.ModuliIntegralCharts.H1.mVal
        rw [Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.coeff_eq_of_psJet hE2 (by rw [colIdx_degree]; exact hD m hm)]
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m :=
        hK.symm
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) :=
        Finset.sum_congr rfl (fun m _ => by rw [Formalism.MainNotions.ModuliIntegralCharts.H1.prodCol_holds E H Dw S n g m])
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
