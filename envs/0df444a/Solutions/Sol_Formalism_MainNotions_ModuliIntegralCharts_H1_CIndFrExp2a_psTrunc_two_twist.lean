-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.psTrunc_two_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:07.420102+00:00
-- url     : https://prove2.me/submissions/2c504688-7fef-4f25-b4ec-c227fcfc218f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_smul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_sum
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_lg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_log_low_order_one
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}
private lemma exp_split_lemma_4 {σ : Type} {B : MvPowerSeries σ S} (hB2 : Low 2 B) :
    Low 3 (PowerSeries.subst B (PowerSeries.exp S) - 1 - B) := by
  have hB0 : constantCoeff B = 0 := (low_one_iff _).1 (low_mono (by norm_num) hB2)
  have hB : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB0
  have hexp : PowerSeries.exp S = 1 + PowerSeries.X + PowerSeries.X ^ 2 *
      PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ))) := by
    ext n
    rcases n with _ | _ | n <;> simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, PowerSeries.coeff_one]
  rw [hexp, ← PowerSeries.coe_substAlgHom hB, map_add, map_add, map_mul, map_pow, map_one,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hB]
  have h4 : Low (2 + 2 + 0) (B ^ 2 * PowerSeries.subst B
      (PowerSeries.mk (fun n => algebraMap ℚ S (1 / ((n + 2).factorial : ℚ))))) := by
    rw [pow_two]
    exact low_mul (low_mul hB2 hB2) (low_zero _)
  have h3 := low_mono (by norm_num : 3 ≤ 2 + 2 + 0) h4
  convert h3 using 1
  ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
theorem _root_.solution (G : FGLaw S d) (c : Fin d → Fin d → S) :
    psTrunc 2 (CIndFrFix.expP (CIndFrFix.bilL G c)) =
      1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) := by
  have hB2 : Low 2 (CIndFrFix.bilL G c) := by
    unfold CIndFrFix.bilL
    exact low_sum _ (fun i _ => low_sum _ (fun l _ => low_smul _ (low_mul (log_low_order_one G 0 i) (log_low_order_one G 1 l))))
  have hBQ : Low 3 (CIndFrFix.bilL G c - ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l))) := by
    unfold CIndFrFix.bilL
    rw [← Finset.sum_sub_distrib]
    apply low_sum
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply low_sum
    intro l _
    rw [← smul_sub]
    apply low_smul
    have key : Low 3 ((CIndFrFix.lg G (0 : Fin 2) i - X ((0 : Fin 2), i)) * CIndFrFix.lg G (1 : Fin 2) l +
        X ((0 : Fin 2), i) * (CIndFrFix.lg G (1 : Fin 2) l - X ((1 : Fin 2), l))) :=
      low_add (low_mul (low_lg G 0 i) (log_low_order_one G 1 l))
        (low_mul ((low_one_iff _).2 (constantCoeff_X _)) (low_lg G 1 l))
    convert key using 1
    ring
  have hcoe : ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) :
        MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S) =
      1 + ∑ i, ∑ l, c i l • (X ((0 : Fin 2), i) * X ((1 : Fin 2), l)) := by
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_one, map_sum]
    simp only [map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C,
      MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]
  have hdiff : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - ((1 + ∑ i, ∑ l, MvPolynomial.C (c i l) * (MvPolynomial.X ((0 : Fin 2), i) * MvPolynomial.X ((1 : Fin 2), l)) :
        MvPolynomial (Fin 2 × Fin d) S) : MvPowerSeries (Fin 2 × Fin d) S)) := by
    rw [hcoe]
    have h1 : Low 3 (CIndFrFix.expP (CIndFrFix.bilL G c) - 1 - CIndFrFix.bilL G c) := exp_split_lemma_4 hB2
    convert low_add h1 hBQ using 1
    ring
  have hmem : ∀ e : Fin 2 × Fin d →₀ ℕ, e ∈ degLE 2 ↔ e.degree ≤ 2 := by
    intro e
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩
      · have hle : e i ≤ e.degree := by
          show e i ≤ ∑ j ∈ e.support, e j
          by_cases hi : i ∈ e.support
          · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _) hi
          · have h0 : e i = 0 := by simpa using hi
            rw [h0]
            exact Nat.zero_le _
        omega
      · ext i
        simp
  have hpt : ∀ (g : MvPowerSeries (Fin 2 × Fin d) S) (e : Fin 2 × Fin d →₀ ℕ),
      MvPolynomial.coeff e (psTrunc 2 g) = if e.degree ≤ 2 then coeff e g else 0 := by
    intro g e
    rw [psTrunc, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases h : e.degree ≤ 2
    · rw [if_pos ((hmem e).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hmem e).1 h')), if_neg h]
  have hXX : ∀ (a b : Fin 2 × Fin d) (e : Fin 2 × Fin d →₀ ℕ), 2 < e.degree →
      coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0 := by
    intro a b e he
    rw [MvPowerSeries.X, MvPowerSeries.X, monomial_mul_monomial, coeff_monomial, if_neg]
    rintro rfl
    have hdeg : (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).degree = 2 := by
      show (Finsupp.single a 1 + Finsupp.single b 1 : Fin 2 × Fin d →₀ ℕ).sum (fun _ k => k) = 2
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_single_index rfl]
    omega
  ext e
  rw [hpt]
  by_cases hd : e.degree ≤ 2
  · rw [if_pos hd, ← MvPolynomial.coeff_coe]
    have h := hdiff e (by omega)
    rwa [map_sub, sub_eq_zero] at h
  · rw [if_neg hd, ← MvPolynomial.coeff_coe, hcoe, map_add, map_sum]
    have h2 : 2 < e.degree := by omega
    have hz : ∀ a b : Fin 2 × Fin d, coeff e (X a * X b : MvPowerSeries (Fin 2 × Fin d) S) = 0 :=
      fun a b => hXX a b e h2
    simp only [map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, add_zero]
    rw [coeff_one, if_neg]
    rintro rfl
    simp at hd
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
