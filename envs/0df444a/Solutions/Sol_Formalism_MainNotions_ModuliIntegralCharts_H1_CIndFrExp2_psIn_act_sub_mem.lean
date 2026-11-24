-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.psIn_act_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:53.598789+00:00
-- url     : https://prove2.me/submissions/ac5963dd-1deb-4788-929f-5aaa314a07a7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_psTrunc_act_sub_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
private theorem mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} {x : κ →₀ ℕ}
    (hx : x.degree ≤ n) : x ∈ degLE n := by
  have hle : ∀ i, x i ≤ n := by
    intro i
    by_cases hi : x i = 0
    · rw [hi]
      exact Nat.zero_le n
    · exact le_trans (Finset.single_le_sum (f := fun j => x j) (fun j _ => Nat.zero_le (x j))
        (Finsupp.mem_support_iff.2 hi)) hx
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun i => ⟨x i, Nat.lt_succ_of_le (hle i)⟩, Finset.mem_univ _, ?_⟩, hx⟩
  ext i
  simp
private theorem coeff_psTrunc_lemma_2 {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S) (n : ℕ)
    (x : κ →₀ ℕ) : coeff x (psTrunc n f) = if x.degree ≤ n then MvPowerSeries.coeff x f else 0 := by
  unfold psTrunc
  rw [coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
  by_cases h : x.degree ≤ n
  · rw [if_pos (mem_degLE_lemma h), if_pos h]
  · have h' : x ∉ degLE n := by
      intro h'
      unfold degLE at h'
      exact h (Finset.mem_filter.1 h').2
    rw [if_neg h', if_neg h]
section Poly
variable [Algebra ℚ S]
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
end Poly
section Act
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
end Act
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
theorem _root_.solution (φ : Fin d → PS S 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {m : ℕ}
    (hm : 1 ≤ m) (k : Fin 2) (i : Fin d) :
    psIn d m ![k] (φ i) - C (constantCoeff (psIn d m ![k] (φ i))) - PairEvaluation.lin (dLin φ) k i ∈
      Io S (Fin 2 × Fin d) ^ 2 := by
  have hmap : ∀ q ∈ Io S (Fin 1 × Fin d) ^ 2,
      rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) q ∈ Io S (Fin 2 × Fin d) ^ 2 := by
    intro q hq
    have hle : Ideal.map (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) :
        MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) (Io S (Fin 1 × Fin d)) ≤
          Io S (Fin 2 × Fin d) := by
      rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, rename_X]
      exact Ideal.subset_span ⟨_, rfl⟩
    have h2 := Ideal.mem_map_of_mem (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) :
        MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) hq
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hle 2 h2
  have h3 := hmap _ (psTrunc_act_sub_mem φ hφ hm i)
  have hc0 : constantCoeff (psIn d m ![k] (φ i)) = 0 := by
    rw [psIn, constantCoeff_rename]
    have h0 : constantCoeff (psTrunc m (φ i)) = coeff 0 (psTrunc m (φ i)) := by
      first
        | rfl
        | simp [constantCoeff_eq]
    rw [h0, coeff_psTrunc_lemma_2]
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
  convert h3 using 1
  rw [hc0, map_zero, sub_zero, map_sub]
  congr 1
  all_goals first
    | rfl
    | simp [PairEvaluation.lin, map_sum, rename_X, rename_C]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
