-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.formal_group_linear_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:36.337462+00:00
-- url     : https://prove2.me/submissions/9ae005ad-dd13-440d-833f-b58a09b92c40

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_formal_group_linear_second
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero
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
private theorem coeff_mul_eq_zero_lemma_4 {τ : Type} (A B : MvPowerSeries τ S) (a b : ℕ)
    (hA : ∀ x : τ →₀ ℕ, x.degree < a → MvPowerSeries.coeff x A = 0)
    (hB : ∀ x : τ →₀ ℕ, x.degree < b → MvPowerSeries.coeff x B = 0) :
    ∀ x : τ →₀ ℕ, x.degree < a + b → MvPowerSeries.coeff x (A * B) = 0 := by
  classical
  intro x hx
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp : p.1 + p.2 = x := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      | exact Finset.mem_antidiagonal.1 hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = x.degree := by
    rw [← hp]
    have e : ∀ y : τ →₀ ℕ, y.degree = y.sum (fun _ k => k) := fun y => by
      first
        | rfl
        | simp [Finsupp.degree, Finsupp.sum]
    rw [e, e, e, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  by_cases h1 : p.1.degree < a
  · rw [hA _ h1, zero_mul]
  · rw [hB _ (by omega), mul_zero]
private theorem order_prod_lemma_5 {τ τ' : Type} (σ' : τ' → MvPowerSeries τ S)
    (hσ : ∀ s, MvPowerSeries.constantCoeff (σ' s) = 0) (e : τ' →₀ ℕ) (x : τ →₀ ℕ)
    (hx : x.degree < e.degree) : MvPowerSeries.coeff x (e.prod fun s n => σ' s ^ n) = 0 := by
  classical
  have hpow : ∀ s (n : ℕ) (y : τ →₀ ℕ), y.degree < n → MvPowerSeries.coeff y (σ' s ^ n) = 0 := by
    intro s n
    induction n with
    | zero => intro y hy; omega
    | succ n ih =>
      intro y hy
      rw [pow_succ]
      refine coeff_mul_eq_zero_lemma_4 _ _ n 1 ih ?_ y (by omega)
      intro z hz
      have hz0 : z = 0 := by
        first
          | exact (Finsupp.degree_eq_zero_iff z).1 (by omega)
          | exact Finsupp.degree_eq_zero_iff.1 (by omega)
      rw [hz0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hσ]
  have hprod : ∀ (t : Finset τ') (y : τ →₀ ℕ), y.degree < ∑ s ∈ t, e s →
      MvPowerSeries.coeff y (∏ s ∈ t, σ' s ^ e s) = 0 := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro y hy
      simp at hy
    · intro a t ha ih y hy
      rw [Finset.prod_insert ha]
      rw [Finset.sum_insert ha] at hy
      exact coeff_mul_eq_zero_lemma_4 _ _ (e a) (∑ s ∈ t, e s) (hpow a (e a)) ih y hy
  have he : e.degree = ∑ s ∈ e.support, e s := by
    first
      | rfl
      | simp [Finsupp.degree]
  exact hprod e.support x (he ▸ hx)
private theorem eq_single_lemma_6 {κ : Type} (e : κ →₀ ℕ) (he : e.degree = 1) : ∃ q, e = Finsupp.single q 1 := by
  classical
  have h1 : ∑ i ∈ e.support, e i = 1 := by
    first
      | exact he
      | simpa [Finsupp.degree] using he
  obtain ⟨q, hq⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have h2 := Finset.add_sum_erase e.support e hq
  rw [h1] at h2
  have hq0 : e q ≠ 0 := Finsupp.mem_support_iff.1 hq
  have h3s : ∑ i ∈ e.support.erase q, e i = 0 := by omega
  have h3 := Finset.sum_eq_zero_iff.1 h3s
  refine ⟨q, ?_⟩
  ext i
  by_cases hi : i = q
  · subst hi
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne
    exact hne (h3 i (Finset.mem_erase.2 ⟨hi, Finsupp.mem_support_iff.2 hne⟩))
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
theorem _root_.solution (G : FGLaw S d) (i j : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by
  have key : ∀ f : PS S 2 d, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)
      (ev (n := 2) ![pt S d 1, pt S d 0] f) = MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) f := by
    intro f
    unfold ev
    have hσ : ∀ s : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2) = 0 := by
      rintro ⟨a, l⟩
      obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      · simp [pt]
      · simp [pt]
    have hS : MvPowerSeries.HasSubst
        (fun s : Fin 2 × Fin d => (![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2) := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hσ
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hσ
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact ⟨fun s => by rw [hσ s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    rw [MvPowerSeries.coeff_subst hS]
    have hd1 : (Finsupp.single ((0 : Fin 2), j) 1).degree = 1 := by
      first
        | simp
        | simp [Finsupp.degree]
    rw [finsum_eq_single _ (Finsupp.single ((1 : Fin 2), j) 1)]
    · rw [Finsupp.prod_single_index (by simp)]
      simp [pt, MvPowerSeries.coeff_X]
    · intro e he
      rcases lt_trichotomy e.degree 1 with hlt | heq | hgt
      · have he0 : e = 0 := by
          first
            | exact (Finsupp.degree_eq_zero_iff e).1 (by omega)
            | exact Finsupp.degree_eq_zero_iff.1 (by omega)
        subst he0
        simp [MvPowerSeries.coeff_one]
      · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_lemma_6 e heq
        rw [Finsupp.prod_single_index (by simp)]
        obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp
        · simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero]
        · have hq : q2 ≠ j := fun h => he (by rw [h])
          simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]
      · have h0 := order_prod_lemma_5 _ hσ e (Finsupp.single ((0 : Fin 2), j) 1) (by omega)
        first
          | simp only [h0, smul_zero]
          | rw [h0, smul_zero]
          | erw [h0, smul_zero]
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)) (G.comm i)
  rw [key] at hc
  rw [← hc]
  exact formal_group_linear_second G i j
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
