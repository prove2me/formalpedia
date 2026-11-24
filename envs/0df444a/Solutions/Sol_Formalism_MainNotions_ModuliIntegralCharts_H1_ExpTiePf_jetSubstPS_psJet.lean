-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf.jetSubstPS_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:53.464107+00:00
-- url     : https://prove2.me/submissions/edcc9d40-6461-42da-964d-06f576bbb2b1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
private lemma mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE m ↔ (e.sum fun _ k => k) ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_image]
    refine ⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩
    · have hi : e i ≤ e.sum fun _ k => k := by
        by_cases hi0 : e i = 0
        · omega
        · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
            (Finsupp.mem_support_iff.2 hi0)
      omega
    · ext i
      simp
private lemma coeff_psTrunc_lemma_2 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ)
    (f : MvPowerSeries κ R) (e : κ →₀ ℕ) (he : (e.sum fun _ k => k) ≤ m) :
    MvPolynomial.coeff e (psTrunc m f) = MvPowerSeries.coeff e f := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single e]
  · simp [MvPolynomial.coeff_monomial]
  · intro b _ hb
    simp [MvPolynomial.coeff_monomial, hb]
  · intro h
    exact absurd ((mem_degLE_lemma m e).2 he) h
private lemma mem_orig_pow_lemma_3 {R κ : Type} [CommRing R] (m : ℕ) (p : MvPolynomial κ R)
    (hp : ∀ e : κ →₀ ℕ, (e.sum fun _ k => k) ≤ m → MvPolynomial.coeff e p = 0) :
    p ∈ orig R κ ^ (m + 1) := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun e _ => ?_
  by_cases he : (e.sum fun _ k => k) ≤ m
  · rw [hp e he, map_zero]
    exact Ideal.zero_mem _
  · have h1 : MvPolynomial.monomial e (MvPolynomial.coeff e p) ∈
        orig R κ ^ (e.sum fun _ k => k) := by
      rw [MvPolynomial.monomial_eq]
      refine Ideal.mul_mem_left _ _ ?_
      rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
    exact Ideal.pow_le_pow_right (by omega) h1
private lemma psJet_mul_lemma_4 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ)
    (f g : MvPowerSeries κ R) : psJet m (f * g) = psJet m f * psJet m g := by
  unfold psJet
  rw [← map_mul, Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_3
  intro e he
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_mul, coeff_psTrunc_lemma_2 m _ e he,
    MvPowerSeries.coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpe : p.1 + p.2 = e := by simpa using hp
  have hd : (p.1.sum fun _ k => k) + (p.2.sum fun _ k => k) = e.sum fun _ k => k := by
    rw [← hpe, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  rw [coeff_psTrunc_lemma_2 m f p.1 (by omega), coeff_psTrunc_lemma_2 m g p.2 (by omega)]
private lemma mk_eq_psJet_lemma_6 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ)
    (p : MvPolynomial κ R) (g : MvPowerSeries κ R)
    (h : ∀ e : κ →₀ ℕ, (e.sum fun _ k => k) ≤ m → MvPolynomial.coeff e p = MvPowerSeries.coeff e g) :
    (Ideal.Quotient.mk (orig R κ ^ (m + 1)) p : Jet R κ m) = psJet m g := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_3
  intro e he
  rw [MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2 m _ e he, h e he, sub_self]
private lemma psJet_add_lemma_7 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ)
    (f g : MvPowerSeries κ R) : psJet m (f + g) = psJet m f + psJet m g := by
  have h := mk_eq_psJet_lemma_6 m (psTrunc m f + psTrunc m g) (f + g) (by
    intro e he
    rw [MvPolynomial.coeff_add, coeff_psTrunc_lemma_2 m f e he, coeff_psTrunc_lemma_2 m g e he, map_add])
  rw [← h, map_add]
  all_goals rfl
private lemma psJet_eq_zero_lemma_8 {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ)
    (g : MvPowerSeries κ R)
    (h : ∀ e : κ →₀ ℕ, (e.sum fun _ k => k) ≤ m → MvPowerSeries.coeff e g = 0) :
    psJet m g = 0 := by
  rw [← mk_eq_psJet_lemma_6 m 0 g (fun e he => by rw [h e he, MvPolynomial.coeff_zero]), map_zero]
private lemma vanish_mul_lemma_9 {R τ : Type} [CommRing R] [DecidableEq τ] (a b : MvPowerSeries τ R)
    (k l : ℕ)
    (ha : ∀ e : τ →₀ ℕ, (e.sum fun _ j => j) < k → MvPowerSeries.coeff e a = 0)
    (hb : ∀ e : τ →₀ ℕ, (e.sum fun _ j => j) < l → MvPowerSeries.coeff e b = 0) :
    ∀ e : τ →₀ ℕ, (e.sum fun _ j => j) < k + l → MvPowerSeries.coeff e (a * b) = 0 := by
  intro e he
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpe : p.1 + p.2 = e := by simpa using hp
  have hd : (p.1.sum fun _ j => j) + (p.2.sum fun _ j => j) = e.sum fun _ j => j := by
    rw [← hpe, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  by_cases h1 : (p.1.sum fun _ j => j) < k
  · rw [ha p.1 h1, zero_mul]
  · rw [hb p.2 (by omega), mul_zero]
private lemma vanish_one_lemma_10 {R τ : Type} [CommRing R] (a : MvPowerSeries τ R)
    (ha : MvPowerSeries.constantCoeff a = 0) :
    ∀ e : τ →₀ ℕ, (e.sum fun _ j => j) < 1 → MvPowerSeries.coeff e a = 0 := by
  intro e he
  have he0 : e = 0 := by
    ext i
    by_contra hi
    have hi' : e i ≠ 0 := by simpa using hi
    have hle : e i ≤ e.sum fun _ j => j :=
      Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.2 hi')
    omega
  subst he0
  simpa using ha
private lemma vanish_prod_lemma_11 {R τ τ' : Type} [CommRing R] [DecidableEq τ]
    (a : τ' → MvPowerSeries τ R) (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (d : τ' →₀ ℕ) :
    ∀ e : τ →₀ ℕ, (e.sum fun _ j => j) < (d.sum fun _ j => j) →
      MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) = 0 := by
  classical
  have hpow : ∀ (s : τ') (n : ℕ) (e : τ →₀ ℕ), (e.sum fun _ j => j) < n →
      MvPowerSeries.coeff e (a s ^ n) = 0 := by
    intro s n
    induction n with
    | zero => intro e he; omega
    | succ n ih =>
      rw [pow_succ]
      exact vanish_mul_lemma_9 _ _ n 1 ih (vanish_one_lemma_10 _ (ha s))
  have key : ∀ T : Finset τ', ∀ e : τ →₀ ℕ, (e.sum fun _ j => j) < ∑ s ∈ T, d s →
      MvPowerSeries.coeff e (∏ s ∈ T, a s ^ d s) = 0 := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro e he
      simp at he
    · intro s T hs ih
      rw [Finset.prod_insert hs, Finset.sum_insert hs]
      exact vanish_mul_lemma_9 _ _ _ _ (hpow s (d s)) ih
  exact key d.support
private lemma coe_C_lemma_12 {R κ : Type} [CommRing R] (c : R) :
    ((MvPolynomial.C c : MvPolynomial κ R) : MvPowerSeries κ R) = algebraMap R _ c := by
  first
    | (rw [MvPolynomial.coe_C, Algebra.algebraMap_eq_smul_one, MvPowerSeries.smul_eq_C_mul, mul_one])
    | (ext e
       simp [Algebra.algebraMap_eq_smul_one, MvPowerSeries.coeff_C, MvPowerSeries.coeff_one])
    | (ext e
       rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_C, Algebra.algebraMap_eq_smul_one,
         MvPowerSeries.coeff_smul, MvPowerSeries.coeff_one]
       by_cases h : e = 0
       · subst h; simp
       · simp [h, Ne.symm h])
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
end Main
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries ExpTieAlg ExpTieGerm ExpTiePf
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
theorem _root_.solution {S : Type} [CommRing S] {d N : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
    (h0 : ∀ j, constantCoeff (φ j) = 0) (m : ℕ) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    (jetSubstPS (m := m) (fun p : Fin 1 × Fin d => φ p.2)) (psJet m f) =
      psJet m (subst (fun p : Fin 1 × Fin d => φ p.2) f) := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => φ p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => h0 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => h0 p.2)
      | exact ⟨fun p => by simp [h0 p.2], by simp [Filter.cofinite_eq_bot, Filter.tendsto_bot]⟩
      | exact ⟨by simp [Filter.cofinite_eq_bot, Filter.tendsto_bot], fun p => by simp [h0 p.2]⟩
  have hpoly : ∀ P : MvPolynomial (Fin 1 × Fin d) S,
      (jetSubstPS (m := m) (fun p : Fin 1 × Fin d => φ p.2))
          (Ideal.Quotient.mk (orig S (Fin 1 × Fin d) ^ (m + 1)) P) =
        psJet m (MvPowerSeries.substAlgHom hs (P : MvPowerSeries (Fin 1 × Fin d) S)) := by
    intro P
    induction P using MvPolynomial.induction_on
    next c =>
      have e1 : (MvPolynomial.C c : MvPolynomial (Fin 1 × Fin d) S) = algebraMap S _ c := by
        rw [MvPolynomial.algebraMap_eq]
      rw [coe_C_lemma_12, AlgHom.commutes, e1, Ideal.Quotient.mk_algebraMap, AlgHom.commutes,
        ← mk_eq_psJet_lemma_6 m (MvPolynomial.C c)]
      · rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
      · intro e _
        rw [← coe_C_lemma_12, MvPolynomial.coeff_coe]
    next p q hp hq =>
      rw [map_add, map_add, hp, hq, MvPolynomial.coe_add, map_add, psJet_add_lemma_7]
    next p n hp =>
      rw [map_mul, map_mul, hp, MvPolynomial.coe_mul, map_mul, psJet_mul_lemma_4]
      congr 1
      rw [MvPolynomial.coe_X, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs]
      have hc : MvPolynomial.constantCoeff (psTrunc m (φ n.2)) = 0 := by
        rw [show MvPolynomial.constantCoeff (psTrunc m (φ n.2)) =
            MvPolynomial.coeff 0 (psTrunc m (φ n.2)) from rfl, coeff_psTrunc_lemma_2 m _ 0 (by simp)]
        first
          | (rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h0 n.2)
          | simpa using h0 n.2
      have hX : (jetSubstPS (m := m) (fun p : Fin 1 × Fin d => φ p.2))
            (Ideal.Quotient.mk (orig S (Fin 1 × Fin d) ^ (m + 1)) (MvPolynomial.X n)) =
          Ideal.Quotient.mk (orig S (Fin 1 × Fin N) ^ (m + 1))
            (psTrunc m (φ n.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (φ n.2)))) := by
        first
          | (simp only [jetSubstPS, jetMap, liftJet, Ideal.Quotient.liftₐ_apply]
             erw [Ideal.Quotient.lift_mk]
             simp)
          | (simp [jetSubstPS, jetMap, liftJet]
             erw [Ideal.Quotient.lift_mk]
             simp)
          | rfl
      rw [hX, hc, map_zero, sub_zero]
      all_goals rfl
  have hvan : ∀ e : Fin 1 × Fin N →₀ ℕ, (e.sum fun _ j => j) ≤ m →
      MvPowerSeries.coeff e (MvPowerSeries.substAlgHom hs
        (f - ((psTrunc m f : MvPolynomial (Fin 1 × Fin d) S) : MvPowerSeries (Fin 1 × Fin d) S))) = 0 := by
    intro e he
    rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.coeff_subst hs]
    apply finsum_eq_zero_of_forall_eq_zero
    intro u
    by_cases hu : (u.sum fun _ j => j) ≤ m
    · rw [map_sub, MvPolynomial.coeff_coe, coeff_psTrunc_lemma_2 m f u hu, sub_self, zero_smul]
    · have hz := vanish_prod_lemma_11 (fun p : Fin 1 × Fin d => φ p.2) (fun p => h0 p.2) u e (by omega)
      first
        | exact (congrArg (fun x => MvPowerSeries.coeff u (f - ((psTrunc m f : MvPolynomial (Fin 1 × Fin d) S) :
            MvPowerSeries (Fin 1 × Fin d) S)) • x) hz).trans (smul_zero _)
        | (rw [show MvPowerSeries.coeff e (u.prod fun s n => φ s.2 ^ n) = 0 from hz, smul_zero])
        | (simp only [hz, smul_zero])
  have e3 : subst (fun p : Fin 1 × Fin d => φ p.2) f = MvPowerSeries.substAlgHom hs f := by
    rw [MvPowerSeries.coe_substAlgHom]
  have e4 : MvPowerSeries.substAlgHom hs f =
      MvPowerSeries.substAlgHom hs ((psTrunc m f : MvPolynomial (Fin 1 × Fin d) S) :
          MvPowerSeries (Fin 1 × Fin d) S) +
        MvPowerSeries.substAlgHom hs (f - ((psTrunc m f : MvPolynomial (Fin 1 × Fin d) S) :
          MvPowerSeries (Fin 1 × Fin d) S)) := by
    rw [← map_add]
    congr 1
    ring
  rw [e3, e4, psJet_add_lemma_7, psJet_eq_zero_lemma_8 m _ hvan, add_zero, ← hpoly]
  all_goals rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
