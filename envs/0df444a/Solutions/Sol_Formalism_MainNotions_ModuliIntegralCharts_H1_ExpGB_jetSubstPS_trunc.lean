-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.jetSubstPS_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:19.788793+00:00
-- url     : https://prove2.me/submissions/f0d6cb9b-a909-4054-873b-6912b552a7df

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
section Jet
variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
private theorem mem_degLE_lemma (n : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE n ↔ (e.sum fun _ k => k) ≤ n := by
  constructor
  · intro h
    simp only [degLE, Finset.mem_filter] at h
    exact h.2
  · intro h
    have hb : ∀ i, e i < n + 1 := by
      intro i
      rcases Nat.eq_zero_or_pos (e i) with h0 | hpos
      · omega
      · have hi : i ∈ e.support := Finsupp.mem_support_iff.2 (by omega)
        have h1 := Finset.single_le_sum (f := (⇑e)) (fun _ _ => Nat.zero_le _) hi
        have h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j := rfl
        omega
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨fun i => ⟨e i, hb i⟩, ?_⟩, h⟩
    ext i
    simp
private theorem monomial_mem_orig_pow_lemma (n : ℕ) (e : κ →₀ ℕ) (c : S)
    (h : n ≤ e.sum fun _ k => k) : MvPolynomial.monomial e c ∈ orig S κ ^ n := by
  have hX : ∀ i, (MvPolynomial.X i : MvPolynomial κ S) ∈ orig S κ :=
    fun i => Ideal.subset_span ⟨i, rfl⟩
  have h1 : (e.prod fun i k => (MvPolynomial.X i : MvPolynomial κ S) ^ k) ∈
      orig S κ ^ (e.sum fun _ k => k) := by
    have h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j := rfl
    rw [h2, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) _
  rw [MvPolynomial.monomial_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right h h1)
private theorem psTrunc_succ_sub_lemma (n : ℕ) (f : MvPowerSeries κ S) :
    psTrunc (n + 1) f - psTrunc n f ∈ orig S κ ^ (n + 1) := by
  have hsub : (degLE n : Finset (κ →₀ ℕ)) = (degLE (n + 1)).filter (fun e => (e.sum fun _ k => k) ≤ n) := by
    ext e
    simp only [Finset.mem_filter, mem_degLE_lemma]
    exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
  unfold psTrunc
  rw [hsub, ← Finset.sum_filter_add_sum_filter_not (degLE (n + 1))
    (fun e => (e.sum fun _ k => k) ≤ n), add_sub_cancel_left]
  refine Ideal.sum_mem _ fun e he => ?_
  rw [Finset.mem_filter, mem_degLE_lemma] at he
  have he2 := he.2
  exact monomial_mem_orig_pow_lemma _ _ _ (by omega)
private theorem cc_psTrunc_lemma (n : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.constantCoeff (psTrunc n f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq', if_pos ((mem_degLE_lemma n 0).2 (by simp))]
  rfl
private theorem jetTrunc_mk_lemma (n : ℕ) (P : MvPolynomial κ S) :
    (jetTrunc : Jet S κ (n + 1) →ₐ[S] Jet S κ n) (Ideal.Quotient.mk (orig S κ ^ (n + 1 + 1)) P) =
      Ideal.Quotient.mk (orig S κ ^ (n + 1)) P := rfl
private theorem jetSubstPS_mk_lemma (n : ℕ) (g : κ → MvPowerSeries κ' S) (P : MvPolynomial κ S) :
    (jetSubstPS (m := n) g) (Ideal.Quotient.mk (orig S κ ^ (n + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (n + 1))
        (MvPolynomial.aeval (fun i => psTrunc n (g i) -
          MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc n (g i)))) P) := rfl
end Jet
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
theorem _root_.solution (m : ℕ) (g : κ → MvPowerSeries κ' S) :
    (jetTrunc : Jet S κ' (m + 1) →ₐ[S] Jet S κ' m).comp (jetSubstPS (m := m + 1) g) =
      (jetSubstPS (m := m) g).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  simp only [jetTrunc_mk_lemma, jetSubstPS_mk_lemma, MvPolynomial.aeval_X]
  rw [Ideal.Quotient.eq, cc_psTrunc_lemma, cc_psTrunc_lemma, sub_sub_sub_cancel_right]
  exact psTrunc_succ_sub_lemma m (g i)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
