-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.tie_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:32.357021+00:00
-- url     : https://prove2.me/submissions/920153fc-8f81-492a-af47-df9ba3421e41

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_const_subst0
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_dof_addF
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_dpoly_comp
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
private theorem iter_coeff_lemma {S : Type} [CommRing S] {σ : Type} [DecidableEq σ] (i : σ)
    (h : MvPowerSeries σ S) (k : ℕ) : ∀ n : σ →₀ ℕ, ((n i).factorial : S) * coeff n ((pderiv S i)^[k] h) =
      ((n i + k).factorial : S) * coeff (n + Finsupp.single i k) h := by
  induction k with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    have ih' := ih (n + Finsupp.single i 1)
    have e1 : (n + Finsupp.single i 1 : σ →₀ ℕ) i = n i + 1 := by simp
    have e2 : n + Finsupp.single i 1 + Finsupp.single i k = n + Finsupp.single i (k + 1) := by
      rw [add_assoc, ← Finsupp.single_add, add_comm 1 k]
    have e3 : n i + 1 + k = n i + (k + 1) := by omega
    rw [e1, e2, e3] at ih'
    rw [Function.iterate_succ_apply', coeff_pderiv, ← ih', Nat.factorial_succ]
    push_cast
    ring
private theorem foldr_coeff_lemma_2 {S : Type} [CommRing S] {σ κ : Type} [DecidableEq σ] (v : κ → σ)
    (hv : Function.Injective v) (α : κ → ℕ) (h : MvPowerSeries σ S) : ∀ L : List κ, L.Nodup →
      ∀ n : σ →₀ ℕ, (∀ l ∈ L, n (v l) = 0) →
        coeff n (L.foldr (fun l g => (pderiv S (v l))^[α l] g) h) =
          (L.map fun l => ((α l).factorial : S)).prod *
            coeff (n + (L.map fun l => Finsupp.single (v l) (α l)).sum) h := by
  intro L
  induction L with
  | nil => intro _ n _; simp
  | cons l t ih =>
    intro hnd n hn
    rw [List.nodup_cons] at hnd
    have hnl : n (v l) = 0 := hn l (by simp)
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, List.sum_cons]
    have key1 := iter_coeff_lemma (v l) (t.foldr (fun l g => (pderiv S (v l))^[α l] g) h) (α l) n
    rw [hnl, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add] at key1
    rw [key1, ih hnd.2 (n + Finsupp.single (v l) (α l)) ?_]
    · rw [add_assoc]
      ring
    · intro l' hl'
      have hne : v l ≠ v l' := fun e => hnd.1 (by rw [hv e]; exact hl')
      simp [hn l' (by simp [hl']), Finsupp.single_apply, hne]
private theorem const_dpoly_lemma_3 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {S : Type} [CommRing S] (α : Lt1 Dw →₀ ℕ) (G : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    constantCoeff (DpolyOf (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S (dL Dw)) (fun l => Pi.single (ltIdx Dw l) 1)
      (MvPolynomial.monomial α 1) G) = expVal G α := by
  classical
  have hD : ∀ q : Fin (dL Dw), (Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S (dL Dw)) (Pi.single q 1) :
      PS S 1 (dL Dw) → PS S 1 (dL Dw)) = pderiv S ((0 : Fin 1), q) := by
    intro q
    funext f
    rw [dof_addF, Finset.sum_eq_single q (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  by_cases h1 : (1 : S) = 0
  · haveI : Subsingleton S := subsingleton_of_zero_eq_one h1.symm
    exact Subsingleton.elim _ _
  unfold DpolyOf DmonOf
  rw [MvPolynomial.support_monomial, if_neg h1, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
    map_one, one_mul]
  simp only [hD]
  rw [← coeff_zero_eq_constantCoeff_apply, foldr_coeff_lemma_2 (fun l => ((0 : Fin 1), ltIdx Dw l)) ?_ α G _
    (Finset.nodup_toList _) 0 (fun _ _ => by simp)]
  · simp only [Finset.prod_toList, Finset.sum_toList, zero_add]
    rw [expVal, Finsupp.mapDomain, Finsupp.prod_fintype, Finsupp.sum_fintype]
    all_goals simp
  · intro a b hab
    simpa using hab
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj ExpTieAlg NumberField
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type} [CommRing S]
    {d : ℕ} (F : Fin d → PS S 2 d) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf F uvec φ) (α : Lt1 Dw →₀ ℕ) (g : PS S 1 d) :
    constantCoeff (DpolyOf F uvec (MvPolynomial.monomial α 1) g) = expVal (compL φ g) α := by
  classical
  have h0 := hφ.const
  have hlin : ∀ (q : Fin (dL Dw)) (j : Fin d), coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) =
      uvec ((ltIdx Dw).symm q) j := by
    intro q j
    simpa using hφ.lin ((ltIdx Dw).symm q) j
  have hd := dpoly_comp F φ h0 (fun q j => uvec ((ltIdx Dw).symm q) j) hlin hφ.hom (fun l => ltIdx Dw l)
    (MvPolynomial.monomial α 1) g
  simp only [Equiv.symm_apply_apply] at hd
  rw [← const_subst0 (a := famL φ) (fun p => h0 p.2) (DpolyOf F uvec (MvPolynomial.monomial α 1) g), ← hd]
  exact const_dpoly_lemma_3 α (subst (famL φ) g)
end Formalism.MainNotions.ModuliIntegralCharts.H1
