-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:26.337566+00:00
-- url     : https://prove2.me/submissions/4c4c2ad7-e383-491e-8e9b-223d1d108f74

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_repar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
private theorem powerSeries_rescale_smul (a c : C) (f : PowerSeries C) :
    PowerSeries.rescale a (c • f) = c • PowerSeries.rescale a f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring
private theorem alongCv_rescale_eq_rescale_alongCv {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (a : C) (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.rescale a (γ i)) f = PowerSeries.rescale a (alongCv γ f) := by
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f
private theorem tyS_neg_eq_rescale_neg_one_of_odd {l : ℕ} (hl : Odd l) (a : ℕ → C) :
    tyS l (fun s => -a s) = PowerSeries.rescale (-1) (tyS l a) := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rw [← h, (hl.pow).neg_one_pow]
    ring
  · ring
private theorem isCv_rescale_neg_one (V : VF C) {σ : Type} {γ : σ → PowerSeries C} (h : IsCv V γ) :
    IsCv V (fun i => PowerSeries.rescale (-1 : C) (γ i)) := by
  intro i
  show PowerSeries.constantCoeff (PowerSeries.rescale (-1 : C) (γ i)) = 0 ∧
    ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale (-1 : C) (γ i)))
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (h i).1
  · have h2 := (h i).2 n
    rw [PowerSeries.coeff_rescale]
    rcases neg_one_pow_eq_or C n with e | e
    · rw [e, one_mul]
      exact h2
    · rw [e, neg_one_mul]
      unfold VF.Ge at h2 ⊢
      rw [V.v.map_neg]
      exact h2
end RawChart
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (V : VF C) (g : Fin 2) (hodd : V.l ≠ 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    -x ∈ X.TySet V g := by
  have hl : Odd V.l := V.l_prime.odd_of_ne_two hodd
  unfold RawChart.TySet at hx ⊢
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  rw [Set.mem_setOf_eq]
  refine ⟨fun i => PowerSeries.rescale (-1 : C) (γ i), fun q => PowerSeries.rescale (-1 : C) (lam q),
    isCv_rescale_neg_one V hγ, isCv_rescale_neg_one V hlam, ?_, ?_⟩
  · intro i
    simp only [Pi.neg_apply]
    rw [alongCv_rescale_eq_rescale_alongCv hγ0, hlg i, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, powerSeries_rescale_smul]
  · intro q
    simp only [Pi.neg_apply]
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, hq q, alongCv_rescale_eq_rescale_alongCv hγ0]
    simp only [tyS_neg_eq_rescale_neg_one_of_odd hl, map_add, map_sub, map_sum, apply_ite ⇑(PowerSeries.rescale (-1 : C)), map_zero,
      powerSeries_rescale_smul]
end Formalism.L2.FormalSeriesBounds.RawChart
