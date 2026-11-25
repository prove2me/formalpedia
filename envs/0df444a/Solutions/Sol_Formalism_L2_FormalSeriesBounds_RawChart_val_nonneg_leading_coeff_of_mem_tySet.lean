-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.val_nonneg_leading_coeff_of_mem_tySet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:26.455509+00:00
-- url     : https://prove2.me/submissions/6e8d6b27-d485-421a-b5f2-31ab94c78800

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_alongCv_low
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_lt
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_constantCoeff_sg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (V : VF C) (g : Fin 2)
    (hlin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C))
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (hsat : ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (hmis : ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)))
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (s : ℕ) (h0 : ∀ i < s, x i = 0) (n : I g ⊕ JJ I g) :
    V.Ge 0 (x s n) := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨w, hw, huw⟩ := hsat
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hlin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have hpos : 1 ≤ V.l ^ s := Nat.one_le_pow _ _ (by omega)
  have hlow : ∀ (m : ℕ) (hm1 : 1 ≤ m), (∀ i, ∀ m' < m, PowerSeries.coeff m' (γ i) = 0) → ∀ i,
      PowerSeries.coeff m (γ i) = ∑ c : I g, X.u g c i * PowerSeries.coeff m (tyS V.l fun s => x s (Sum.inl c)) := by
    intro m hm1 hm i
    have e1 := coeff_alongCv_low hm1 hm (hlg0 i)
    rw [h1 i, map_sum] at e1
    simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      PowerSeries.coeff_smul, smul_eq_mul] at e1
    exact e1.symm
  have hord : ∀ m, m < V.l ^ s → ∀ i, PowerSeries.coeff m (γ i) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm i
      by_cases hm0 : m = 0
      · rw [hm0, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact (hγ i).1
      · rw [hlow m (by omega) (fun i m' hm' => ih m' hm' (by omega) i) i]
        apply Finset.sum_eq_zero
        intro c _
        rw [coeff_tyS_lt hl2 _ s (fun i hi => by rw [h0 i hi]; rfl) m hm, mul_zero]
  have hord' : ∀ i, ∀ m < V.l ^ s, PowerSeries.coeff m (γ i) = 0 := fun i m hm => hord m hm i
  have hlead : ∀ i, PowerSeries.coeff (V.l ^ s) (γ i) = ∑ c : I g, X.u g c i * x s (Sum.inl c) := by
    intro i
    rw [hlow _ hpos hord' i]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coeff_tyS_pow hl2]
  have hinl : ∀ c', x s (Sum.inl c') = ∑ i, PowerSeries.coeff (V.l ^ s) (γ i) * w i c' := by
    intro c'
    simp only [hlead, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ c : I g, ∑ i, X.u g c i * x s (Sum.inl c) * w i c' = (if c = c' then 1 else 0) * x s (Sum.inl c) := by
      intro c
      rw [← huw c c', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinlInt : ∀ c', V.Ge 0 (x s (Sum.inl c')) := by
    intro c'
    rw [hinl c']
    exact VF.Ge.sum fun i _ => ((hγ i).2 _).mul_int (hw i c')
  cases n with
  | inl c' => exact hinlInt c'
  | inr q =>
    have e2 := congrArg (PowerSeries.coeff (V.l ^ s)) (h2 q)
    rw [coeff_tyS_pow hl2, map_add, map_sub, coeff_alongCv_low hpos hord' (X.constantCoeff_sg hh _), map_sum] at e2
    have e3 : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (X.sg (X.u (1 - g) q)) * PowerSeries.coeff (V.l ^ s) (γ i) =
        ∑ c : I g, X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) := by
      simp only [hlead, sg1, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    have e4 : ∀ c : I g, PowerSeries.coeff (V.l ^ s) (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) =
        if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) else 0 := by
      intro c
      split_ifs
      · rw [PowerSeries.coeff_smul, coeff_tyS_pow hl2, smul_eq_mul]
      · rw [map_zero]
    simp only [e4] at e2
    rw [e3, sub_add, ← Finset.sum_sub_distrib] at e2
    rw [e2]
    refine ((hlam q).2 _).sub (VF.Ge.sum fun c _ => ?_)
    split_ifs with hc
    · rw [sub_self]
      exact VF.Ge.zero 0
    · rw [sub_zero]
      exact (hmis c q hc).mul_int (hinlInt c)
end Formalism.L2.FormalSeriesBounds.RawChart
