-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.star_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:35.290874+00:00
-- url     : https://prove2.me/submissions/21c796a7-5993-4baa-863e-27ad6f04bb80

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_deg_ZV
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_norm_prod_fact
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_norm_le_of_dvd
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators
namespace Formalism.InvariantFactorPaths.G7.StarEntryOperators
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] (hS : StarArith)
    {p ν r0 r1 E : ℕ} [NeZero ν] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (TT : Finset (ZMod (2 * ν))) (e : TpV ν r1 → ℕ) (ls : ZMod (2 * ν) → ℕ)
    (he : ∀ x : TpV ν r1, x.1 ∉ TT → e x = 0) (β : KapI ν r1 E →₀ ℕ)
    (hβ : ∀ k, β k ≠ 0 → k.1 ∈ TT) (n : ZV ν r0 r1 →₀ ℕ) (i0 i2 : ℕ)
    (h1 : ∀ s, ∑ x : Fin r0 × Fin r1, n (s, x) ≤ ls s) (h2 : n.degree + ∑ k, β k = ∑ s, ls s)
    (h3 : ∀ k : KapI ν r1 E, p ^ (2 * k.2.1.val + 1) * β k ≤ e (k.1, k.2.2))
    (h4 : p * i2 ≤ n.degree) :
    (p : ℝ) ^ (i0 + ∑ k, β k + i2) * ‖((mfact (Finsupp.equivFunOnFinite.symm e) : ℕ) : K)‖ *
        ‖(((∑ k, β k).factorial : ℕ) : K)‖ * ‖((mfact n : ℕ) : K)‖ ≤
      (p : ℝ) ^ (-(gamP p * ∑ s ∈ TT, (alN e s : ℝ) - (i0 : ℝ) - (∑ k, (β k : ℝ)) -
        deLoss p r0 r1 TT (alN e) ls + rhoP p * ∑ s, ((alN e s : ℝ) + ls s))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le

  set i : ZMod (2 * ν) → ℕ → ℕ := fun s e' =>
    if h : e' < E then ∑ b, β (s, ⟨e', h⟩, b) else 0 with hi
  have hirange : ∀ s, ∑ e' ∈ range E, i s e' = ∑ ε : Fin E, ∑ b, β (s, ε, b) := by
    intro s
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun ε _ => ?_
    simp only [hi, ε.2, dif_pos]
  have hβsum : ∑ k, β k = ∑ s, ∑ e' ∈ range E, i s e' := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hirange, Fintype.sum_prod_type]
  have hioff : ∀ s, s ∉ TT → ∀ e', i s e' = 0 := by
    intro s hs e'
    simp only [hi]
    split_ifs with h
    · refine Finset.sum_eq_zero fun b _ => ?_
      by_contra hne
      exact hs (hβ _ hne)
    · rfl
  have key := hS (ZMod (2 * ν)) p r0 r1 TT (alN e) ls (fun s b => e (s, b)) (fun s x => n (s, x)) i
    (range E) i0 i2 hp
    (by
      intro s hs
      exact Finset.sum_eq_zero fun b _ => he (s, b) hs)
    (fun s => rfl) h1
    (by
      intro s e' he'
      simp only [hi]
      rw [dif_neg (by simpa using he')])
    hioff
    (by
      intro s e'
      simp only [hi]
      split_ifs with h
      · rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun b _ => h3 (s, ⟨e', h⟩, b)
      · simp)
    (by rw [← hβsum, ← deg_ZV, h2])
    (by rw [← h2]; exact h4.trans (Nat.le_add_right _ _))

  have N1 : ‖((mfact (Finsupp.equivFunOnFinite.symm e) : ℕ) : K)‖ =
      (p : ℝ) ^ (-(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ))) := by
    have : mfact (Finsupp.equivFunOnFinite.symm e) = ∏ x ∈ univ, (e x).factorial := by
      unfold mfact
      rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
      rfl
    rw [this, norm_prod_fact hp hnp, Fintype.sum_prod_type]
  have N3 : ‖((mfact n : ℕ) : K)‖ =
      (p : ℝ) ^ (-(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ))) := by
    have : mfact n = ∏ x ∈ univ, (n x).factorial := by
      unfold mfact
      rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    rw [this, norm_prod_fact hp hnp, Fintype.sum_prod_type]
  have N2 : ‖(((∑ k, β k).factorial : ℕ) : K)‖ ≤
      (p : ℝ) ^ (-(∑ s, ∑ e' ∈ range E, (padicValNat p (i s e').factorial : ℝ))) := by
    have hdvd : (∏ x ∈ (univ : Finset (ZMod (2 * ν))) ×ˢ range E, (i x.1 x.2).factorial) ∣
        (∑ k, β k).factorial := by
      rw [hβsum, ← Finset.sum_product']
      exact Nat.prod_factorial_dvd_factorial_sum _ _
    refine (norm_le_of_dvd hdvd).trans (le_of_eq ?_)
    rw [norm_prod_fact hp hnp, Finset.sum_product]
  have hTTsum : ∑ s ∈ TT, ∑ e' ∈ range E, (i s e' : ℝ) = ∑ s, ∑ e' ∈ range E, (i s e' : ℝ) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => ?_
    exact Finset.sum_eq_zero fun e' _ => by rw [hioff s hs e', Nat.cast_zero]
  have hβR : (∑ k, (β k : ℝ)) = ∑ s, ∑ e' ∈ range E, (i s e' : ℝ) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hβsum
    simpa [Nat.cast_sum] using this
  rw [N1, N3]
  calc (p : ℝ) ^ (i0 + ∑ k, β k + i2) *
          (p : ℝ) ^ (-(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ))) *
          ‖(((∑ k, β k).factorial : ℕ) : K)‖ *
          (p : ℝ) ^ (-(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ)))
      ≤ (p : ℝ) ^ (((i0 + ∑ k, β k + i2 : ℕ) : ℝ)) *
          (p : ℝ) ^ (-(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ))) *
          (p : ℝ) ^ (-(∑ s, ∑ e' ∈ range E, (padicValNat p (i s e').factorial : ℝ))) *
          (p : ℝ) ^ (-(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ))) := by
        rw [Real.rpow_natCast]
        gcongr
    _ = (p : ℝ) ^ (((i0 + ∑ k, β k + i2 : ℕ) : ℝ) +
          -(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ)) +
          -(∑ s, ∑ e' ∈ range E, (padicValNat p (i s e').factorial : ℝ)) +
          -(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ))) := by
        rw [Real.rpow_add hp0, Real.rpow_add hp0, Real.rpow_add hp0]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
        rw [hTTsum] at key
        push_cast
        rw [hβR]
        linarith
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
